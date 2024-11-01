// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

//! Contains STARK proof struct and associated components.

use crate::{ProofOptions, TraceInfo, TraceLayout};
use core::cmp;
use crypto::Hasher;
use fri::FriProof;
use utils::{
    collections::Vec, ByteReader, Deserializable, DeserializationError, Serializable, SliceReader,
};

mod context;
pub use context::Context;

mod commitments;
pub use commitments::Commitments;

mod queries;
pub use queries::JointTraceQueries;
pub use queries::Queries;

mod ood_frame;
pub use ood_frame::OodFrame;

mod table;
pub use table::Table;

// CONSTANTS
// ================================================================================================

const GRINDING_CONTRIBUTION_FLOOR: u32 = 80;

// STARK PROOF
// ================================================================================================
/// A proof generated by Winterfell prover.
///
/// A STARK proof contains information proving that a computation was executed correctly. A proof
/// also contains basic metadata for the computation, but neither the definition of the computation
/// itself, nor public inputs consumed by the computation are contained in a proof.
///
/// A proof can be serialized into a sequence of bytes using [to_bytes()](StarkProof::to_bytes)
/// function, and deserialized from a sequence of bytes using [from_bytes()](StarkProof::from_bytes)
/// function.
///
/// To estimate soundness of a proof (in bits), [security_level()](StarkProof::security_level)
/// function can be used.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StarkProof {
    /// Basic metadata about the execution of the computation described by this proof.
    pub contexts: Vec<Context>,
    /// Commitments made by the prover during the commit phase of the protocol.
    pub commitments: Commitments,
    /// Decommitments of extended execution trace values (for all trace segments) at position
    ///  queried by the verifier.
    pub trace_queries: Vec<JointTraceQueries>,
    /// Decommitments of constraint composition polynomial evaluations at positions queried by
    /// the verifier.
    pub constraint_queries: Queries,
    /// Trace and constraint polynomial evaluations at an out-of-domain point.
    pub ood_frames: Vec<OodFrame>,
    /// Low-degree proof for a DEEP composition polynomial.
    pub fri_proof: FriProof,
    /// Proof-of-work nonce for query seed grinding.
    pub pow_nonce: u64,
}

impl StarkProof {
    /// Returns STARK protocol parameters used to generate this proof.
    pub fn options(&self, i: usize) -> &ProofOptions {
        self.contexts[i].options()
    }

    /// Returns a layout describing how columns of the execution trace described by this context
    /// are arranged into segments.
    pub fn trace_layout(&self, i: usize) -> &TraceLayout {
        self.contexts[i].trace_layout()
    }

    /// Returns trace length for the computation described by this proof.
    pub fn trace_length(&self, i: usize) -> usize {
        self.contexts[i].trace_length()
    }

    /// Returns trace info for the computation described by this proof.
    pub fn get_trace_info(&self, i: usize) -> TraceInfo {
        self.contexts[i].get_trace_info()
    }

    /// Returns the size of the LDE domain for the computation described by this proof.
    pub fn lde_domain_size(&self, i: usize) -> usize {
        self.contexts[i].lde_domain_size()
    }

    // SECURITY LEVEL
    // --------------------------------------------------------------------------------------------
    /// Returns security level of this proof (in bits).
    ///
    /// When `conjectured` is true, conjectured security level is returned; otherwise, provable
    /// security level is returned. Usually, the number of queries needed for provable security is
    /// 2x - 3x higher than the number of queries needed for conjectured security at the same
    /// security level.
    pub fn security_level<H: Hasher>(&self, conjectured: bool) -> u32 {
        if conjectured {
            get_conjectured_security(
                self.contexts[0].options(),
                self.contexts[0].num_modulus_bits(),
                self.trace_length(0) as u64,
                H::COLLISION_RESISTANCE,
            )
        } else {
            #[cfg(not(feature = "std"))]
            panic!("proven security level is not available in no_std mode");

            #[cfg(feature = "std")]
            get_proven_security(
                self.contexts[0].options(),
                self.contexts[0].num_modulus_bits(),
                self.lde_domain_size(0) as u64,
                self.trace_length(0) as u64,
                H::COLLISION_RESISTANCE,
            )
        }
    }

    // SERIALIZATION / DESERIALIZATION
    // --------------------------------------------------------------------------------------------

    /// Serializes this proof into a vector of bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result = Vec::new();
        for context in self.contexts.iter() {
            context.write_into(&mut result);
        }
        self.commitments.write_into(&mut result);
        self.trace_queries.write_into(&mut result);
        self.constraint_queries.write_into(&mut result);
        for ood_frame in self.ood_frames.iter() {
            ood_frame.write_into(&mut result);
        }
        self.fri_proof.write_into(&mut result);
        result.extend_from_slice(&self.pow_nonce.to_le_bytes());
        result
    }

    /// Returns a STARK proof read from the specified `source`.
    ///
    /// # Errors
    /// Returns an error of a valid STARK proof could not be read from the specified `source`.
    pub fn from_bytes(&self, source: &[u8]) -> Result<Self, DeserializationError> {
        let mut source = SliceReader::new(source);

        // parse the context
        //let contexts = self
        //    .contexts
        //    .iter()
        //    .map(|context| Context::read_from(&mut source))
        //    .collect();
        let mut contexts = Vec::new();
        for _ in self.contexts.iter() {
            contexts.push(Context::read_from(&mut source)?);
        }
        // parse the commitments
        let commitments = Commitments::read_from(&mut source)?;

        // parse trace queries
        let num_trace_segments = contexts[0].trace_layout().num_segments();
        //We may need to change something here!!
        let mut trace_queries = Vec::with_capacity(num_trace_segments);
        for _ in 0..num_trace_segments {
            trace_queries.push(JointTraceQueries::read_from(&mut source)?);
        }
        let constraint_queries = Queries::read_from(&mut source)?;
        let mut ood_frames = Vec::new();
        for _ in self.ood_frames.iter() {
            ood_frames.push(OodFrame::read_from(&mut source)?);
        }
        // parse the rest of the proof
        let proof = StarkProof {
            contexts,
            commitments,
            trace_queries,
            constraint_queries, //: Queries::read_from(&mut source)?,
            ood_frames,
            fri_proof: FriProof::read_from(&mut source)?,
            pow_nonce: source.read_u64()?,
        };
        if source.has_more_bytes() {
            return Err(DeserializationError::UnconsumedBytes);
        }
        Ok(proof)
    }
}

// HELPER FUNCTIONS
// ================================================================================================

/// Computes conjectured security level for the specified proof parameters.
fn get_conjectured_security(
    options: &ProofOptions,
    base_field_bits: u32,
    trace_domain_size: u64,
    collision_resistance: u32,
) -> u32 {
    // compute max security we can get for a given field size
    let field_size = base_field_bits * options.field_extension().degree();
    let field_security = field_size - trace_domain_size.trailing_zeros();

    // compute security we get by executing multiple query rounds
    let security_per_query = options.blowup_factor().ilog2();
    let mut query_security = security_per_query * options.num_queries() as u32;

    // include grinding factor contributions only for proofs adequate security
    if query_security >= GRINDING_CONTRIBUTION_FLOOR {
        query_security += options.grinding_factor();
    }

    cmp::min(
        cmp::min(field_security, query_security) - 1,
        collision_resistance,
    )
}

#[cfg(feature = "std")]
/// Estimates proven security level for the specified proof parameters.
fn get_proven_security(
    options: &ProofOptions,
    base_field_bits: u32,
    lde_domain_size: u64,
    trace_domain_size: u64,
    collision_resistance: u32,
) -> u32 {
    let extension_field_bits = (base_field_bits * options.field_extension().degree()) as f64;

    let blowup_bits = options.blowup_factor().ilog2() as f64;
    let num_fri_queries = options.num_queries() as f64;
    let lde_size_bits = lde_domain_size.trailing_zeros() as f64;

    // blowup_plus_bits is the number of bits in the blowup factor which is the inverse of
    // `\rho^+ := (trace_domain_size + 2) / lde_domain_size`. `\rho^+` is used in order to define a larger
    // agreement parameter `\alpha^+ := (1 + 1/2m)\sqrt{rho^+} := 1 - \theta^+`. The reason for
    // running FRI with a larger agreement parameter is to account for the simplified
    // DEEP composition polynomial. See Protocol 3 in https://eprint.iacr.org/2022/1216.
    let blowup_plus_bits = ((lde_domain_size as f64) / (trace_domain_size as f64 + 2_f64)).log2();

    // m is a parameter greater or equal to 3.
    // A larger m gives a worse field security bound but a better query security bound.
    // An optimal value of m is then a value that would balance field and query security
    // but there is no simple closed form solution.
    // This sets m so that field security is equal to the best query security for any value
    // of m, unless the calculated value is less than 3 in which case it gets rounded up to 3.
    let mut m = extension_field_bits + 1.0;
    m -= options.grinding_factor() as f64;
    m -= 1.5 * blowup_bits;
    m -= 0.5 * num_fri_queries * blowup_plus_bits;
    m -= 2.0 * lde_size_bits;
    m /= 7.0;
    m = 2.0_f64.powf(m);
    m -= 0.5;
    m = m.max(3.0);

    // compute pre-FRI query security
    // this considers only the third component given in the corresponding part of eq. 20
    // in https://eprint.iacr.org/2021/582, i.e. (m+1/2)^7.n^2 / (2\rho^1.5.q) as all
    // other terms are negligible in comparison.
    let pre_query_security = (extension_field_bits + 1.0
        - 3.0 / 2.0 * blowup_bits
        - 2.0 * lde_size_bits
        - 7.0 * (m + 0.5).log2()) as u32;

    // compute security we get by executing multiple query rounds
    let security_per_query = 0.5 * blowup_plus_bits - (1.0 + 1.0 / (2.0 * m)).log2();
    let mut query_security = (security_per_query * num_fri_queries) as u32;

    query_security += options.grinding_factor();

    cmp::min(
        cmp::min(pre_query_security, query_security) - 1,
        collision_resistance,
    )
}
