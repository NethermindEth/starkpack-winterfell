// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

//! This crate contains Winterfell STARK prover.
//!
//! This prover can be used to generate proofs of computational integrity using the
//! [STARK](https://eprint.iacr.org/2018/046) (Scalable Transparent ARguments of Knowledge)
//! protocol.
//!
//! When the crate is compiled with `concurrent` feature enabled, proof generation will be
//! performed in multiple threads (usually, as many threads as there are logical cores on the
//! machine). The number of threads can be configured via `RAYON_NUM_THREADS` environment
//! variable.
//!
//! # Usage
//! To generate a proof that a computation was executed correctly, you'll need to do the
//! following:
//!
//! 1. Define an *algebraic intermediate representation* (AIR) for your computation. This can
//!    be done by implementing [Air] trait.
//! 2. Define an execution trace for your computation. This can be done by implementing [Trace]
//!    trait. Alternatively, you can use [TraceTable] struct which already implements [Trace]
//!    trait in cases when this generic implementation works for your use case.
//! 3. Execute your computation and record its execution trace.
//! 4. Define your prover by implementing [Prover] trait. Then execute [Prover::prove()] function
//!    passing the trace generated in the previous step into it as a parameter. The function will
//!    return a instance of [StarkProof].
//!
//! This [StarkProof] can be serialized and sent to a STARK verifier for verification. The size
//! of proof depends on the specifics of a given computation, but for most computations it should
//! be in the range between 15 KB (for very small computations) and 300 KB (for very large
//! computations).
//!
//! Proof generation time is also highly dependent on the specifics of a given computation, but
//! also depends on the capabilities of the machine used to generate the proofs (i.e. on number
//! of CPU cores and memory bandwidth).

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

pub use air::{
    proof::StarkProof, Air, AirContext, Assertion, AuxTraceRandElements, BoundaryConstraint,
    BoundaryConstraintGroup, ConstraintCompositionCoefficients, ConstraintDivisor,
    DeepCompositionCoefficients, EvaluationFrame, FieldExtension, ProofOptions, TraceInfo,
    TraceLayout, TransitionConstraintDegree,
};
pub use utils::{
    iterators, ByteReader, ByteWriter, Deserializable, DeserializationError, Serializable,
    SliceReader,
};

use fri::FriProver;
use utils::{batch_iter_mut, collections::Vec};

pub use math;
use math::{
    add_in_place,
    fft::infer_degree,
    fields::{CubeExtension, QuadExtension},
    log2, ExtensibleField, FieldElement, StarkField, ToElements,
};

pub use crypto;
use crypto::{ElementHasher, MerkleTree, RandomCoin};

#[cfg(feature = "std")]
use log::debug;
#[cfg(feature = "std")]
use std::time::Instant;

mod domain;
pub use domain::StarkDomain;

pub mod matrix;
pub use matrix::{ColMatrix, RowMatrix};

mod constraints;
use constraints::ConstraintEvaluator;
pub use constraints::{CompositionPoly, ConstraintCommitment};

mod composer;
use composer::DeepCompositionPoly;

mod trace;
pub use trace::{Trace, TraceTable, TraceTableFragment};
use trace::{TraceCommitment, TraceLde, TracePolyTable};

mod channel;
use channel::ProverChannel;

mod errors;
pub use errors::ProverError;

#[cfg(test)]
pub mod tests;

// PROVER
// ================================================================================================

// this segment width seems to give the best performance for small fields (i.e., 64 bits)
const DEFAULT_SEGMENT_WIDTH: usize = 8;

/// Defines a STARK prover for a computation.
///
/// A STARK prover can be used to generate STARK proofs. The prover contains definitions of a
/// computation's AIR (specified via [Air](Prover::Air) associated type), execution trace
/// (specified via [Trace](Prover::Trace) associated type) and hash function to be used (specified
/// via [HashFn](Prover::HashFn) associated type), and exposes [prove()](Prover::prove) method which can
/// be used to build STARK proofs for provided execution traces.
///
/// Thus, once a prover is defined and instantiated, generating a STARK proof consists of two
/// steps:
/// 1. Build an execution trace for a specific instance of the computation.
/// 2. Invoke [Prover::prove()] method generate a proof using the trace from the previous step
///    as a witness.
///
/// The generated proof is built using protocol parameters defined by the [ProofOptions] struct
/// return from [Prover::options] method.
pub trait Prover {
    /// Base field for the computation described by this prover.
    type BaseField: StarkField + ExtensibleField<2> + ExtensibleField<3>;

    /// Algebraic intermediate representation (AIR) for the computation described by this prover.
    type Air: Air<BaseField = Self::BaseField>;

    /// Execution trace of the computation described by this prover.
    type Trace: Trace<BaseField = Self::BaseField>;

    /// Hash function to be used.
    type HashFn: ElementHasher<BaseField = Self::BaseField>;

    /// PRNG to be used for generating random field elements.
    type RandomCoin: RandomCoin<BaseField = Self::BaseField, Hasher = Self::HashFn>;

    // REQUIRED METHODS
    // --------------------------------------------------------------------------------------------

    /// Returns a set of public inputs for an instance of the computation defined by the provided
    /// trace.
    ///
    /// Public inputs need to be shared with the verifier in order for them to verify a proof.
    fn get_pub_inputs(&self, trace: &Self::Trace) -> <<Self as Prover>::Air as Air>::PublicInputs;

    /// Returns [ProofOptions] which this prover uses to generate STARK proofs.
    ///
    /// Proof options defines basic protocol parameters such as: number of queries, blowup factor,
    /// grinding factor etc. These properties directly inform such metrics as proof generation time,
    /// proof size, and proof security level.
    fn options(&self) -> &ProofOptions;

    // PROVIDED METHODS
    // --------------------------------------------------------------------------------------------

    /// Returns a STARK proof attesting to a correct execution of a computation defined by the
    /// provided trace.
    ///
    /// The returned [StarkProof] attests that the specified `trace` is a valid execution trace of
    /// the computation described by [Self::Air](Prover::Air) and generated using some set of
    /// secret and public inputs. Public inputs must match the value returned from
    /// [Self::get_pub_inputs()](Prover::get_pub_inputs) for the provided trace.
    #[rustfmt::skip]
    fn prove(&self, trace: Self::Trace, trace1: Self::Trace) -> Result<StarkProof, ProverError> {
        // figure out which version of the generic proof generation procedure to run. this is a sort
        // of static dispatch for selecting two generic parameter: extension field and hash function.
        match self.options().field_extension() {
            FieldExtension::None => self.generate_proof::<Self::BaseField>(trace, trace1),
            FieldExtension::Quadratic => {
                if !<QuadExtension<Self::BaseField>>::is_supported() {
                    return Err(ProverError::UnsupportedFieldExtension(2));
                }
                self.generate_proof::<QuadExtension<Self::BaseField>>(trace, trace1)
            }
            FieldExtension::Cubic => {
                if !<CubeExtension<Self::BaseField>>::is_supported() {
                    return Err(ProverError::UnsupportedFieldExtension(3));
                }
                self.generate_proof::<CubeExtension<Self::BaseField>>(trace, trace1)
            }
        }
    }

    // HELPER METHODS
    // --------------------------------------------------------------------------------------------

    /// Performs the actual proof generation procedure, generating the proof that the provided
    /// execution `trace` is valid against this prover's AIR.
    /// TODO: make this function un-callable externally?
    #[doc(hidden)]
    fn generate_proof<E>(
        &self,
        mut trace: Self::Trace,
        mut trace1: Self::Trace,
    ) -> Result<StarkProof, ProverError>
    where
        E: FieldElement<BaseField = Self::BaseField>,
    {
        // 0 ----- instantiate AIR and prover channel ---------------------------------------------

        // serialize public inputs; these will be included in the seed for the public coin
        let pub_inputs = self.get_pub_inputs(&trace);
        let pub_inputs_elements = pub_inputs.to_elements();

        let pub_inputs1 = self.get_pub_inputs(&trace1);
        let pub_inputs_elements1 = pub_inputs1.to_elements();

        // create an instance of AIR for the provided parameters. this takes a generic description
        // of the computation (provided via AIR type), and creates a description of a specific
        // execution of the computation for the provided public inputs.
        let air = Self::Air::new(trace.get_info(), pub_inputs, self.options().clone());

        let air1 = Self::Air::new(trace1.get_info(), pub_inputs1, self.options().clone());

        // create a channel which is used to simulate interaction between the prover and the
        // verifier; the channel will be used to commit to values and to draw randomness that
        // should come from the verifier.
        let mut channel = ProverChannel::<Self::Air, E, Self::HashFn, Self::RandomCoin>::new(
            &air,
            &air1,
            pub_inputs_elements,
            pub_inputs_elements1,
        );
        //Shoulf be changed for multiple pub_inputs
        //probably already done

        // 1 ----- Commit to the execution trace --------------------------------------------------

        // build computation domain; this is used later for polynomial evaluations
        #[cfg(feature = "std")]
        let now = Instant::now();
        // Keep in mind that here the traces are identitical so only having one domain is fine for
        // now
        let domain = StarkDomain::new(&air);
        #[cfg(feature = "std")]
        debug!(
            "Built domain of 2^{} elements in {} ms",
            domain.lde_domain_size().ilog2(),
            now.elapsed().as_millis()
        );

        // extend the main execution trace and build a Merkle tree from the extended trace
        let (main_trace_lde, main_trace1_lde, main_trace_tree, main_trace_polys, main_trace1_polys) =
            self.build_trace_commitment::<Self::BaseField>(
                trace.main_segment(),
                trace1.main_segment(),
                &domain,
            );

        // commit to the LDE of the main trace by writing the root of its Merkle tree into
        // the channel
        // ****
        // Here we may need to commit to all the traces
        // probably there will be some problems on how the channel sends this to the verifier

        //I create the clone of the main trace tree
        // manually as the #derive(Clone) didn't work
        let main_trace1_tree = main_trace_tree.clone();
        //println!("Trace root on Prover Channel:\n{:?}", main_trace_tree.root());
        channel.commit_trace(*main_trace_tree.root());

        // initialize trace commitment and trace polynomial table structs with the main trace
        // data; for multi-segment traces these structs will be used as accumulators of all
        // trace segments

        //let main_trace1_tree = &main_trace_tree;
        let mut trace_commitment = TraceCommitment::new(
            main_trace_lde,
            main_trace_tree,
            domain.trace_to_lde_blowup(),
        );
        let mut trace1_commitment = TraceCommitment::new(
            main_trace1_lde,
            main_trace1_tree,
            domain.trace_to_lde_blowup(),
        );
        let mut trace_polys = TracePolyTable::new(main_trace_polys);
        let mut trace1_polys = TracePolyTable::new(main_trace1_polys);

        // build auxiliary trace segments (if any), and append the resulting segments to trace
        // commitment and trace polynomial table structs
        let mut aux_trace_segments = Vec::new();
        let mut aux_trace_rand_elements = AuxTraceRandElements::new();
        let mut aux_trace1_segments = Vec::new();
        let mut aux_trace1_rand_elements = AuxTraceRandElements::new();
        for i in 0..trace.layout().num_aux_segments() {
            #[cfg(feature = "std")]
            let now = Instant::now();

            // draw a set of random elements required to build an auxiliary trace segment
            let rand_elements = channel.get_aux_trace_segment_rand_elements(i);
            println!("The random elements of the Prover,{:?}", rand_elements);

            let rand_elements1 = channel.get_aux_trace_segment_rand_elements(i);
            // build the trace segment
            let aux_segment = trace
                .build_aux_segment(&aux_trace_segments, &rand_elements)
                .expect("failed build auxiliary trace segment");
            #[cfg(feature = "std")]
            debug!(
                "Built auxiliary trace segment of {} columns and 2^{} steps in {} ms",
                aux_segment.num_cols(),
                aux_segment.num_rows().ilog2(),
                now.elapsed().as_millis()
            );
            let aux_segment1 = trace1
                .build_aux_segment(&aux_trace1_segments, &rand_elements1)
                .expect("failed build auxiliary trace segment");
            #[cfg(feature = "std")]
            debug!(
                "Built auxiliary trace segment of {} columns and 2^{} steps in {} ms",
                aux_segment1.num_cols(),
                log2(aux_segment1.num_rows()),
                now.elapsed().as_millis()
            );

            // extend the auxiliary trace segment and build a Merkle tree from the extended trace
            let (
                aux_segment_lde,
                aux_segment1_lde,
                aux_segment_tree,
                aux_segment_polys,
                aux_segment1_polys,
            ) = self.build_trace_commitment::<E>(&aux_segment, &aux_segment1, &domain);

            // commit to the LDE of the extended auxiliary trace segment  by writing the root of
            // its Merkle tree into the channel
            // ****
            // Here we may need to commit to all the traces
            // probably there will be some problems on how the channel sends this to the verifier

            //The aux_tree is also one for all of the trace
            // so we should clone it too.
            let aux_segment1_tree = aux_segment_tree.clone();
            channel.commit_trace(*aux_segment_tree.root());
            println!(
                "The aux Trace root of the Prover,{:?}",
                aux_segment_tree.root()
            );

            // append the segment to the trace commitment and trace polynomial table structs
            trace_commitment.add_segment(aux_segment_lde, aux_segment_tree);
            trace1_commitment.add_segment(aux_segment1_lde, aux_segment1_tree);

            trace_polys.add_aux_segment(aux_segment_polys);
            aux_trace_rand_elements.add_segment_elements(rand_elements);
            aux_trace_segments.push(aux_segment);

            trace1_polys.add_aux_segment(aux_segment1_polys);
            aux_trace1_rand_elements.add_segment_elements(rand_elements1);
            aux_trace1_segments.push(aux_segment1);
        }

        // make sure the specified trace (including auxiliary segments) is valid against the AIR.
        // This checks validity of both, assertions and state transitions. We do this in debug
        // mode only because this is a very expensive operation.
        #[cfg(debug_assertions)]
        trace.validate(&air, &aux_trace_segments, &aux_trace_rand_elements);

        trace1.validate(&air1, &aux_trace1_segments, &aux_trace1_rand_elements);

        // 2 ----- evaluate constraints -----------------------------------------------------------
        // evaluate constraints specified by the AIR over the constraint evaluation domain, and
        // compute random linear combinations of these evaluations using coefficients drawn from
        // the channel; this step evaluates only constraint numerators, thus, only constraints with
        // identical denominators are merged together. the results are saved into a constraint
        // evaluation table where each column contains merged evaluations of constraints with
        // identical denominators.
        #[cfg(feature = "std")]
        let now = Instant::now();
        let constraint_coeffs = channel.get_constraint_composition_coeffs();
        let evaluator = ConstraintEvaluator::new(&air, aux_trace_rand_elements, constraint_coeffs);
        let constraint_evaluations = evaluator.evaluate(trace_commitment.trace_table(), &domain);

        let constraint_coeffs1 = channel.get_constraint_composition_coeffs();
        let evaluator1 =
            ConstraintEvaluator::new(&air1, aux_trace1_rand_elements, constraint_coeffs1);
        let constraint_evaluations1 = evaluator1.evaluate(trace1_commitment.trace_table(), &domain);

        // We need to combine all comp polys into one final polynomial.
        let final_evaluations = constraint_evaluations.clone();

        #[cfg(feature = "std")]
        debug!(
            "Evaluated constraints over domain of 2^{} elements in {} ms",
            constraint_evaluations.num_rows().ilog2(),
            now.elapsed().as_millis()
        );

        // 3 ----- commit to constraint evaluations -----------------------------------------------

        // first, build constraint composition polynomial from the constraint evaluation table:
        // - divide all constraint evaluation columns by their respective divisors
        // - combine them into a single column of evaluations,
        // - interpolate the column into a polynomial in coefficient form
        // - "break" the polynomial into a set of column polynomials each of degree equal to
        //   trace_length - 1
        #[cfg(feature = "std")]
        let now = Instant::now();
        let (composition_poly, trace_length, num_cols) = constraint_evaluations
            .into_comb_poly(air.context().num_constraint_composition_columns());
        let (composition_poly1, trace1_length, num_cols1) = constraint_evaluations1
            .into_comb_poly(air1.context().num_constraint_composition_columns());
        //let final_coef = col_composition_poly + col_composition_poly1;
        let mut final_comb_poly = composition_poly;
        //for (i, (val, val1)) in composition_poly.iter().zip(composition_poly1).enumerate() {
        //    final_comb_poly[i] = *val + val1;
        //}
        add_in_place(&mut final_comb_poly, &composition_poly1);
        assert_eq!(trace_length, trace1_length, "Traces of different lenght");
        assert_eq!(num_cols, num_cols1, "Traces of different number of columns");
        let final_poly = final_evaluations.into_poly(final_comb_poly, trace_length, num_cols)?;

        #[cfg(feature = "std")]
        debug!(
            "Converted constraint evaluations into {} composition polynomial columns of degree {} in {} ms",
            final_poly.num_columns(),
            final_poly.column_degree(),
            now.elapsed().as_millis()
        );

        // then, build a commitment to the evaluations of the composition polynomial columns
        //let constraint_commitment =
        //    self.build_constraint_commitment::<E>(&composition_poly, &domain);
        //let constraint_commitment1 =
        //    self.build_constraint_commitment::<E>(&composition_poly1, &domain);
        let constraint_commitment = self.build_constraint_commitment::<E>(&final_poly, &domain);
        // then, commit to the evaluations of constraints by writing the root of the constraint
        // Merkle tree into the channel
        //println!(
        //    "Constraint root on Prover Channel:\n{:?}",
        //    constraint_commitment.root()
        //);
        channel.commit_constraints(constraint_commitment.root());

        // 4 ----- build DEEP composition polynomial ----------------------------------------------
        #[cfg(feature = "std")]
        let now = Instant::now();

        // draw an out-of-domain point z. Depending on the type of E, the point is drawn either
        // from the base field or from an extension field defined by E.
        //
        // The purpose of sampling from the extension field here (instead of the base field) is to
        // increase security. Soundness is limited by the size of the field that the random point
        // is drawn from, and we can potentially save on performance by only drawing this point
        // from an extension field, rather than increasing the size of the field overall.
        let z = channel.get_ood_point();

        // evaluate trace and constraint polynomials at the OOD point z, and send the results to
        // the verifier. the trace polynomials are actually evaluated over two points: z and z * g,
        // where g is the generator of the trace domain.
        let ood_trace_states = trace_polys.get_ood_frame(z);

        let ood_trace1_states = trace1_polys.get_ood_frame(z);
        channel.send_ood_trace_states(&ood_trace_states, &ood_trace1_states);
        println!("ood_frame from the prover{:?}", ood_trace_states);
        println!("ood_frame1 from the prover{:?}", ood_trace1_states);

        //let ood_evaluations = composition_poly.evaluate_at(z);
        let ood_evaluations = final_poly.evaluate_at(z);
        channel.send_ood_constraint_evaluations(&ood_evaluations);
        println!("ood_eval from the prover{:?}", ood_evaluations);

        // draw random coefficients to use during DEEP polynomial composition, and use them to
        // initialize the DEEP composition polynomial
        let deep_coefficients = channel.get_deep_composition_coeffs();
        let mut deep_composition_poly = DeepCompositionPoly::new(z, deep_coefficients);

        // combine all trace polynomials together and merge them into the DEEP composition
        // polynomial
        deep_composition_poly.add_trace_polys(trace_polys, ood_trace_states);
        deep_composition_poly.add_trace_polys(trace1_polys, ood_trace1_states);
        // merge columns of constraint composition polynomial into the DEEP composition polynomial;
        deep_composition_poly.add_composition_poly(final_poly, ood_evaluations);

        // raise the degree of the DEEP composition polynomial by one to make sure it is equal to
        // trace_length - 1

        //
        // The Original winterfell removed deree adjustment
        //deep_composition_poly.adjust_degree();

        #[cfg(feature = "std")]
        debug!(
            "Built DEEP composition polynomial of degree {} in {} ms",
            deep_composition_poly.degree(),
            now.elapsed().as_millis()
        );

        // make sure the degree of the DEEP composition polynomial is equal to trace polynomial
        // degree
        assert_eq!(domain.trace_length() - 2, deep_composition_poly.degree());

        //let final_poly = deep_composition_poly0 + deep_composition_poly1;

        // 5 ----- evaluate DEEP composition polynomial over LDE domain ---------------------------
        #[cfg(feature = "std")]
        let now = Instant::now();
        //let deep_evaluations = deep_composition_poly.evaluate(&domain);
        let deep_evaluations = deep_composition_poly.evaluate(&domain);
        // we check the following condition in debug mode only because infer_degree is an expensive
        // operation
        debug_assert_eq!(
            domain.trace_length() - 2,
            infer_degree(&deep_evaluations, domain.offset())
        );
        #[cfg(feature = "std")]
        debug!(
            "Evaluated DEEP composition polynomial over LDE domain (2^{} elements) in {} ms",
            domain.lde_domain_size().ilog2(),
            now.elapsed().as_millis()
        );

        // 6 ----- compute FRI layers for the composition polynomial ------------------------------
        #[cfg(feature = "std")]
        let now = Instant::now();
        let mut fri_prover = FriProver::new(air.options().to_fri_options());
        fri_prover.build_layers(&mut channel, deep_evaluations);
        #[cfg(feature = "std")]
        debug!(
            "Computed {} FRI layers from composition polynomial evaluations in {} ms",
            fri_prover.num_layers(),
            now.elapsed().as_millis()
        );

        // 7 ----- determine query positions ------------------------------------------------------
        #[cfg(feature = "std")]
        let now = Instant::now();

        // apply proof-of-work to the query seed
        channel.grind_query_seed();

        // generate pseudo-random query positions
        let query_positions = channel.get_query_positions();
        #[cfg(feature = "std")]
        debug!(
            "Determined {} query positions in {} ms",
            query_positions.len(),
            now.elapsed().as_millis()
        );

        // 8 ----- build proof object -------------------------------------------------------------
        #[cfg(feature = "std")]
        let now = Instant::now();

        // generate FRI proof
        let fri_proof = fri_prover.build_proof(&query_positions);

        // query the execution trace at the selected position; for each query, we need the
        // state of the trace at that position + Merkle authentication path
        let trace_queries = trace_commitment.query(&query_positions);
        //println!("trace_querries from the Prover{:?}", trace_queries);
        let trace1_queries = trace1_commitment.query(&query_positions);

        // query the constraint commitment at the selected positions; for each query, we need just
        // a Merkle authentication path. this is because constraint evaluations for each step are
        // merged into a single value and Merkle authentication paths contain these values already
        let constraint_queries = constraint_commitment.query(&query_positions);

        // build the proof object
        let proof =
            channel.build_proof(trace_queries, trace1_queries, constraint_queries, fri_proof);
        #[cfg(feature = "std")]
        debug!("Built proof object in {} ms", now.elapsed().as_millis());

        Ok(proof)
    }

    /// Computes a low-degree extension (LDE) of the provided execution trace over the specified
    /// domain and build a commitment to the extended trace.
    ///
    /// The extension is performed by interpolating each column of the execution trace into a
    /// polynomial of degree = trace_length - 1, and then evaluating the polynomial over the LDE
    /// domain.
    ///
    /// Trace commitment is computed by hashing each row of the extended execution trace, and then
    /// building a Merkle tree from the resulting hashes.
    fn build_trace_commitment<E>(
        &self,
        trace: &ColMatrix<E>,
        trace1: &ColMatrix<E>,
        domain: &StarkDomain<Self::BaseField>,
    ) -> (
        RowMatrix<E>,
        RowMatrix<E>,
        MerkleTree<Self::HashFn>,
        ColMatrix<E>,
        ColMatrix<E>,
    )
    where
        E: FieldElement<BaseField = Self::BaseField>,
    {
        // extend the execution trace
        #[cfg(feature = "std")]
        let now = Instant::now();
        let trace_polys = trace.interpolate_columns();
        let trace1_polys = trace1.interpolate_columns();
        let trace_lde =
            RowMatrix::evaluate_polys_over::<DEFAULT_SEGMENT_WIDTH>(&trace_polys, domain);
        let trace1_lde =
            RowMatrix::evaluate_polys_over::<DEFAULT_SEGMENT_WIDTH>(&trace1_polys, domain);
        #[cfg(feature = "std")]
        debug!(
            "Extended execution trace of {} columns from 2^{} to 2^{} steps ({}x blowup) in {} ms",
            trace_lde.num_cols(),
            trace_polys.num_rows().ilog2(),
            trace_lde.num_rows().ilog2(),
            domain.trace_to_lde_blowup(),
            now.elapsed().as_millis()
        );

        // build trace commitment
        let trace1_lde_clone = trace1_lde.clone();
        #[cfg(feature = "std")]
        let now = Instant::now();
        let trace_tree = trace_lde.commit_to_comb_rows(trace1_lde_clone);

        #[cfg(feature = "std")]
        debug!(
            "Computed execution trace commitment (Merkle tree of depth {}) in {} ms",
            trace_tree.depth(),
            now.elapsed().as_millis()
        );

        (trace_lde, trace1_lde, trace_tree, trace_polys, trace1_polys)
    }

    /// Evaluates constraint composition polynomial over the LDE domain and builds a commitment
    /// to these evaluations.
    ///
    /// The evaluation is done by evaluating each composition polynomial column over the LDE
    /// domain.
    ///
    /// The commitment is computed by hashing each row in the evaluation matrix, and then building
    /// a Merkle tree from the resulting hashes.
    fn build_constraint_commitment<E>(
        &self,
        composition_poly: &CompositionPoly<E>,
        domain: &StarkDomain<Self::BaseField>,
    ) -> ConstraintCommitment<E, Self::HashFn>
    where
        E: FieldElement<BaseField = Self::BaseField>,
    {
        // evaluate composition polynomial columns over the LDE domain
        #[cfg(feature = "std")]
        let now = Instant::now();
        let composed_evaluations = RowMatrix::evaluate_polys_over::<DEFAULT_SEGMENT_WIDTH>(
            composition_poly.data(),
            domain,
        );
        #[cfg(feature = "std")]
        debug!(
            "Evaluated {} composition polynomial columns over LDE domain (2^{} elements) in {} ms",
            composed_evaluations.num_cols(),
            composed_evaluations.num_rows().ilog2(),
            now.elapsed().as_millis()
        );

        // build constraint evaluation commitment
        #[cfg(feature = "std")]
        let now = Instant::now();
        let commitment = composed_evaluations.commit_to_rows();
        let constraint_commitment = ConstraintCommitment::new(composed_evaluations, commitment);
        #[cfg(feature = "std")]
        debug!(
            "Computed constraint evaluation commitment (Merkle tree of depth {}) in {} ms",
            constraint_commitment.tree_depth(),
            now.elapsed().as_millis()
        );
        constraint_commitment
    }
}
