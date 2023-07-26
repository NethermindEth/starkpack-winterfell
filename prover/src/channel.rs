// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use air::{
    proof::{Commitments, Context, JointTraceQueries, OodFrame, Queries, StarkProof},
    Air, ConstraintCompositionCoefficients, DeepCompositionCoefficients,
};
use core::marker::PhantomData;
use crypto::{ElementHasher, RandomCoin};
use fri::{self, FriProof};
use math::{FieldElement, ToElements};
use utils::collections::Vec;

#[cfg(feature = "concurrent")]
use utils::iterators::*;

// TYPES AND INTERFACES
// ================================================================================================
#[derive(Debug)]
pub struct ProverChannel<'a, A, E, H, R>
where
    A: Air,
    E: FieldElement<BaseField = A::BaseField>,
    H: ElementHasher<BaseField = A::BaseField>,
    R: RandomCoin<BaseField = E::BaseField, Hasher = H>,
{
    n: usize,
    airs: &'a Vec<A>,
    public_coin: R,
    contexts: Vec<Context>,
    commitments: Commitments,
    ood_frames: Vec<OodFrame>,
    pow_nonce: u64,
    _field_element: PhantomData<E>,
}

// PROVER CHANNEL IMPLEMENTATION
// ================================================================================================

impl<'a, A, E, H, R> ProverChannel<'a, A, E, H, R>
where
    A: Air,
    E: FieldElement<BaseField = A::BaseField>,
    H: ElementHasher<BaseField = A::BaseField>,
    R: RandomCoin<BaseField = A::BaseField, Hasher = H>,
{
    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    /// Creates a new prover channel for the specified `air` and public inputs.
    pub fn new(airs: &'a Vec<A>, mut pub_inputs_elements_vec: Vec<Vec<A::BaseField>>) -> Self {
        assert_eq!(
            n,
            airs.len(),
            "number of airs is not equal to the number of proofs"
        );
        assert_eq!(
            n,
            pub_inputs_elements_vec.len(),
            "number of public inputs is not equal to the number of proofs"
        );
        let contexts: Vec<Context> = airs
            .iter()
            .map(|air| Context::new::<A::BaseField>(air.trace_info(), air.options().clone()))
            .collect();

        // build a seed for the public coin; the initial seed is a hash of the proof context and
        // the public inputs, but as the protocol progresses, the coin will be reseeded with the
        // info sent to the verifier
        let mut coin_seed_elements = contexts[0].to_elements();
        for mut pub_inputs_elements in pub_inputs_elements_vec.iter() {
            coin_seed_elements.append(&mut pub_inputs_elements);
        }

        ProverChannel {
            n,
            airs,
            public_coin: RandomCoin::new(&coin_seed_elements),
            contexts,
            commitments: Commitments::default(),
            ood_frames: vec![n; OodFrame::default()],
            pow_nonce: 0,
            _field_element: PhantomData,
        }
    }

    // COMMITMENT METHODS
    // --------------------------------------------------------------------------------------------

    /// Commits the prover the extended execution trace.
    pub fn commit_trace(&mut self, trace_root: H::Digest) {
        self.commitments.add::<H>(&trace_root);
        self.public_coin.reseed(trace_root);
    }

    /// Commits the prover to the evaluations of the constraint composition polynomial.
    pub fn commit_constraints(&mut self, constraint_root: H::Digest) {
        self.commitments.add::<H>(&constraint_root);
        self.public_coin.reseed(constraint_root);
    }

    /// Saves the evaluations of trace polynomials over the out-of-domain evaluation frame. This
    /// also reseeds the public coin with the hashes of the evaluation frame states.
    pub fn send_ood_trace_states(&mut self, trace_states_vec: Vec<&[Vec<E>]>) {
        for trace_states in trace_states_vec.iter() {
            let result = self.ood_frame.set_trace_states(trace_states);
            self.public_coin.reseed(H::hash_elements(&result));
        }
    }

    /// Saves the evaluations of constraint composition polynomial columns at the out-of-domain
    /// point. This also reseeds the public coin wit the hash of the evaluations.
    pub fn send_ood_constraint_evaluations(&mut self, evaluations: &[E]) {
        for ood_frame in self.ood_frames.iter() {
            ood_frame.set_constraint_evaluations(evaluations);
        }
        self.public_coin.reseed(H::hash_elements(evaluations));
    }

    // PUBLIC COIN METHODS
    // --------------------------------------------------------------------------------------------

    /// Returns a set of random elements required for constructing an auxiliary trace segment with
    /// the specified index.
    ///
    /// The elements are drawn from the public coin uniformly at random.
    pub fn get_aux_trace_segment_rand_elements(&mut self, aux_segment_idx: usize) -> Vec<E> {
        self.airs[0]
            .get_aux_trace_segment_random_elements(aux_segment_idx, &mut self.public_coin)
            .expect("failed to draw random elements for an auxiliary trace segment")
    }

    /// Returns a set of coefficients for constructing a constraint composition polynomial.
    ///
    /// The coefficients are drawn from the public coin uniformly at random.
    pub fn get_constraint_composition_coeffs(&mut self) -> ConstraintCompositionCoefficients<E> {
        self.airs[0]
            .get_constraint_composition_coefficients(&mut self.public_coin)
            .expect("failed to draw composition coefficients")
    }

    /// Returns an out-of-domain point drawn uniformly at random from the public coin.
    pub fn get_ood_point(&mut self) -> E {
        self.public_coin.draw().expect("failed to draw OOD point")
    }

    /// Returns a set of coefficients for constructing a DEEP composition polynomial.
    ///
    /// The coefficients are drawn from the public coin uniformly at random.
    pub fn get_deep_composition_coeffs(&mut self) -> DeepCompositionCoefficients<E> {
        self.airs[0]
            .get_deep_composition_coefficients(self.airs, &mut self.public_coin)
            .expect("failed to draw DEEP composition coefficients")
    }

    /// Returns a set of positions in the LDE domain against which the evaluations of trace and
    /// constraint composition polynomials should be queried.
    ///
    /// The positions are drawn from the public coin uniformly at random.
    pub fn get_query_positions(&mut self) -> Vec<usize> {
        let num_queries = self.contexts[0].options().num_queries();
        let lde_domain_size = self.contexts[0].lde_domain_size();
        self.public_coin
            .draw_integers(num_queries, lde_domain_size)
            .expect("failed to draw query position")
    }

    /// Determines a nonce, which when hashed with the current seed of the public coin results
    /// in a new seed with the number of leading zeros equal to the grinding_factor specified
    /// in the proof options.
    pub fn grind_query_seed(&mut self) {
        let grinding_factor = self.contexts[0].options().grinding_factor();

        #[cfg(not(feature = "concurrent"))]
        let nonce = (1..u64::MAX)
            .find(|&nonce| self.public_coin.check_leading_zeros(nonce) >= grinding_factor)
            .expect("nonce not found");

        #[cfg(feature = "concurrent")]
        let nonce = (1..u64::MAX)
            .into_par_iter()
            .find_any(|&nonce| self.public_coin.check_leading_zeros(nonce) >= grinding_factor)
            .expect("nonce not found");

        self.pow_nonce = nonce;
        self.public_coin.reseed_with_int(nonce);
    }

    // PROOF BUILDER
    // --------------------------------------------------------------------------------------------
    /// Builds a proof from the previously committed values as well as values passed into
    /// this method.
    pub fn build_proof(
        self,
        trace_queries: Vec<JointTraceQueries>,
        constraint_queries: Queries,
        fri_proof: FriProof,
    ) -> StarkProof {
        StarkProof {
            context: self.contexts[0],
            commitments: self.commitments,
            ood_frames: self.ood_frames,
            trace_queries,
            constraint_queries,
            fri_proof,
            pow_nonce: self.pow_nonce,
        }
    }
}

// FRI PROVER CHANNEL IMPLEMENTATION
// ================================================================================================

impl<'a, A, E, H, R> fri::ProverChannel<E> for ProverChannel<'a, A, E, H, R>
where
    A: Air,
    E: FieldElement<BaseField = A::BaseField>,
    H: ElementHasher<BaseField = A::BaseField>,
    R: RandomCoin<BaseField = A::BaseField, Hasher = H>,
{
    type Hasher = H;

    /// Commits the prover to a FRI layer.
    fn commit_fri_layer(&mut self, layer_root: H::Digest) {
        self.commitments.add::<H>(&layer_root);
        self.public_coin.reseed(layer_root);
    }

    /// Returns a new alpha drawn from the public coin.
    fn draw_fri_alpha(&mut self) -> E {
        self.public_coin.draw().expect("failed to draw FRI alpha")
    }
}
