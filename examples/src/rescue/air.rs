// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use super::rescue;
use crate::utils::{are_equal, is_zero, not, EvaluationResult};
use prover::{
    math::field::{f128::BaseElement, FieldElement},
    Air, Assertion, ComputationContext, EvaluationFrame, ExecutionTrace, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

// CONSTANTS
// ================================================================================================

const CYCLE_LENGTH: usize = 16;
const NUM_HASH_ROUNDS: usize = 14;
const TRACE_WIDTH: usize = 4;

/// Specifies steps on which Rescue transition function is applied.
const CYCLE_MASK: [BaseElement; CYCLE_LENGTH] = [
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ZERO,
    BaseElement::ZERO,
];

// RESCUE AIR
// ================================================================================================

pub struct PublicInputs {
    pub seed: [BaseElement; 2],
    pub result: [BaseElement; 2],
}

pub struct RescueAir {
    context: ComputationContext,
    seed: [BaseElement; 2],
    result: [BaseElement; 2],
}

impl Air for RescueAir {
    type BaseElement = BaseElement;
    type PublicInputs = PublicInputs;

    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        let degrees = vec![
            TransitionConstraintDegree::with_cycles(3, vec![CYCLE_LENGTH]),
            TransitionConstraintDegree::with_cycles(3, vec![CYCLE_LENGTH]),
            TransitionConstraintDegree::with_cycles(3, vec![CYCLE_LENGTH]),
            TransitionConstraintDegree::with_cycles(3, vec![CYCLE_LENGTH]),
        ];
        let context = ComputationContext::new(TRACE_WIDTH, trace_info.length, degrees, options);
        RescueAir {
            context,
            seed: pub_inputs.seed,
            result: pub_inputs.result,
        }
    }

    fn context(&self) -> &ComputationContext {
        &self.context
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseElement>> {
        let mut result = vec![CYCLE_MASK.to_vec()];
        result.append(&mut rescue::get_round_constants());
        result
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseElement>> {
        // Assert starting and ending values of the hash chain
        let last_step = self.trace_length() - 1;
        vec![
            Assertion::single(0, 0, self.seed[0]),
            Assertion::single(1, 0, self.seed[1]),
            Assertion::single(0, last_step, self.result[0]),
            Assertion::single(1, last_step, self.result[1]),
        ]
    }

    fn evaluate_transition<E: FieldElement + From<Self::BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = &frame.current;
        let next = &frame.next;
        // expected state width is 4 field elements
        debug_assert_eq!(TRACE_WIDTH, current.len());
        debug_assert_eq!(TRACE_WIDTH, next.len());

        // split periodic values into hash_flag and Rescue round constants
        let hash_flag = periodic_values[0];
        let ark = &periodic_values[1..];

        // when hash_flag = 1, constraints for Rescue round are enforced
        rescue::enforce_round(result, &frame.current, &frame.next, &ark, hash_flag);

        // when hash_flag = 0, constraints for copying hash values to the next
        // step are enforced.
        let copy_flag = not(hash_flag);
        enforce_hash_copy(result, &frame.current, &frame.next, copy_flag);
    }
}

// HELPER EVALUATORS
// ------------------------------------------------------------------------------------------------

/// when flag = 1, enforces that the next state of the computation is defined like so:
/// - the first two registers are equal to the values from the previous step
/// - the other two registers are equal to 0
fn enforce_hash_copy<E: FieldElement>(result: &mut [E], current: &[E], next: &[E], flag: E) {
    result.agg_constraint(0, flag, are_equal(current[0], next[0]));
    result.agg_constraint(1, flag, are_equal(current[1], next[1]));
    result.agg_constraint(2, flag, is_zero(next[2]));
    result.agg_constraint(3, flag, is_zero(next[3]));
}

// RESCUE TRACE GENERATOR
// ================================================================================================

pub fn build_trace(seed: [BaseElement; 2], iterations: usize) -> ExecutionTrace<BaseElement> {
    // allocate memory to hold the trace table
    let trace_length = iterations * CYCLE_LENGTH;
    let mut trace = ExecutionTrace::new(4, trace_length);

    trace.fill(
        |state| {
            // initialize first state of the computation
            state[0] = seed[0];
            state[1] = seed[1];
            state[2] = BaseElement::ZERO;
            state[3] = BaseElement::ZERO;
        },
        |step, state| {
            // execute the transition function for all steps
            //
            // for the first 14 steps in every cycle, compute a single round of
            // Rescue hash; for the remaining 2 rounds, just carry over the values
            // in the first two registers to the next step
            if (step % CYCLE_LENGTH) < NUM_HASH_ROUNDS {
                rescue::apply_round(state, step);
            } else {
                state[2] = BaseElement::ZERO;
                state[3] = BaseElement::ZERO;
            }
        },
    );

    trace
}