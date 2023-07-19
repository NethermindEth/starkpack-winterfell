#![cfg_attr(not(feature = "std"), no_std)]
pub use crate::crypto::{hashers::Blake3_256, DefaultRandomCoin};
pub use crate::math::{fields::f128::BaseElement, FieldElement, ToElements};
pub use prover::{
    crypto, iterators, math, Air, AirContext, Assertion, AuxTraceRandElements, BoundaryConstraint,
    BoundaryConstraintGroup, ByteReader, ByteWriter, ColMatrix, ConstraintCompositionCoefficients,
    ConstraintDivisor, DeepCompositionCoefficients, Deserializable, DeserializationError,
    EvaluationFrame, FieldExtension, ProofOptions, Prover, ProverError, Serializable, SliceReader,
    StarkProof, Trace, TraceInfo, TraceLayout, TraceTable, TraceTableFragment,
    TransitionConstraintDegree,
};
pub use verifier::{verify, VerifierError};

fn main() {
    pub fn build_do_work_trace(start: BaseElement, n: usize) -> TraceTable<BaseElement> {
        let trace_width: usize = 1;
        let mut trace = TraceTable::new(trace_width, n);
        trace.fill(
            |state| {
                state[0] = start;
            },
            |_, state| {
                state[0] = state[0].exp(3u32.into()) + BaseElement::new(42);
            },
        );
        trace
    }
    // Public inputs for our computation will consist of the starting value and the end result.

    pub struct PublicInputs {
        start: BaseElement,
        result: BaseElement,
    }
    impl ToElements<BaseElement> for PublicInputs {
        fn to_elements(&self) -> Vec<BaseElement> {
            vec![self.start, self.result]
        }
    }
    pub struct WorkAir {
        context: AirContext<BaseElement>,
        start: BaseElement,
        result: BaseElement,
    }
    impl Air for WorkAir {
        type BaseField = BaseElement;
        type PublicInputs = PublicInputs;
        fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
            assert_eq!(1, trace_info.width());
            let degrees = vec![TransitionConstraintDegree::new(3)];
            WorkAir {
                context: AirContext::new(trace_info, degrees, 2, options),
                start: pub_inputs.start,
                result: pub_inputs.result,
            }
        }
        fn evaluate_transition<E: FieldElement + From<Self::BaseField>>(
            &self,
            frame: &EvaluationFrame<E>,
            _periodic_values: &[E],
            result: &mut [E],
        ) {
            let current_state = &frame.current()[0];
            let next_state = current_state.exp(3u32.into()) + E::from(42u32);
            result[0] = frame.next()[0] - next_state;
        }
        fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
            let last_step = self.trace_length() - 1;
            vec![
                Assertion::single(0, 0, self.start),
                Assertion::single(0, last_step, self.result),
            ]
        }
        fn context(&self) -> &AirContext<Self::BaseField> {
            &self.context
        }
    }
    struct WorkProver {
        options: ProofOptions,
    }
    impl WorkProver {
        pub fn new(options: ProofOptions) -> Self {
            Self { options }
        }
    }
    impl Prover for WorkProver {
        type BaseField = BaseElement;
        type Air = WorkAir;
        type Trace = TraceTable<Self::BaseField>;
        type HashFn = Blake3_256<Self::BaseField>;
        type RandomCoin = DefaultRandomCoin<Self::HashFn>;
        fn get_pub_inputs(&self, trace: &Self::Trace) -> PublicInputs {
            let last_step = trace.length() - 1;
            PublicInputs {
                start: trace.get(0, 0),
                result: trace.get(0, last_step),
            }
        }
        fn options(&self) -> &ProofOptions {
            &self.options
        }
    }

    let start = BaseElement::new(3);
    let start1 = BaseElement::new(4);
    let n = 1024;
    // Build the execution trace and get the result from the last step.
    let trace = build_do_work_trace(start, n);
    let trace1 = build_do_work_trace(start1, n);
    let result = trace.get(0, n - 1);
    let result1 = trace1.get(0, n - 1);
    // Define proof options; these will be enough for ~96-bit security level.
    let options = ProofOptions::new(
        32, // number of queries
        8,  // blowup factor
        0,  // grinding factor
        FieldExtension::None,
        8,  // FRI folding factor
        31, // FRI max remainder polynomial degree
    );
    // Instantiate the prover and generate the proof.
    let prover = WorkProver::new(options);
    let proof = prover.prove(trace, trace1).unwrap();
    // Verify the proof. The number of steps and options are encoded in the proof itself,
    // so we don't need to pass them explicitly to the verifier.
    let pub_inputs = PublicInputs { start, result };
    let pub_inputs1 = PublicInputs {
        start: start1,
        result: result1,
    };
    let validation = verify::<
        WorkAir,
        Blake3_256<BaseElement>,
        DefaultRandomCoin<Blake3_256<BaseElement>>,
    >(proof, pub_inputs, pub_inputs1)
    .is_ok();
    println!("{:?}", validation);
    assert!(validation)
}
