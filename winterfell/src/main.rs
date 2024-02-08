//#![cfg_attr(not(feature = "std"), no_std)]
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
use std::time::Instant;
pub use verifier::{verify, VerifierError};

fn main() {
    pub fn build_do_work_trace(
        start: BaseElement,
        n: usize,
        k: usize,
    ) -> Vec<&TraceTable<BaseElement>> {
        let trace_width: usize = 275;
        let len = n / k;
        let mut sub_traces = Vec::with_capacity(k);
        let mut cur_start = start;
        for _ in 0..k {
            let mut trace = TraceTable::new(trace_width, len);
            trace.fill(
                |state| {
                    state[0] = cur_start;
                },
                |_, state| {
                    state[0] = state[0].exp(3u32.into()) + BaseElement::new(42);
                },
            );
            cur_start = trace.get(0, len - 1);
            sub_traces.push(&trace);
        }
        sub_traces
    }
    // Public inputs for our computation will consist of the starting value and the end result.

    #[derive(Clone, Copy)]
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
            assert_eq!(275, trace_info.width());
            let degrees = vec![TransitionConstraintDegree::new(3)];
            WorkAir {
                //TODO this may need to be modified to get a vec of trace infos
                context: AirContext::new(trace_info, degrees, 2, options),
                start: pub_inputs.start,
                result: pub_inputs.result,
            }
        }
        fn evaluate_transition<E: FieldElement + From<Self::BaseField>>(
            &self,
            frames: Vec<&EvaluationFrame<E>>,
            _periodic_values: &[E],
            result: &mut [E],
        ) {
            //let k = frames.lem();
            for (i, &frame) in frames.iter().enumerate() {
                let current_state = &frame.current()[0];
                let next_state = current_state.exp(3u32.into()) + E::from(42u32);
                result[i][0] = frame.next()[0] - next_state;
            }
        }
        fn get_assertions(&self, k: usize, idx: usize) -> Vec<Assertion<Self::BaseField>> {
            let last_step = self.trace_length() - 1;
            if idx == 0 {
                vec![Assertion::single(0, 0, self.start)]
            }
            if idx == k - 1 {
                vec![Assertion::single(0, last_step, self.result)]
            }
            vec![]
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
        fn get_pub_inputs(&self, sub_traces: Vec<&Self::Trace>) -> PublicInputs {
            let k = sub_traces.len();
            let last_step = sub_traces[k].length() - 1;
            PublicInputs {
                start: sub_traces[0].get(0, 0),
                result: sub_traces[k].get(0, last_step),
            }
        }
        fn options(&self) -> &ProofOptions {
            &self.options
        }
    }

    //for j in 1..=10 {
    let starting_vec: Vec<_> = (0..5).map(|_| BaseElement::new(3)).collect();
    let m = 1024; //The length of the trace
    let n = starting_vec.len(); //The number of the traces
    let k = 1; //The number of folds(splits)

    // Build the execution trace and get the result from the last step.
    let traces: Vec<_> = starting_vec
        .iter()
        .map(|&start| build_do_work_trace(start, m, k))
        .collect();

    let results: Vec<_> = traces
        .iter()
        .map(|sub_traces| sub_traces[k - 1].get(0, m - 1))
        .collect();
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
    let now: Instant = Instant::now();
    let proof = prover.prove(k, n, traces).unwrap();
    println!("Generated the proof in {}ms", now.elapsed().as_millis());

    let proof_bytes: Vec<u8> = proof.to_bytes();
    println!("Proof size: {:.1} KB", proof_bytes.len() as f64 / 1024f64);
    //println!("Proof Security: {} bits", proof.security_level(true));

    //let parsed_proof: StarkProof = StarkProof::from_bytes(&proof_bytes).unwrap();
    //assert_eq!(proof, parsed_proof);
    // Verify the proof. The number of steps and options are encoded in the proof itself,
    // so we don't need to pass them explicitly to the verifier.
    let pub_inputs_vec = starting_vec
        .into_iter()
        .zip(results.into_iter())
        .map(|(start, result)| PublicInputs { start, result })
        .collect();
    let now: Instant = Instant::now();
    match verify::<WorkAir, Blake3_256<BaseElement>, DefaultRandomCoin<Blake3_256<BaseElement>>>(
        proof,
        pub_inputs_vec,
    ) {
        Ok(_) => {
            println!(
                "Proof verified in {:.1} ms",
                now.elapsed().as_micros() as f64 / 1000f64
            );
        }
        Err(err) => {
            println!("Proof is not valid\nErr: {}", err);
        }
    }
    //}
}
