use winterfell::FieldElement;

use super::{
    BaseElement, DefaultRandomCoin, DoWorkAir, ElementHasher, PhantomData, ProofOptions, Prover,
    PublicInputs, Trace, TraceTable,
};

// DO WORK PROVER
// ================================================================================================

pub struct DoWorkProver<H: ElementHasher> {
    options: ProofOptions,
    _hasher: PhantomData<H>,
}

impl<H: ElementHasher> DoWorkProver<H> {
    pub fn new(options: ProofOptions) -> Self {
        Self {
            options,
            _hasher: PhantomData,
        }
    }

    // For now all traces has the same lenght
    pub fn build_do_work_traces(
        &self,
        starting_vec: &Vec<BaseElement>,
        trace_lenght: usize,
    ) -> Vec<TraceTable<BaseElement>> {
        starting_vec
            .iter()
            .map(|&start| build_do_work_trace(start, trace_lenght))
            .collect()
    }
}

impl<H: ElementHasher> Prover for DoWorkProver<H>
where
    H: ElementHasher<BaseField = BaseElement>,
{
    type BaseField = BaseElement;
    type Air = DoWorkAir;
    type Trace = TraceTable<Self::BaseField>;
    type HashFn = H;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;

    fn get_pub_inputs(
        &self,
        trace: &Self::Trace,
    ) -> <<Self as Prover>::Air as winterfell::Air>::PublicInputs {
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

fn build_do_work_trace(start: BaseElement, trace_lenght: usize) -> TraceTable<BaseElement> {
    let trace_width = 275;
    let mut trace = TraceTable::new(trace_width, trace_lenght);
    trace.fill(
        |state| {
            for i in 0..state.len() {
                state[i] = start
            }
            state[0] = start;
        },
        |_, state| {
            state[0] = state[0].exp(3u32.into()) + BaseElement::new(42);
            for i in 1..state.len() {
                state[i] = state[i];
            }
        },
    );
    trace
}
