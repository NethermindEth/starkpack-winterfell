use std::marker::PhantomData;

use winterfell::{crypto::ElementHasher, ProofOptions, BaseElement, TraceTable};

use crate::{Example, ExampleOptions, HashFunction, Blake3_192, Blake3_256, Sha3_256};

pub fn get_example(
    options: &ExampleOptions,
    num_traces: usize,
    trace_lenght: usize,
) -> Result<Box<dyn Example>, String> {
    let (options, hash_fn) = options.to_proof_options(28, 8);

    match hash_fn {
        HashFunction::Blake3_192 => Ok(Box::new(DoWorkExample::<Blake3_192>::new(options))),
        HashFunction::Blake3_256 => Ok(Box::new(DoWorkExample::<Blake3_256>::new(options))),
        HashFunction::Sha3_256 => Ok(Box::new(DoWorkExample::<Sha3_256>::new(options))),
        _ => Err("The specified hash function cannot be used with this example.".to_string()),
    }
}

pub struct DoWorkExample<H: ElementHasher> {
    options: ProofOptions,
    _hasher: PhantomData<H>,
}

impl<H: ElementHasher> DoWorkExample<H> {
    pub fn new(options: ProofOptions) -> Self{
        DoWorkExample { options, _hasher: PhantomData }
    }
}

impl<H: ElementHasher> Example for DoWorkExample<H> 
where
    H: ElementHasher<BaseField = BaseElement>,
{
    fn prove(&self) -> winterfell::StarkProof {
        todo!();
    }

    fn verify(&self, proof: winterfell::StarkProof) -> Result<(), winterfell::VerifierError> {
        todo!();
    }

    fn verify_with_wrong_inputs(&self, proof: winterfell::StarkProof) -> Result<(), winterfell::VerifierError> {
        todo!();
    }
    
}

fn build_do_work_trace(start: BaseElement, n: usize) -> TraceTable<BaseElement> {
    todo!();
}
