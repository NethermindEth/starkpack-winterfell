use crate::{Blake3_192, Blake3_256, Example, ExampleOptions, HashFunction, Sha3_256};
use core::marker::PhantomData;
use log::debug;
use std::time::Instant;
use winterfell::{
    crypto::{DefaultRandomCoin, Digest, ElementHasher, MerkleTree},
    math::{fields::f128::BaseElement, FieldElement, StarkField},
    ProofOptions, Prover, StarkProof, Trace, TraceTable, VerifierError,
};

mod air;
use air::{DoWorkAir, PublicInputs};
mod prover;
use prover::DoWorkProver;

// Do WORK AUTHENTICATION EXAMPLE
// ================================================================================================
pub fn get_example(
    options: &ExampleOptions,
    num_traces: usize,
    trace_lenght: usize,
) -> Result<Box<dyn Example>, String> {
    let (options, hash_fn) = options.to_proof_options(28, 8);
    println!("Getting example");

    match hash_fn {
        HashFunction::Blake3_192 => Ok(Box::new(DoWorkExample::<Blake3_192>::new(
            num_traces,
            trace_lenght,
            options,
        ))),
        HashFunction::Blake3_256 => Ok(Box::new(DoWorkExample::<Blake3_256>::new(
            num_traces,
            trace_lenght,
            options,
        ))),
        HashFunction::Sha3_256 => Ok(Box::new(DoWorkExample::<Sha3_256>::new(
            num_traces,
            trace_lenght,
            options,
        ))),
        _ => Err("The specified hash function cannot be used with this example.".to_string()),
    }
}

pub struct DoWorkExample<H: ElementHasher> {
    options: ProofOptions,
    starting_vec: Vec<BaseElement>,
    results: Vec<BaseElement>,
    trace_lenght: usize,
    _hasher: PhantomData<H>,
}

impl<H: ElementHasher> DoWorkExample<H> {
    pub fn new(num_traces: usize, trace_lenght: usize, options: ProofOptions) -> Self {
        let starting_vec: Vec<_> = (0..num_traces as u128)
            .into_iter()
            .map(|i| BaseElement::new(i))
            .collect();
        let results = calculate_results(&starting_vec, trace_lenght);
        //TODO^ calculate results in utils
        DoWorkExample {
            options,
            starting_vec,
            results,
            trace_lenght,
            _hasher: PhantomData,
        }
    }
}

fn calculate_results(starting_vec: &Vec<BaseElement>, trace_lenght: usize) -> Vec<BaseElement> {
    starting_vec
        .iter()
        .map(|start| {
            let mut result = start.to_owned();
            for _ in 0..trace_lenght {
                result = result.exp(3u128) + BaseElement::new(42u128);
            }
            result
        })
        .collect()
}

impl<H: ElementHasher> Example for DoWorkExample<H>
where
    H: ElementHasher<BaseField = BaseElement>,
{
    fn prove(&self) -> StarkProof {
        debug!(
            "Generating proof for do work of n+1 = n^3 + 42, {} times for {} traces",
            self.trace_lenght,
            self.starting_vec.len(),
        );
        // Create prover
        let prover = DoWorkProver::<H>::new(self.options.clone());

        // Generate traces
        let now = Instant::now();
        let traces = prover.build_do_work_traces(&self.starting_vec, self.trace_lenght);
        debug!(
            "Generated execution trace of {} registers and 2^{} steps in {} ms",
            traces[0].width(),
            traces[0].length(),
            now.elapsed().as_millis()
        );

        // Generate proof
        prover.prove(self.starting_vec.len(), traces).unwrap()
    }

    fn verify(&self, proof: StarkProof) -> Result<(), VerifierError> {
        let pub_inputs_vec = self
            .starting_vec
            .iter()
            .zip(self.results.iter())
            .map(|(&start, &result)| PublicInputs { start, result })
            .collect();
        winterfell::verify::<DoWorkAir, H, DefaultRandomCoin<H>>(proof, pub_inputs_vec)
    }

    fn verify_with_wrong_inputs(
        &self,
        proof: winterfell::StarkProof,
    ) -> Result<(), winterfell::VerifierError> {
        todo!();
    }
}
