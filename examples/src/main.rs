// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log::debug;
use winterfell::{ProofOptions, FieldExtension};
use std::io::Write;
use std::time::Instant;
use structopt::StructOpt;

#[cfg(feature = "std")]
use examples::{do_work, ExampleOptions, ExampleType};

// EXAMPLE RUNNER
// ================================================================================================
#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn main() {
    // configure logging
    env_logger::Builder::new()
        .format(|buf, record| writeln!(buf, "{}", record.args()))
        .filter_level(log::LevelFilter::Debug)
        .init();

    // read command-line args
    let options = ExampleOptions::from_args();
    println!("{:?}", options);

    debug!("============================================================");

    // instantiate and prepare the example
    let example = match options.example {
        ExampleType::DoWork {
            num_traces,
            trace_lenght,
        } => do_work::get_example(&options, num_traces, trace_lenght),
    }
    .expect("The example failed to initialize.");

    // generate proof
    let now = Instant::now();
    let example = example.as_ref();
    
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();
    let proof = example.prove();
    debug!(
        "---------------------\nProof generated in {} ms",
        now.elapsed().as_millis()
    );

    let proof_bytes = proof.to_bytes();
    debug!("Proof size: {:.1} KB", proof_bytes.len() as f64 / 1024f64);
    let conjectured_security_level = options.get_proof_security_level(&proof, true);

    #[cfg(feature = "std")]
    {
        let proven_security_level = options.get_proof_security_level(&proof, false);
        debug!(
            "Proof security: {} bits ({} proven)",
            conjectured_security_level, proven_security_level,
        );
    }

    #[cfg(not(feature = "std"))]
    debug!("Proof security: {} bits", conjectured_security_level);

    #[cfg(feature = "std")]
    debug!(
        "Proof hash: {}",
        hex::encode(blake3::hash(&proof_bytes).as_bytes())
    );

    // verify the proof
    debug!("---------------------");
    // let parsed_proof = &StarkProof::from_bytes(StarkProof, &proof_bytes).unwrap();
    let parsed_proof = proof.from_bytes(&proof_bytes).unwrap();
    // assert_eq!(proof, parsed_proof);
    let now = Instant::now();
    match example.verify(proof) {
        Ok(_) => debug!(
            "Proof verified in {:.1} ms",
            now.elapsed().as_micros() as f64 / 1000f64
        ),
        Err(msg) => debug!("Failed to verify proof: {}", msg),
    }
    debug!("============================================================");
}
