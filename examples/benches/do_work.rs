// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use examples::{do_work, Example};
use std::time::Duration;
use winterfell::{
    crypto::hashers::Blake3_256, math::fields::f128::BaseElement, FieldExtension, ProofOptions, verify,
};

const NUM_COL: usize = 10;

fn do_work_prover(c: &mut Criterion) {
    let mut group = c.benchmark_group("do_work_prove");
    let traces: Vec<_> = (1..=8).map(|i| (2_u32.pow(i - 1) as usize, 2_u32.pow(20 - i + 1) as usize)).collect();
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(1));

    let options = ProofOptions::new(32, 8, 0, FieldExtension::None, 4, 255);
    println!("{:?}", options);

    for (num_traces, trace_lenght) in traces.iter() {
        let do_work = do_work::DoWorkExample::<Blake3_256<BaseElement>>::new(
            *num_traces,
            *trace_lenght,
            NUM_COL,
            options.clone(),
        );

        group.bench_function(BenchmarkId::from_parameter(*num_traces), |bench| {
            bench.iter(|| do_work.prove());
        });
    }
    group.finish();
}

fn do_work_verifier(c: &mut Criterion) {
    let mut group = c.benchmark_group("do_work_verifier");
    let traces: Vec<_> = (1..=8).map(|i| (2_u32.pow(i - 1) as usize, 2_u32.pow(20 - i + 1) as usize)).collect();
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(1));

    let options = ProofOptions::new(32, 8, 0, FieldExtension::None, 4, 255);
    println!("{:?}", options);

    for (num_traces, trace_lenght) in traces.iter() {
        let do_work = do_work::DoWorkExample::<Blake3_256<BaseElement>>::new(
            *num_traces,
            *trace_lenght,
            NUM_COL,
            options.clone(),
        );
        let proof = do_work.prove();

        group.bench_function(BenchmarkId::from_parameter(*num_traces), |bench| {
            bench.iter(|| do_work.verify(proof.clone()));
        });
    }
    group.finish();
}
criterion_group!(do_work_group, do_work_prover, do_work_verifier);
criterion_main!(do_work_group);
