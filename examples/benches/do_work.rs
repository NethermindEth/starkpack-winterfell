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

fn do_work(c: &mut Criterion) {
    let mut group = c.benchmark_group("do_work");
    /* let num_traces_vec =
        (1..513).filter(|&n| n % 10 == 0 || n == 128 || n == 256 || n == 512 || n == 1); */
    // let traces: Vec<_> = num_traces_vec.map(|i| (i, 1024)).collect();
    let traces: Vec<_> = (250..261).map(|i| (i, 1024)).collect();
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(20));

    let options = ProofOptions::new(32, 8, 0, FieldExtension::None, 4, 255);

    for (num_traces, trace_lenght) in traces.iter() {
        let do_work = do_work::DoWorkExample::<Blake3_256<BaseElement>>::new(
            *num_traces,
            *trace_lenght,
            options.clone(),
        );
        let proof = do_work.prove();

        group.bench_function(BenchmarkId::from_parameter(num_traces), |bench| {
            bench.iter(|| do_work.verify(proof.clone()));
        });
    }
    group.finish();
}

criterion_group!(do_work_group, do_work);
criterion_main!(do_work_group);
