// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use examples::{do_work, Example};
use std::time::Duration;
use winterfell::{
    crypto::hashers::Blake3_256, math::fields::f128::BaseElement, FieldExtension, ProofOptions,
};

const SIZES: [(usize, usize); 3] = [(128, 1_024), (256, 1_024), (512, 1_024)];

fn do_work(c: &mut Criterion) {
    let mut group = c.benchmark_group("do_work");
    let traces: Vec<_> = (1..513).map(|i| (i, 1024)).collect();
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(20));

    let options = ProofOptions::new(32, 8, 0, FieldExtension::None, 4, 255);

    for (num_traces, trace_lenght) in traces.iter() {
        let do_work =
            do_work::DoWorkExample::<Blake3_256<BaseElement>>::new(*num_traces, *trace_lenght, options.clone());
        group.bench_function(BenchmarkId::from_parameter(num_traces), |bench| {
            bench.iter(|| do_work.prove());
        });
    }
    group.finish();
}

criterion_group!(do_work_group, do_work);
criterion_main!(do_work_group);
