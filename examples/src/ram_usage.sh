#!/bin/bash

for i in {1..10}
do
    echo "Running Do Work iteration $i"
    cargo run --features dhat-heap -- do-work -n $i -l 65536

    if [[ -f "dhat-heap.json" ]]; then
        mv dhat-heap.json dhat-heap_$i.json
    else
        echo "dhat-heap.json was not created for iteration $i"
    fi
done
