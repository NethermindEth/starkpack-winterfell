#!/bin/bash

# columns=(1 10 100 275)
# COLUMN_PATTERN="const NUM_COLS: usize = \([0-9]|[1-9][0-9]|[1-3][0-9][0-9]\);"
SPLIT_PATTERN="let k = 2_usize.pow([0-9]);"

# for column in "${columns[@]}"; do
echo "Processing $column columns"
# Backup the original main.rs file
cp main.rs main.rs.bak
# sed "s/$COLUMN_PATTERN/const NUM_COLS: usize = $column;/" main.rs

# Loop from 0 to 17
for i in {0..7}; do
    # Use sed to replace SOME_NUMBER with the current iteration number
    sed -i.bak "s/$SPLIT_PATTERN/let k = 2_usize.pow($i);/" main.rs
    rg "let k = 2_usize"
    rg "const NUM_COLS: usize" 

    # Run cargo run, capturing both stdout and stderr
    cargo run --features dhat-heap

    # Check if cargo run was successful
    if [ $? -ne 0 ]; then
        echo "cargo run failed on iteration $i"
        break
    fi

    if [[ -f "dhat-heap.json" ]]; then
        mv dhat-heap.json dhat-heap_$i.json
    fi
done

# Restore the original main.rs file
mv main.rs.bak main.rs
# done
