#!/bin/bash

# Backup the original main.rs file
cp main.rs main.rs.bak

PATTERN="let k = 2_usize.pow([0-9]);"

# Loop from 0 to 17
for i in {0..17}; do
    # Use sed to replace SOME_NUMBER with the current iteration number
    sed -i.bak "s/$PATTERN/let k = 2_usize.pow($i);/" main.rs
    rg "let k = 2_usize"

    # Run cargo run, capturing both stdout and stderr
    cargo run > output_$i.txt

    # Check if cargo run was successful
    if [ $? -ne 0 ]; then
        echo "cargo run failed on iteration $i"
        break
    fi
done

# Restore the original main.rs file
mv main.rs.bak main.rs

