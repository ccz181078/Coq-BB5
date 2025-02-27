#!/bin/bash

cp printers.out printers.ml
cp BB4_verified_enumeration.out BB4_verified_enumeration.ml

# We need high stack size for compiling the OCaml extraction
# Get the hard limit for stack size
HARD_LIMIT=$(ulimit -H -s 2>/dev/null)

# Get the current soft limit
SOFT_LIMIT=$(ulimit -S -s 2>/dev/null)


# Verify the change
echo "Stack size limit: $(ulimit -S -s)"

echo "Compiling extraction..."

ocamlbuild BB4_verified_enumeration.native -pkg zarith

if [ $? -ne 0 ]; then  # Check if the command failed
    echo ""
    echo "Compilation failed most likely because of stack overflow"
    echo "To extend your stack size do:"
    echo "    ulimit -s unlimited"
    echo "After that, retry"
    exit -1
fi

echo "Extraction compiled with success"
echo "Running extraction, see generated 'BB4_verified_enumeration.csv'..."

echo "machine,status,decider" > BB4_verified_enumeration.csv
./BB4_verified_enumeration.native >> BB4_verified_enumeration.csv

echo "BB4 extraction done!"

if command -v sha256sum &> /dev/null; then
    ACTUAL_HASH=$(sha256sum "BB4_verified_enumeration.csv" | awk '{print $1}')
elif command -v shasum &> /dev/null; then
    ACTUAL_HASH=$(shasum -a 256 "BB4_verified_enumeration.csv" | awk '{print $1}')
else
    echo "Error: No SHA-256 hashing tool found."
    exit 1
fi

EXPECTED_HASH=6a4abba432b1b36ad7c45a2382ed1d8ce08aee30401964e36ce74453755b5c08
# Compare the hashes
if [[ "$ACTUAL_HASH" == "$EXPECTED_HASH" ]]; then
    echo "Success: Hash matches the expected one from BB4 extraction."
    exit 0
else
    echo "Error: Hash does not match the expected one from BB4 extraction."
    echo "Expected: $EXPECTED_HASH"
    echo "Actual:   $ACTUAL_HASH"
    exit 1
fi