cp printers.out printers.ml
cp BB2x4_verified_enumeration.out BB2x4_verified_enumeration.ml

# We need high stack size for compiling the OCaml extraction
# Get the hard limit for stack size
HARD_LIMIT=$(ulimit -H -s 2>/dev/null)

# Get the current soft limit
SOFT_LIMIT=$(ulimit -S -s 2>/dev/null)

echo "Extending stack size is needed to make sure the extraction compiles"

if [ "$HARD_LIMIT" == "unlimited" ] || [ -z "$HARD_LIMIT" ]; then
    echo "Setting stack size to unlimited"
    sudo ulimit -S -s unlimited
else
    echo "Setting stack size to hard limit: $HARD_LIMIT"
    sudo ulimit -S -s "$HARD_LIMIT"
fi

# Verify the change
echo "New stack size limit: $(ulimit -S -s)"

echo "Compiling extraction..."

ocamlbuild BB2x4_verified_enumeration.native -pkg zarith

echo "Extraction compiled with success"
echo "Running extraction, see generated 'BB2x4_verified_enumeration.csv'..."

echo "machine,status,decider" > BB2x4_verified_enumeration.csv
./BB2x4_verified_enumeration.native >> BB2x4_verified_enumeration.csv

# Remove empty trailing line
if [[ "$OSTYPE" == "darwin"* ]]; then
    sed -i '' '${/^$/d;}' BB2x4_verified_enumeration.csv
else
    sed -i '${/^$/d;}' BB2x4_verified_enumeration.csv
fi

echo "BB2x4 extraction done!"

if command -v sha256sum &> /dev/null; then
    ACTUAL_HASH=$(sha256sum "BB2x4_verified_enumeration.csv" | awk '{print $1}')
elif command -v shasum &> /dev/null; then
    ACTUAL_HASH=$(shasum -a 256 "BB2x4_verified_enumeration.csv" | awk '{print $1}')
else
    echo "Error: No SHA-256 hashing tool found."
    exit 1
fi

EXPECTED_HASH=d6e6a8da09528a67b6fba9301949f7544c987bae04b6dbbc6f3d99ea5ea8518a
# Compare the hashes
if [[ "$ACTUAL_HASH" == "$EXPECTED_HASH" ]]; then
    echo "Success: Hash matches the expected one from BB2x4 extraction."
    exit 0
else
    echo "Error: Hash does not match the expected one from BB2x4 extraction."
    echo "Expected: $EXPECTED_HASH"
    echo "Actual:   $ACTUAL_HASH"
    exit 1
fi