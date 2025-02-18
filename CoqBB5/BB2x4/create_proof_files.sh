#!/bin/bash

cp ../BB5/Prelims.v ../BB5/List_Routines.v ../BB5/List_Tape.v ../BB5/Tactics.v ../BB5/TM.v ../BB5/TNF.v ../BB5/Makefile .
cp ../BB5/Deciders/Decider_Halt.v ../BB5/Deciders/Decider_Loop.v ../BB5/Deciders/Decider_NGramCPS.v ../BB5/Deciders/Decider_RepWL.v ../BB5/Deciders/Deciders_Common.v ../BB5/Deciders/Verifier_Halt.v Deciders
cp ._CoqProject _CoqProject

# Define replacements using parallel arrays
search_terms=("CoqBB5" "BB5_Statement" "BB5_Encodings" "BB5_Deciders_Generic" "BB5_Make_TM" "BB5_minus_one" "47176870" "47176869")
replace_terms=("CoqBB2x4" "BB2x4_Statement" "BB2x4_Encodings" "BB2x4_Deciders_Generic" "BB2x4_Make_TM" "BB2x4_minus_one" "3932964" "3932963")

# Define files to process for general replacements
files=(
    Prelims.v
    List_Routines.v
    List_Tape.v
    Tactics.v
    TM.v
    TNF.v
    Deciders/Decider_Halt.v
    Deciders/Decider_Loop.v
    Deciders/Decider_NGramCPS.v
    Deciders/Decider_RepWL.v
    Deciders/Deciders_Common.v
    Deciders/Verifier_Halt.v
)

# Apply general replacements to all files
for file in "${files[@]}"; do
    if [[ -f "$file" ]]; then  # Ensure file exists
        for i in "${!search_terms[@]}"; do
            if [[ "$OSTYPE" == "darwin"* ]]; then
                sed -i '' "s/${search_terms[i]}/${replace_terms[i]}/g" "$file"
            else
                sed -i "s/${search_terms[i]}/${replace_terms[i]}/g" "$file"
            fi
        done
    else
        echo "Warning: File '$file' not found, skipping..."
    fi
done