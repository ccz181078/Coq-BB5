#!/bin/bash

cp ../BB5/Prelims.v ../BB5/List_Routines.v ../BB5/List_Tape.v ../BB5/Tactics.v ../BB5/TM.v ../BB5/TNF.v .
mkdir -p Deciders
cp ../BB5/Deciders/Decider_Halt.v ../BB5/Deciders/Decider_Loop.v ../BB5/Deciders/Decider_NGramCPS.v ../BB5/Deciders/Decider_RepWL.v ../BB5/Deciders/Deciders_Common.v ../BB5/Deciders/Verifier_Halt.v Deciders
cp ._CoqProject _CoqProject

# Define replacements using parallel arrays
search_terms=("CoqBB5" "BB5_Statement" "BB5_Encodings" "BB5_Deciders_Generic" "BB5_Make_TM" "BB5_minus_one" "47176870" "47176869")
replace_terms=("CoqBB4" "BB4_Statement" "BB4_Encodings" "BB4_Deciders_Generic" "BB4_Make_TM" "BB4_minus_one" "3932964" "3932963")

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

# Tactics.v
if [[ -f "Tactics.v" ]]; then
    if [[ "$OSTYPE" == "darwin"* ]]; then
        sed -i '' '/Definition St_eqb(s1 s2:St) :=/,/end\./c\
Definition St_eqb(s1 s2:St) :=\
match s1,s2 with\
| St0,St0 | St1,St1 | St2,St2 | St3,St3 => true\
| _,_ => false\
end.\

' "Tactics.v"
    else
        sed -i '/Definition St_eqb(s1 s2:St) :=/,/end\./c\
Definition St_eqb(s1 s2:St) :=\
match s1,s2 with\
| St0,St0 | St1,St1 | St2,St2 | St3,St3 => true\
| _,_ => false\
end.\

' "Tactics.v"
    fi
else
    echo "Warning: Fichier 'Tactics.v' introuvable, passage au suivant..."
fi