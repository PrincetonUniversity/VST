#!/usr/bin/env bash

# Usage: ./RefinedVST.sh
# NOTE need to compile RefinedCC first, follow RefinedVST.md
# Assume path is root of VST
# path is relevant path to ./refinedVST/typing/frontend_stuff, where the frontend is located


c_file="examples/test_f_temps.c"

pushd ./refinedVST/typing/frontend_stuff || exit
basename=$(basename -- "$c_file" .${c_file##*.})
dirname=$(dirname -- "$c_file")
absolute_dir=$(realpath "$dirname")
stripped_file="${dirname}/${basename}_stripped.c"
generated_dir="${absolute_dir}/proofs/${basename}"

# generates the clight AST
dune exec -- refinedc check "$c_file"
sed 's/\[\[rc::[^]]*\]\]//g' "$c_file" > "$stripped_file"
# compcert must be < 3.15
clightgen -normalize "$stripped_file" -o "${generated_dir}/generated_code_vst_clight.v"
popd || exit

# compile stuff
REFINEDVSTFLAGS="-R ${generated_dir} VST.typing.examples.${basename}"
# make .depend -B REFINEDVSTFLAGS="${REFINEDVSTFLAGS}"

make "${generated_dir}/generated_code_vst_clight.vo"   -j  REFINEDVSTFLAGS="${REFINEDVSTFLAGS}"
make "${generated_dir}/generated_code_vst.vo"          -j  REFINEDVSTFLAGS="${REFINEDVSTFLAGS}"
make "${generated_dir}/generated_spec_vst.vo"          -j  REFINEDVSTFLAGS="${REFINEDVSTFLAGS}"

# find all files that starts with the name "generated_proof" in ${generated_dir}
proofs=$(find "${generated_dir}" -name "generated_proof*.v")
proofs_compiled=()
for proof in $proofs; do
    make "${proof}o" -j  REFINEDVSTFLAGS="${REFINEDVSTFLAGS}"; proofs_compiled+=("${proofs}") || perror "Failed to compile ${proof}"
done

make _CoqProject -B REFINEDVSTFLAGS="${REFINEDVSTFLAGS}"

# set colour to green
echo -e "\033[0;32m"
for proof_compiled in $proofs_compiled; do
    echo "Successfully checked: ${proof_compiled}"
done
echo -e "\033[0m"