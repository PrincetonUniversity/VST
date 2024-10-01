# RefinedVST Frontend
The files are adapted from [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc/-/commits/ea6be6de7f27855a79c9ca18e6a54ba3bd5ed883). 

##
```
pushd refinedVST/typing/frontend_stuff/
dune exec -- refinedc check examples/test_f_temps.c
sed 's/\[\[rc::[^]]*\]\]//g' examples/test_f_temps.c > examples/test_f_temps_stripped.c
# compcert must be < 3.15
clightgen -normalize examples/test_f_temps_stripped.c -o examples/proofs/test_f_temps/generated_code_vst_clight.v
popd

make .depend -B
make _CoqProject -B
echo "-R refinedVST/typing/frontend_stuff/examples/proofs/test_f_temps VST.typing.examples.test_f_temps" >> _CoqProject
# can't just do the last one because it seems that .depend does not know the dependencies between these because the mapping above is not known when generating the .depend file
coqc $(cat _CoqProject) refinedVST/typing/frontend_stuff/examples/proofs/test_f_temps/generated_code_vst_clight.v
coqc $(cat _CoqProject) refinedVST/typing/frontend_stuff/examples/proofs/test_f_temps/generated_code_vst.v
coqc $(cat _CoqProject) refinedVST/typing/frontend_stuff/examples/proofs/test_f_temps/generated_spec_vst.v
coqc $(cat _CoqProject) refinedVST/typing/frontend_stuff/examples/proofs/test_f_temps/generated_proof_vst_f_temps.v

```