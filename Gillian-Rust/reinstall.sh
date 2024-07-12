opam pin add gillian ../../Gillian --working-dir -y
opam update gillian
opam upgrade gillian
dune build @install
# dune exec -- gillian-rust verify ../tests/proph/vec_std_proph.stdout  --proph --proc "Vec::<T>::push" -l tmi
cd ..
./test_ci_gil.sh