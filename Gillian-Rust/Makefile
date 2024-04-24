init-dev:
	opam switch create . --packages=ocaml-variants.5.1.1+options -y --deps-only
	opam pin add gillian "https://github.com/GillianPlatform/Gillian.git#f5995995deb0334f8b292c07fb15f7bdebde6514" -y
	opam install ocaml-lsp-server ocamlformat -y