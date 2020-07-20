all: gen main_official.native main_optimized.native

clean:
	ocamlbuild -clean
	rm -rf gen official.ml optimized.ml

official.ml: Official.thy
	isabelle build -evD .
	mv official.ocaml official.ml
	mv optimized.ocaml optimized.ml

optimized.ml: Optimized.thy
	isabelle build -evD .
	mv official.ocaml official.ml
	mv optimized.ocaml optimized.ml

main_official.native: main_official.ml official.ml
	ocamlbuild -package zarith main_official.native

main_optimized.native: main_optimized.ml optimized.ml
	ocamlbuild -package zarith main_optimized.native

gen: gen.cpp
	g++ -o gen gen.cpp
