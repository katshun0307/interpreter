builder = dune
target = main

default: mdeq.exe

.PHONY: test clean

mdeq.exe: src/* main.ml
	dune build main.exe --profile release
	mv ./_build/default/main.exe ./mdeq.exe

test:
	dune runtest --profile release

doc:
	dune build @doc --profile release
	# mv ./_build/default/_doc/_html ./docs

parser:
	cd src; menhir --explain parser.mly

conflicts: src/parser.mly
	menhir src/parser.mly --explain
	mv src/parser.conflicts ./
	rm src/parser.ml src/parser.mli

.PHONY: clean clean/parser
clean:
	dune clean

clean/parser:
	rm src/parser.ml src/parser.mli
