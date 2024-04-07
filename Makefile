parser:
	bison -d  parser.y
lexer: parser
	flex  tokenizer.l

test: lexer
	g++ parser.tab.c lex.yy.c 
	./a.out < ../tests/test1.py 2>debug.txt
	dot -Tpdf graph.dot -o graph.pdf


run: test

clear: run
	rm lex.yy.c
	rm parser.tab.c
	rm parser.tab.h
	rm debug.txt
	rm a.out
	rm graph.dot
	rm graph.pdf
	