all: composite

composite: composite.c
	make -C parser
	gcc -std=gnu99 -Wall -o $@ -I include -L lib composite.c -lzmq -lpthread


.phony: run

run:
	PATH=$(PATH):. ./composite < parser/test5.smt2
