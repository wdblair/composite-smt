all: composite

composite: composite.c
	make -C parser
	gcc -std=gnu99 -Wall -o $@ -I include -L lib composite.c -lzmq -lpthread


.phony: run

clean:
	rm composite yices2
	make -C parser clean
