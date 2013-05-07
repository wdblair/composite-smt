CC = gcc
FLEX = flex
BISON = bison
CFLAGS = -std=c99 -pedantic -g -Wall -I../include
LDFLAGS = -g -lgmp -lstdc++ -lyices

OBJECTS = smtlib2bisonparser.o \
	  smtlib2flexlexer.o \
	  smtlib2hashtable.o \
	  smtlib2abstractparser.o \
	  smtlib2termparser.o \
	  smtlib2utils.o \
	  smtlib2vector.o \
	  smtlib2charbuf.o \
	  smtlib2stream.o \
	  smtlib2scanner.o

YICES_OBJECTS = yices2.o \
	        yicesmain.o

all: libsmtlib2parser.a yices2

clean:
	rm -f $(OBJECTS) $(YICES_OBJECTS) libsmtlib2parser.a smtlib2yices smtlib2bisonparser.c smtlib2bisonparser.h smtlib2flexlexer.c smtlib2flexlexer.h

yices2: libsmtlib2parser.a $(YICES_OBJECTS)
	$(CC) -L../lib/ $(YICES_OBJECTS) libsmtlib2parser.a $(LDFLAGS) -o ../$@

yicesmain.o: yicesmain.c
	$(CC) $(CFLAGS) -c -o $@ $<


libsmtlib2parser.a: $(OBJECTS)
	ar rc $@ $(OBJECTS)
	ranlib $@

yices2.o: ../yices2.c
	$(CC) $(CFLAGS) -c -o $@ $<

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<


smtlib2bisonparser.c: smtlib2bisonparser.y smtlib2flexlexer.c
	$(BISON) -o $@ $<

smtlib2flexlexer.c: smtlib2flexlexer.l
	$(FLEX) --header-file="smtlib2flexlexer.h" -o $@ $<
