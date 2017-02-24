CC	= gcc -O2

lsencode: lsencode-v1.1.c
	$(CC) lsencode-v1.1.c -o lsencode-v1.1

install: lsencode
	mv lsencode-v1.1 $(HOME)/bin/
clean: 
	rm -f lsencode-v1.1

