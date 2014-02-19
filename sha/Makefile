CC=~/compcert/ccomp -DCOMPCERT

target: sha sha.v
	./sha < shatest.c
	./sha < /dev/null

sha.v: sha.c
	~/compcert/clightgen -DCOMPCERT sha.c

sha: shatest.c sha.c
	$(CC) shatest.c sha.c -o sha
