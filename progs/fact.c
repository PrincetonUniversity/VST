/* Hello World program */

// #include <stdlib.h>
#include <stdio.h>

int fac(int n)
{
	int i, f;

	f = i = 1;

	while (i < n)
		f *= ++i;

	return f;
}

int main() {

	printf("%i\n",fac(17));

	return 1;
}