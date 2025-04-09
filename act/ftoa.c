#include <stdio.h>
#include <stdlib.h>

char* ftoa(float i) {
	char* x = malloc(20);
	sprintf(x, "%f", i);
	return x;
}
