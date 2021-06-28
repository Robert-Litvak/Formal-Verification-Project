int bad_min3(int x, int y, int z) {
    int tmp = x;
    if (y < tmp) tmp = y;
    if (z < tmp) tmp = x;
    return tmp;
}

int bad_add(int x, int y){
	int result = x;
	for (int i = y; i > 0; i -= 1){
		result += 1;
	}
	return result;
}

int bad_mul(int x, int y){
	int result = 0;
	for (int i = y; i >= 0; i -= 1){
		result += x;
	}
	return result;
}

void bad_fibonacci_array(int fib[], int length){
	fib[0] = 1;
	fib[1] = 1;
	for (int i = 2; i < length; i += 1){
		fib[i] = fib[i-2] + fib[i-1];
	}
}

int bad_mc91(int n){
	int c = 1;
	while (c > 0){
		c -= 1;
		if (n < 100) {
			n -= 10;
		}
		else {
			n += 11;
			c += 2;
		}
	}
	return n;
}

int bad_tricky_sub(int x, int iterations){
	int odd = 1;
	int even = 2;
	int result = x;
	for (int i = 1; i <= iterations; i += 1){
		result += odd;
		result -= even;
		odd += 2;
		even += 2;
	}
	return result;
}
