int add(int x, int y){
	int result = x;
	for (int i = y; i > 0; i -= 1){
		result += 1;
	}
	return result;
}

int sub(int x, int y){
	int result = x;
	for (int i = y; i > 0; i -= 1){
		result -= 1;
	}
	return result;
}

int mul(int x, int y){
	int result = 0;
	for (int i = y; i > 0; i -= 1){
		result += x;
	}
	return result;
}

int div(int x, int y){
	int q = 0;
	int r = x - q * y;
	while (r >= y){
		q += 1;
		r -= y;
	}
	return q;
}

int mod(int x, int y){
	int q = 0;
	int r = x - q * y;
	while (r >= y){
		q += 1;
		r -= y;
	}
	return r;
}

int abs(int x){
	if (x < 0){
		return -x;
	}
	return x;
}

int fibonacci_1000_array(int fib[], int length){
	fib[0] = 1;
	fib[1] = 1;
	for (int i = 2; i < length; i += 1){
		fib[i] = fib[i-2] + fib[i-1];
	}
}
