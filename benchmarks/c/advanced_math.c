int gcd(int x, int y){
	int x_m = x;
	int y_m = y;
	while (x_m != y_m){
		while (x_m > y_m){
			x_m -= y_m;
		}
		while (y_m > x_m){
			y_m -= x_m;
		}
	}
	return x_m;
}

bool is_prime(int x){
	int i = 2;
	int j = 2;
	if (x == 1){
		return false;
	}
	for (i = 2; i < x; i += 1){
		for (j = 2; j < x; j += 1){
			if (i * j == x){
				return false;
			}
		}
	}
	return true;
}

void fibonacci_array(int fib[], int length){
	fib[0] = 1;
	fib[1] = 1;
	for (int i = 2; i < length; i += 1){
		fib[i] = fib[i-2] + fib[i-1];
	}
}

void factorials_array(int factorials[], int length){
	factorials[0] = 1;
	factorials[1] = 1;
	for (int i = 2; i < length; i += 1){
		factorials[i] = i * factorials[i-1];
	}
}

void five_factorials() {
	int i = 0;
    int results[5];
	results[i] = 1;
	i = i + 1;
	results[i] = 2 * results[0];
	i = i + 1;
	results[i] = 3 * results[1];
	i = i + 1;
	results[i] = 4 * results[2];
	i = i + 1;
	results[i] = 5 * results[3];
}

int limited_factorial_with_while(int n){
	int result = 1;
	int i = n;
	while (i > 0){
		result = result * i;
		i = i - 1;
	}
	return result;
}

int limited_factorial_with_for(int n){
	int result = 1;
	for (int i = n; i > 0; i = i - 1){
		result = result * i;
	}
	return result;
}

int power_of_two(int exp){
	int result = 1;
	for (int i = 0; i < exp; i += 1){
		result *= 2;
	}
	return result;
}
