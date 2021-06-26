void array_index_value_id(){
	int result[100];
	for (int i = 0; i < 100; i = i + 1){
		result[i] = 0;
	}
	for (int j = 1; j < 100; j = j + 1){
		result[j] = result[j-1] + 1;
	}
}

int mc91(int n){
	int c = 1;
	while (c > 0){
		c -= 1;
		if (n > 100) {
			n -= 10;
		}
		else {
			n += 11;
			c += 2;
		}
	}
	return n;
}

int square(int x){
	int result = 0;
	int dif = 1;
	for (int i = 0; i < x; i += 1){
		result += dif;
		dif += 2;
	}
	return result;
}

int foo(int x, int iterations){
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
