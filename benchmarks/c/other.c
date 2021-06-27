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

int tricky_square(int x){
	int result = 0;
	int dif = 1;
	for (int i = 0; i < x; i += 1){
		result += dif;
		dif += 2;
	}
	return result;
}

int tricky_sub(int x, int iterations){
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

void two(int x){
	int temp = x*3;
	for (int i = 1; i <= 6; i += 1){
		temp += 1;
	}
	int magic = (temp/3) - x;
}

void three_same_digits(int d){
	int number = 0;
	int digits_sum = 0;
	for (int i = 1; i < 1000; i *= 10){
		number += d * i;
		digits_sum += d;
	}
}

int three_digit_number_duplication(int x){
	int y = 0;
	int z = 0;
	for (int i = 1; i < 1000000; i *= 1000){
		y += x * i;
	}
	z = x * 7;
	z = z * 11;
	z = z * 13;
}
