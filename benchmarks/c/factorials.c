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

void five_factorials_v2() {
	int i = 0;
    int results[5] = {1, 2, 3, 4, 5};
	results[i] = results[i] * results[i-1];
	i = i + 1;
	results[i] = results[i] * results[i-1];
	i = i + 1;
	results[i] = results[i] * results[i-1];
	i = i + 1;
	results[i] = results[i] * results[i-1];
	i = i + 1;
	results[i] = results[i] * results[i-1];
}

int factorial_with_while(int n){
	int result = 1;
	int i = n;
	while (i > 0){
		result = result * i;
		i = i - 1;
	}
	return result;
}

int factorial_with_for(int n){
	int result = 1;
	for (int i = n; i > 0; i = i - 1){
		result = result * i;
	}
	return result;
}
