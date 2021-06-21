void array_index_value_id(){
	int result[100];
	for (int i = 0; i < 100; i = i + 1){
		result[i] = 0;
	}
	for (int j = 1; j < 100; j = j + 1){
		result[j] = result[j-1] + 1;
	}
}

void test_exists(){
	int array[100];
	array[13] = 77;
}
