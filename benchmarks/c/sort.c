void max_sort(int array[], int size){
	int tmp;
	for(int length = size; length >= 1; length = length - 1){
		int i = 0;
		int i_max = 0;
		for(i = 1; i < length; i = i + 1){
			if(array[i] > array[i_max]){
				i_max = i;
			}
		}
		tmp = array[length-1];
		array[length-1] = array[i_max];
		array[i_max] = tmp;
	}
}