#define N 100
#define SWAP(X,Y) { tmp = (X); (X) = (Y); (Y) = tmp; }

int min3_array(int arr[N], int i, int j, int k) {
    if (arr[i] < arr[j]) {
        if (arr[i] < arr[k]) return arr[i];
    }
    else {
        if (arr[j] < arr[k]) return arr[j];
    }
    return arr[k];
}

int min3_array_indirect(int arr[N], int is[3]) {
    if (arr[is[0]] < arr[is[1]]) {
        if (arr[is[0]] < arr[is[2]]) return arr[is[0]];
    }
    else {
        if (arr[is[1]] < arr[is[2]]) return arr[is[1]];
    }
    return arr[is[2]];
}

void sort3(int arr[N], int i) {
    int tmp;

    if (arr[i] > arr[i + 1]) SWAP(arr[i], arr[i + 1]);
    if (arr[i + 1] > arr[i + 2]) SWAP(arr[i + 1], arr[i + 2]);
    if (arr[i] > arr[i + 1]) SWAP(arr[i], arr[i + 1]);
}
