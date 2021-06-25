int min3_v1(int x, int y, int z) {
    if (x < y) {
        if (x < z) return x;
        else return z;
    }
    else {
        if (y < z) return y;
        else return z;
    }
}

int min3_v2(int x, int y, int z) {
    if (x < y) {
        if (x < z) return x;
    }
    else {
        if (y < z) return y;
    }
    return z;
}

int min3_v3(int x, int y, int z) {
    int tmp = x;
    if (y < tmp) tmp = y;
    if (z < tmp) tmp = z;
    return tmp;
}
