void foo(int *a, int i) {
    a[i] = 10;
}

int main() {
    int a[10];
    foo(a, 5);
    print(a[5]);
    return 0;
}