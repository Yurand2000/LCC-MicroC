int main(){
    int *ptr;
    int a[5];
    ptr = &a[0];
    *(ptr + 1) = 10;
    print(a[1]);
    return 0;
}