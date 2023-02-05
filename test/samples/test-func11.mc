void foo(int* a, int i){
    *a = 15;
}

int main(){
    int a[10];
    a[0] = 5;
    a[1] = 10;

    foo(a, 0);
    print(a[0]);
    print(a[1]);
    return 0;
}