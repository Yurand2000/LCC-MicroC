struct my_struct { int num; }

int main()
{
    struct my_struct mystr;
    struct my_struct *ptr = &mystr;

    mystr.num = 10;
    print(mystr.num);
    print(ptr->num);
    ptr->num = 20;
    print(mystr.num);
    print(ptr->num);

    return 0;
}