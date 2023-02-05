struct my_rec_struct2 { struct my_rec_struct rec_str; }

struct my_struct { int num; }

struct my_rec_struct { struct my_struct str; }

int main()
{
    struct my_rec_struct x;
    struct my_rec_struct2 y;

    x.str.num = 10;
    print(x.str.num);

    y.rec_str.str.num = 20;
    print(y.rec_str.str.num);

    return 0;
}