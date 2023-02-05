struct my_struct1 { struct my_struct2 x; }

struct my_struct2 { struct my_struct1 x; }

int main()
{
  return 0;
}
