int main()
{
    int *my_int = (int*) mem_alloc( sizeof(int) );
    *my_int = 15;
    print(*my_int);
    mem_free(my_int);
    return 0;
}