char *global_string = "global_string";

int main()
{
    char *local_string = "local_string";

    print_string(global_string);
    print_string(local_string);
    print_string("string_literal");
    return 0;
}