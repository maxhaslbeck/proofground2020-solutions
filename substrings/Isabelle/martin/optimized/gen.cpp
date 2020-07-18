#include <cstdio>
#include <cstdlib>

int main(int argc, char **argv) {
    int n = atoi(argv[1]);

    for (int i = 0; i <= n; i++) printf("x");
    for (int i = 0; i <= n; i++) printf("y");
    printf("\n");

    for (int i = 0; i < n; i++) printf("x");
    printf("yx");
    for (int i = 0; i < n; i++) printf("y");
    printf("\n");

    return 0;
}
