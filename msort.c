#include <stdlib.h>

void merge(int A[], int B[], int res[], int a, int b) {

    int x = 0;
    int y = 0;

    for (int i = 0; i < a + b; i++) {
        if (x < a) {
            if (y < b) {
                if (A[x] < B[y]) {
                    res[i] = A[x];
                    x++;
                } else {
                    res[i] = B[y];
                    y++;
                }
            } else {
                res[i] = A[x];
                x++;
            }
        } else {
            if (y < b) {
                res[i] = B[y];
                y++;
            }
        }
    }
}

int *msort(int array[], int size) {
    if (size == 1) {
        int* res = malloc(sizeof(int));
        if (!res) exit(1);
        
        res[0] = array[0];
        return res;
    } else {
        int* res = malloc(size * sizeof(int));
        if (!res) exit(1);
        
        int* A = msort(array, size / 2);
        int* B = msort(array + size / 2, size / 2 + size % 2);

        merge(A, B, res, size / 2, size / 2 + size % 2);

        free(A);
        free(B);

        return res;
    }
}
