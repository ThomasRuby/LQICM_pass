#include<stdlib.h>
#include<stdio.h>

int main(int argc, char **argv){
    int i,j,t=0;
    int * p;
    for (i = 0; i < 10; i++) {
        for (j = 0; j < 10; j++) {
            p = malloc (sizeof(int));
            if ((i+j)%7==0){
                *p = 7;
                break;
            }
            else {
                *p = t;
                t++;
                free(p);
            }
        }
    }
    printf("p=%d \n",*p);
    printf("%d\n",t);
    return 42;
}
