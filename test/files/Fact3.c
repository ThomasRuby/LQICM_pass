#include<stdio.h>
#include<stdlib.h>
#include<time.h>


int main(){
    int i;
    srand(time(NULL));
    int n=rand()%100;
    int y=rand()%100;
    int x=rand()%100;
    int z=rand()%100;
    int j=0; 
    i=0;
    while(i<100){
        x=y+10;
        printf("blabla %d", x);
        z=y;
        while (y<x) { 
            z=z*y; 
            y=y+1;
        }
        y=1;
        x=i;
        printf("blabla %d", x);
        i=x+1;
        printf("blabla %d %d", i, z);
    }
    return i;
}
/* int main(){ */
/*     int i, fact; */
/*     srand(time(NULL)); */
/*     int n=rand()%100; */
/*     int j=0; */ 
/*     while(j<n){ */
/*         fact=1; */
/*         i=1; */
/*         while (i<=n) { */ 
/*             fact=fact*i; */ 
/*             i=i+1; */
/*         } */
/*         printf("blabla %d %d", i, fact); */
/*         j=j+1; */
/*     } */
/*     return i; */
/* } */
