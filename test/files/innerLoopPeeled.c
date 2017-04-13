#include<stdio.h>
#include<stdlib.h>
#include<time.h>

void use(int y){
    printf("y=%d\n",y);
}

int main(){
    int i=0;
    srand(time(NULL));
    int n=rand()%100;
    int x=rand()%100;
    int y=rand()%100;
    int x2=rand()%100;
    int j=0; 
    int z;
    while(j<n){
        i=1;
        while(i<=n){
          z=y*y;
          use(z);
          y=x+x;
          use(y);
          i=i+1;
        }
        printf("blabla %d %d", y, z);
        j=j+1;
    }
    return 42;
}

