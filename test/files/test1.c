#include<stdio.h>
#include<stdlib.h>
#include<time.h>

int main(){
    int i, fact;
    srand(time(NULL));
    int n=rand()%100;
    int a=rand()%100;
    int j=0; 
    int y=rand()%100;
    while(j<n){
        y=a+1;
        printf("blabla %d ", y);
        if(y==a+1)
          y=y+1;
        printf("blabla %d ", y);
        j=j+1;
        y=j;
        printf("blabla %d ", y);
    }
    return i;
}

