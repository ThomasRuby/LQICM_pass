#include<stdio.h>
#include<stdlib.h>
#include<time.h>

int main(){
    int i, fact;
    srand(time(NULL));
    int n=rand()%100;
    int x=rand()%1000;
    int j=0; 
    int y=5;
    int a=5;
    while(j<n){
        fact=1;
        i=1;
        while (i<=y) { 
            fact=fact*i; 
            i=i+1;
        }
        printf("blabla %d %d", i, fact);
        if(x>100){
          y=x+a;
        }
        printf("blabla %d", y);
        if(x<=100){
          y=x+100;
        }
        printf("blabla %d", y);
        i=j;
        a=0;
        j=i+1;
    }
    return i;
}

