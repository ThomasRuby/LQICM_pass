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
    while(j<n){
        fact=1;
        i=1;
        while (i<=y) { 
            fact=fact*i; 
            i=i+1;
        }
        printf("blabla %d %d", i, fact);
        if(x<100)
          y=x;
        else
          y=x+100;
        i=j;
        j=i+1;
    }
    return i;
}

