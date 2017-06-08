#include<stdio.h>
#include<stdlib.h>
#include<time.h>

int main(){
    int i, fact;
    srand(time(NULL));
    int n=rand()%100;
    int j=0; 
    while(j<n){
        fact=1;
        i=1;
        while (i<=n) { 
            fact=fact*i; 
            if(fact>9000)
              break;
            i=i+1;
        }
        printf("blabla %d %d", i, fact);
        j=j+1;
    }
    return i;
}
