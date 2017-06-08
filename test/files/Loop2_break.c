#include<stdio.h>
#include<stdlib.h>
#include<time.h>
#include<math.h>

void use(int y){
    printf("y=%d\n",y);
}

int main(){
    int i=0,j=0,y=0;
    srand(time(NULL));
    int x=rand()%100;
    y=rand()%100;
    int n=rand()%1000;
    int n2=rand()%1000;
    int x2=rand()%100;
    int x3=rand()%100;
    int z=0;
    while(i<n){
        z=y*y;
        use(z);
        j=0;
        while(j<n2){
          use(z);
          if(x3<50)
            break;
          use(y);
          j++;
        }
        y=x+x;
        use(y);
        i++;
    }
    return 42;
}

