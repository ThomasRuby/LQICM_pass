#include<stdio.h>
#include<stdlib.h>
#include<time.h>

void use(int y){
    printf("y=%d\n",y);
}

int main(){
    int i=0,y=0;
    srand(time(NULL));
    int x=rand()%100;
    int x2=rand()%100;
    int z;
    while(i<100){
        z=y*y;
        use(z);
        if(x<50)
          y=x+x;
        else
          y=0;
        use(y);
        x=x2;
        use(x);
        i++;
    }
    return 42;
}
