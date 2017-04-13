#include<stdlib.h>
#include<stdio.h>
#include<time.h>

int main(int argc, char *argv[]){
  long long i;
  double fact;
  int g = atoi(argv[1]);
  int times = atoi(argv[2]);
  srand(time(NULL));
  int n=times*10000;
  int j=0,k=0,l=0,m=0,o=0; 
  printf("n = %d",n);
  fact=1; 
  i=1;
  /* clock_t start_t, end_t, total_t; */
  /* start_t = clock(); */
  while(j<n){
    fact=1;
    i=1;
    while (i<=n) { 
      fact=fact + i*g; 
      i=i+1;
    }
    printf("i = %lld fact = %lf  \n", i, fact);
    j=j+1;
  }
  /* end_t = clock(); */
  /* total_t = (end_t - start_t); */
  /* printf("blabla %lld %lf clock = %ld \n", i, fact, total_t); */
  printf("blabla %lld %lf  \n", i, fact);
  return i;
}

