#include <stdio.h>
#include <stdlib.h>

struct node
{
    int data;
    struct node* next;
};

void init(struct node* head){
    head = NULL;
}

struct node* push(struct node* head,int data){
    struct node* tmp = (struct node*)malloc(sizeof(struct node));
    if(tmp == NULL)
        exit(0);
    tmp->data = data;
    tmp->next = head;
    head = tmp;
    return head;
}

struct node* pop(struct node *head,int *element){
    struct node* tmp = head;
    *element = head->data;
    head = head->next;
    free(tmp);
    return head;
}

int empty(struct node* head){
    return head == NULL ? 1 : 0;
}

void display(struct node* head){
    struct node *current;
    current = head;
    if(current!= NULL){
        printf("Stack: ");
        do{
            printf("%d ",current->data);
            current = current->next;
        } while (current!= NULL);
        printf("\n");
    } else printf("The Stack is empty\n");
}

struct node * reverse_malloc_rec(struct node *head){
    int element;
    struct node * temp = NULL;
    while(head!=NULL){
        head = pop(head,&element);
        temp = push(temp,element);
        /* return push(reverse_malloc_rec(head),*element); */
    }
    return temp;
}

int main()
{
    struct node* head = NULL;
    int size, element,i;
    int counter = 0;

    printf("Enter the number of stack elements:");
    scanf("%d",&size);

    printf("--- Push elements into the linked stack ---\n");

    init(head);

    for (i = 0; i < size; i++) {
        head = push(head,i);
        display(head);
        counter++;
    }
    
    printf("--- Reversing --- \n");
    head = reverse_malloc_rec(head);
    display(head);

    /* printf("--- Pop elements from the linked stack --- \n"); */
    /* while(empty(head) == 0) */
    /* { */
    /*     head = pop(head,&element); */
    /*     printf("Pop %d from stack\n",element); */
    /*     display(head); */
    /* } */

    return 0;
}
