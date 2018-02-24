// 操作单链表的两个函数，仅验证形状

//#include <stdlib.h>

#define NULL 0
void* malloc(unsigned);
void free(void *);
void exit(int);

typedef struct node{
	struct node *next;
	int data;
}Node;
//@ shape next: list;

/*@ requires \true;
    exits \exit_status == 1;
    ensures \length(\result, next) == n;
*/
Node * create(int n) {
	Node *p;
	Node *head;
	int i;
	int k;
	k = 1;
	head = NULL;
	while (k <= n) // 若无invariant子句，默认为 invariant \true; 
	{
		p = (Node*)malloc(sizeof(Node));
		if (p == NULL){
		    exit(1);
		}
		p->next = head;
		p->data=k;
		head = p;
		k = k + 1;
	}
	return head;
}
