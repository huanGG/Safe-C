// �������������������������֤��״

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
	while (k <= n) // ����invariant�Ӿ䣬Ĭ��Ϊ invariant \true; 
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
