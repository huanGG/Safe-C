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


/*@ requires \length(head, next) == m && m >=0;
    exits \exit_status == 1;
    ensures \result == head && 0 <= \length(head, next) <= m;
*/
Node* DeleteNode(Node * const head, int key, int m) {
	Node *p;
	Node *prev;
	//int i = 0, j = 0, k = 0;
	if(head != NULL)
	{
		prev = head;
		p = head->next;
		
		while(p != NULL)
		{
			if(p->data < key)
			{
				prev->next = p->next;
				free(p);
				p = prev->next;
				//j = j + 1;
			}
			else
			{
				prev = p;
				p = p->next;
				//k = k + 1;
			}
			//i = i + 1;
		}
	}
	return head;
}
