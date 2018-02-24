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
    ensures \result == head && (\length(head, next) == m || \length(head, next) == m - 1);
*/
Node *delete(Node * const head, int data, int const m) {
	Node *ptr;
	Node *ptr1;

	int j;
	j = 1;
	if(head != NULL)
	{
		ptr1 = head;
		ptr = head->next;
		while((ptr != NULL) && (ptr->data < data))
		{
			ptr1 = ptr;
			ptr = ptr->next;
			j = j + 1;
		}
		if((ptr != NULL) && (ptr->data == data))
		{
			ptr1->next = ptr->next; 
			free(ptr);
		}
	}
	return head;
}
