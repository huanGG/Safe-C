/* 测试进度 */
/* 编译通过，无语法错误 */


/* 合并两个有序单向链表为一个新的有序单向链表(用谓词断言) */

//#include <stdlib.h>

#define NULL 0
void* malloc(unsigned);
void free(void *);
void exit(int);

typedef struct node 
{
	struct node* next;
	int data;
}Node;
//@ shape next : list;


/*@
requires \length(h1, next) == m && \length(h2, next) == n;
exits \exit_status == 1;
ensures 
	\length(\result, next) == m + n && \length(h1, next) == m && \length(h2, next) == n;
*/
Node * merge(Node * const h1, Node * const h2, const int m, const int n)
{
    Node *h, *p, *p1, *p2, *new;
    h = NULL; 
	new = NULL;
	p = h;
	p1 = h1;
	p2 = h2;
    while(p1 != NULL && p2 != NULL) 
	{
		new = (Node*)malloc(sizeof(Node));
		if (new == NULL)
			exit(1);
		new->next = NULL;
		if (p1->data < p2->data) 
		{
			new->data = p1->data;
			p1 = p1->next;
		} 
		else 
		{
			new->data = p2->data;
			p2 = p2->next;
		}
		if (p == NULL)
		{
			p = new; 
			h = p;
		} 
		else 
		{
			p->next = new; 
			p = p->next;
		}
    }
    if (p1 == NULL) 
	{ 
		p1 = p2;
	}
    while (p1 != NULL) 
	{
		new = (Node*)malloc(sizeof(Node));
		if(new == NULL) 
			exit(1);
		new->data = p1->data; 
		new->next = NULL;
		if (p == NULL) 
		{
			p = new; 
			h= p;
		} 
		else 
		{
			p->next = new; 
			p = p->next;
		}
		p1 = p1->next;
    }
    return h;
}

