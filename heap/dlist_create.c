// 操作双向链表的若干函数, 仅验证形状

#define NULL 0
void* malloc(unsigned);
void free(void *);
void exit(int);

typedef struct DLNode {
  struct DLNode *r;
  struct DLNode *l;
  int data2;
}dnode;
//@ shape l, r: dlist;
 
/*@ requires \true;
    exits \exit_status == 1;
    ensures  \length(\result, r) == n;
*/
dnode* create_dlist(int const n) 
{
	dnode *p;
	dnode *head;
	int i;
	head = (dnode*)malloc(sizeof(dnode));
	if (head == NULL) {
	    exit(1);
	}
	head->l = NULL;
	head->r = NULL;
	p = NULL;
	i = 1;
	//@ loop invariant \true;
	while (i < n) { 
		p =  (dnode*)malloc(sizeof(dnode));
		if (p == NULL) {
		    exit(1);
		}
		p->r = head;
		p->l = NULL;
		head->l = p;
		head = p;
		p = NULL;
		i = i + 1;
	}
	return head;
}