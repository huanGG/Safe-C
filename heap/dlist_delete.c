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
 
//@ logic dnode* oldp;
int n;
/*@ requires \length(s, r) == n && oldp == s;
    ensures  \dangling(oldp) && \dangling(\result)
			|| oldp == \null && \result == \null;
*/
dnode* delete_dlist(dnode* s)
//@ shape s : forward, r;
{
	dnode *p;
	p = s;
	//@ loop invariant \true;
	while (p != NULL) {
		s = p;
		p = p->r;
		free(s);
	}
	return s;
}
