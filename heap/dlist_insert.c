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
/*@ requires \length(p,r) == n && 1 <= i <= n +1 && oldp == p;
    exits \exit_status == 1;
    ensures  \length(\result, r) == n + 1 && (oldp == \null || oldp == \result);
*/
dnode *insert(dnode *p, int n, int i)
//@ shape p : forward, r;
{
	dnode *q;
	dnode *s;
	int j;
	if (p == NULL) {
		p = (dnode*)malloc(sizeof(dnode));
		if (p == NULL) {
		    exit(1);
		}
		p->l = NULL;
		p->r = NULL;
	}
	else {
		j = 1;
		q = p;
		//@ loop invariant \true;
		while ((j < i) && (q->r != NULL)) {
			q = q->r;
			j = j + 1;
		}
		s = (dnode*)malloc(sizeof(dnode));
		if (s == NULL) {
		    exit(1);
		}
		s->l = q;
		s->r = q->r;
		if (q->r != NULL) {
			q->r->l = s;
		}
		q->r = s;
	}
	return p;
}
