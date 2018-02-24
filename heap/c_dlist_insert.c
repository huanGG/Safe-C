// 操作循环双向链表的函数，仅验证形状

#define NULL 0
void* malloc(unsigned);
void free(void *);
void exit(int);

typedef struct DLNode {
  struct DLNode *r;
  struct DLNode *l;
  int data2;
}dnode;
//@ shape l, r: c_dlist;

//@ logic dnode* oldp;

/*@ requires \length(p, r) == n && 0 <= i <= n && oldp == p;
    exits \exit_status == 1;
    ensures \length(\result, r) == n + 1 && (oldp == \null && n == 0 || oldp == \result && n > 0);
*/ 
dnode * insert(dnode *p, int const n, int i)
// shape p: forword, r;
{
	dnode *q;
	dnode *s;
	int j;
	if (p == NULL) {
		p = (dnode*)malloc(sizeof(dnode));
		if(p == NULL){
		    exit(1);
		}
		p->l = p;
		p->r = p;
	}
	else {
		j = 1;
		q = p->r;
		//@ loop invariant 0 <= i <= n && j >= 1;
		while (j < i) {
			q = q->r;
			j = j + 1; 
		}
		s = (dnode*)malloc(sizeof(dnode));
		if (s == NULL){
		    exit(1);
		}
		s->l = q->l;
		q->l->r = s;
		s->r = q;
		q->l = s;
		s = NULL; q = NULL;
	}
	return p;
}
