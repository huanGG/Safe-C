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
/*@ requires oldp == s;
    ensures \dangling(oldp) || oldp == \null;
*/
void delete_c_dlist(dnode* s)
// shape p: forword, r;
{
	dnode *p;
	dnode *tail;
	if (s != NULL) {
		tail = s->l;
		p = s;
		while (p != tail) { 
			s = p;
			p = p->r;
			free(s);
		}
		free(p);
	}
	return;
}
