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

/*@ requires \true;
    exits \exit_status == 1;
    ensures \length(\result, r) == n;
*/ 
dnode* create_c_dlist(int const n) {
	dnode *p;
	dnode *head;
	int i;
	i = 0;
	head = NULL;
	while (i < n) {  //循环不变式默认为\true
		p = (dnode*)malloc(sizeof(dnode));
		if(p == NULL){
		    exit(1);
		}
		p->r = head;
		if (head != NULL) {
			p->l = head->l;
			head->l = p;
		}
		else {
			p->l = p;
		}
		p->l->r = p;
		head = p;
		p = NULL;
		i = i + 1;
	}
	return head;
} 
