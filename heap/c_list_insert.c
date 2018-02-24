// 操作循环单链表的函数，仅验证形状

#define NULL 0
void* malloc(unsigned);
void free(void *);
void exit(int);

typedef struct node{
	struct node * next;
	int data;
}Node;
//@ shape next: c_list;

//@ logic Node* oldp;
/*@ requires 
	\length(p,next) == n && n >= 0 && 1 <= i <= n +1 && oldp == p;
    exits \exit_status == 1;
    ensures 
	   \length(\result, next) == n + 1 
	   && (oldp == \null && n == 0 || oldp == \result && n > 0);
*/
Node * insert(Node *p, int n, int i) {
	Node *q;
	Node *s;
	int j;
	if (p == NULL) {
		p = (Node*)malloc(sizeof(Node));
		if(p == NULL){
		    exit(1);
		}
		p->next = p;
	}
	else {
		j = 1;
		q = p;
		while (j < i) {
			q = q->next;
			j = j + 1;
		}
		s = (Node*)malloc(sizeof(Node));
		if(s == NULL) {
		    exit(1);
		}
		s->next = q->next;
		q->next = s;
		s = NULL;
		q = NULL;
	}
	return p;
}
 