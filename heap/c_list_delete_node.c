// 操作循环单链表的函数，仅验证形状
/* ensures的编写有误，因现在\dangling()函数没有消除，Z3证明会出错 */

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
/*@ requires \length(p,next) == n && n > 0 && 1 <= i <= n && oldp == p;
    exits \exit_status == 1;
    ensures 
		\length(\result, next) == n - 1 && oldp == \result
		|| \dangling(oldp) && \length(\result, next) == n - 1
		|| \dangling(oldp) && \dangling(\result);
*/
Node* DeleteNode(Node *p, int const n, int i) {
	Node *q;
	Node *t;
	Node *s;
	int j;
	if (i == 1) {
		if (p->next == p) {
			free(p);
		}
		else {
			q = p->next;
			while (q->next != p){
				q = q->next;
			}
			q->next = p->next;
			free(p);
			p = q->next;
		}
	}
	else {
		j = 2;
		t = p;
		q = p->next;
		while (j < i) { 
			t = q;
			q = q->next;
			j = j + 1;
		}
		t->next = q->next;
		free(q);
	}
	return p;
}
