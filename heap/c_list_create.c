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

/*@ requires \true;
    exits \exit_status == 1;
    ensures \length(\result, next) == n;
*/
Node* create_c_list(int const n) { 
	Node *p;
	Node *head;
	Node *tail;
	int i;
	p = (Node*)malloc(sizeof(Node));
	if (p == NULL){
	    exit(1);
	}
	head = p; 
	tail = p;
	tail->next = p;
	i = 1;
	while (i < n) { //循环不变式默认为\true。
		p = (Node*)malloc(sizeof(Node));
		if (p == NULL){
		    exit(1);
		}
		p->next = head;
		tail->next = p;
		head = p;
		i = i + 1;
	}
	return head;
}
