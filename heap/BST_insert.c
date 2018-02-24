
#define NULL 0
void* malloc(unsigned);
void free(void *);
void exit(int);

typedef struct node
{
	int data; 
	struct node *l; 
	struct node *r;
}Node;
//@ shape l, r : tree;

//@ logic Node* oldroot;
/*@
requires  oldroot == root;
exits \exit_status == 1;
ensures \result != \null && (oldroot == \null || oldroot == \result);
*/
Node * TREEinsert(Node *root, const int data) 
{
    Node *q; 
	Node *t;
    if (root == NULL) 
	{
		root = (Node *)malloc(sizeof(Node));
       	if(root == NULL)
			exit(1);
		root->l = NULL;
		root->r = NULL;
		root->data = data;
    } 
	else 
	{
		q = root;
		while(q!=NULL && q->data != data)
		{
			t = q;
			if (q->data > data)
			{
				q = q->l;
			} 
			else
			{
				q = q->r;
			}
		}
		if (q == NULL)
		{
			q = (Node*)malloc(sizeof(Node));    
			if(q == NULL)
				exit(1);
			q->l = NULL;
			q->r = NULL;
			q->data = data;
			if (t->data > data)
			{
				t->l = q;
			}
			else
			{
				t->r = q;
			}
		}
    }
    return root;
}
