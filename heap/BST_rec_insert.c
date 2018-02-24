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

/*@ logic Node* oldp; */

/*@
requires oldp == p;
exits \exit_status == 1;
ensures  \result != \null && (oldp == \null || oldp == \result);
*/
Node * RECinsert(Node * p, const int data)
{
    if ( p == NULL) 
	{
		p = (Node *)malloc(sizeof(Node));
		if(p == NULL) 
			exit(1);
		p->l = NULL;
		p->r = NULL;
		p->data = data;
    }
	else if (p->data > data)
	{
		p->l = RECinsert(p->l, data);
    }
	else if (p->data < data)
	{
		p->r = RECinsert(p->r, data);	
    }
    return p;
}
