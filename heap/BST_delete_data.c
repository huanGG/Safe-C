
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

/*@ logic Node * oldroot;*/

/*@
requires oldroot == root;
ensures 
\dangling(oldroot) && \result == \null
|| \dangling(oldroot)
|| oldroot == \result;
*/
Node* TREEdeleteData(Node* root, const int data) 
{
    Node *pr;
	Node *p; 
	Node *q; 
	Node *s;
    pr = NULL; 
	p = root;
    while (p!=NULL && p->data!=data )
	{
		pr = p;
		if (data < p->data)
		{
			p = p->l;
		} 
		else 
		{
			p = p->r;
		}
    }
    if (p != NULL) 
	{	
		if (p->l == NULL) 
		{ 
			if ( pr == NULL)
			{
				root = p->r;
			} 
			else if (pr->l == p)
			{ 
				pr->l = p->r;
			} 
			else
			{
				pr->r = p->r;
			}
			free(p);
		} 
		else
		{
			q = p; 
			s = p->l;
			while (s->r !=NULL) 
			{
				q = s; 
				s = s->r;
			}
			if (q == p)
			{
				q->l = s->l;
			}
			else 
			{
				q->r = s->l;
			}
			p->data = s->data; 
			free(s);
		}
    }
    return root;
}
