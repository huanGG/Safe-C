
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

//@ logic Node* oldp;
/*@
requires p != \null && oldp == p;
ensures \dangling(oldp) || oldp == \result;
*/
Node * TREEdelete(Node *p) 
{
    Node *q;
	Node *s;
    q = p;
    if(p->r==NULL)
	{
		p = p->l;
		free(q);
    }
	else if(p->l==NULL)
	{
		p = p->r;
		free(q);
    }
	else
	{
		s = p->l;
		if(s->r == NULL)
		{
			p->l = s->l;
			p->data = s->data;
			free(s);
		}
		else
		{
			q = s;
			s = s->r;
			while(s->r != NULL)
			{
				q = s;
				s = s->r;
			}
			p->data = s->data;
			q->r = s->l;
			free(s);
		}
    }
    return p;
}