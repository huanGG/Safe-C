struct MaxAndMin{
                  int max;
                  int min;
       };
       /*@ requires size > 0 && \length(a) == size;
           ensures \forall.integer i :[0..size-1].( a[i] <=\result.max && \result.min <=a[i]  ) ;
            */
       struct MaxAndMin findMaxAndMin(int* a,int size){
                   struct MaxAndMin s;
                   struct MaxAndMin* p = &s;
                   int** q = &a;
                   p->min = (*q)[0];
                   p->max = (*q)[0];
                  int i = 0;
                 /*@ loop invariant *p==s && *q==a && \length(a)==size && size >0 && 
					((i<size && \forall.integer j :[0..i].( a[j] <=s.max && s.min <=a[j]) || 
		i== size && \forall.integer j:[0..size-1].(a[j] <=s.max && s.min <=a[j]));
                 */
                while (i < size){
                           if (p->max < (*q)[i])
                                      p->max = (*q)[i];
                           if (p->min > (*q)[i])
                                      p->min = (*q) [i];
                           i = i + 1;
                 }
                 return s;
      }