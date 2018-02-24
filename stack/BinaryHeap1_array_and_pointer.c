// elements原来是一个全局数组，现在改成全局指针加偏移的方式，但有些保留了下标变量的形式。
#define CAPACITY 10000

int size = 0;
//@ global invariant capacity : 0 <= size <= CAPACITY;
int* elements;



/*@ requires size >= 0 &&  size <= CAPACITY-1 && \length(elements) == CAPACITY + 1 &&
        (\forall integer j:[2..size].elements[j] >= elements[j/2]) && x > -2147483647;
    assigns elements;
    ensures size > 0 &&  size <= CAPACITY && \length(elements) == CAPACITY + 1 &&
        (\forall integer j:[2..size].*(elements + j) >= *(elements + j/2));
*/
void insert(int x) {
    int i, t;
    size = size + 1; i = size; t = i / 2;
    /*@ loop invariant
	    size > 0 &&  size <= CAPACITY &&  i == size &&  t == i/2 && \length(elements) == CAPACITY + 1 &&
		    (\forall integer j:[2..size-1].elements[j] >= elements[j/2]) ||
	    size > 0 && size <= CAPACITY && i <= size/2 && i >= 0 && t == i/2 && *(elements + i) > x && \length(elements) == CAPACITY + 1 &&
		    (\forall integer j:[2..size].*(elements + j) >= *(elements + j/2));
    */
    while (*(elements + t) > x) {
	*(elements + i) = *(elements + t); i = i / 2; t = i / 2;
    }
    *(elements + i) = x;
}




/*@ requires size > 0 && size <= CAPACITY && \length(elements) == CAPACITY + 1 &&
        (\forall integer j:[2..size].*(elements + j) >= *(elements + j/2));
    assigns elements;
    ensures size >=0 && size <= CAPACITY-1 && \length(elements) == CAPACITY + 1 &&
	(\forall integer j:[2..size].elements[j] >= elements[j/2]);
*/
int delete(){	/* 删除最小值lements[1] */
    int i, child;
    int lastElement, minElement;
    minElement = *(elements + 1); lastElement = *(elements + size); size = size -1;
    if (size > 0) {
	i = 1; child = i * 2;
	if (child < size && *(elements + (child +1)) < *(elements + child)) {
	    child = child + 1;
	}
	/*@ loop invariant
	    size > 0 && size <= CAPACITY-1 && i > 0 && i <= size && child == i*2 && child < size && 
		\length(elements) == CAPACITY + 1 && *(elements + child) <= *(elements + (child+1)) &&
		(\forall integer j:[2..size].elements[j] >= elements[j/2]) && lastElement >= elements[i] ||
	    size > 0 && size <= CAPACITY-1 && i > 0 && i <= size && child == i*2+1 && child <= size && 
		*(elements + (child-1)) > *(elements + child) && \length(elements) == CAPACITY + 1 &&
		(\forall integer j:[2..size].elements[j] >= elements[j/2]) && lastElement >= elements[i] ||  
	    size > 0 && size <= CAPACITY-1 && i > 0 && i <= size && child == i*2 &&  child >= size && \length(elements) == CAPACITY + 1 &&
		(\forall integer j:[2..size].*(elements + j) >= *(elements + j/2)) &&  lastElement >= *(elements + i);
	*/
	while (child <= size && lastElement > *(elements + child)) {
	    *(elements + i) = *(elements + child); i = child; child = i * 2;
	    if (child < size && *(elements + child + 1) < *(elements + child)) {
		child = child + 1;
	    }
	}
	*(elements + i) = lastElement;
    }
    return minElement;
}
