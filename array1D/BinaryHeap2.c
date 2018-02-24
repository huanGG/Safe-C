// 用数组实现二叉堆（简化循环不变式）
// 因为没有main函数，element[0]的初值不好处理，所以不知道element[0]等于什么，但它一定是最小的。
// 删除函数没有把element[0]考虑在内

#define CAPACITY 10000
#define INT_MIN -2147483647

int size = 0;
//@ global invariant capacity : 0 <= size <= CAPACITY;
int elements[CAPACITY+1];


/*@
requires size >= 0 &&  size <= CAPACITY-1 &&
    (\forall integer j:[1..size].elements[j] >= elements[j/2]) &&  x > INT_MIN;
assigns elements;
ensures size > 0 &&  size <= CAPACITY && (\forall integer j:[1..size].elements[j] >= elements[j/2]);
*/
void insert(int x) {
    int i,t;
    size = size + 1; i = size; t = i / 2;
    /*@ loop invariant	size > 0 &&  size <= CAPACITY &&  i == size &&  t == i/2 && 
	(\forall integer j:[1..size-1].elements[j] >= elements[j/2]) ||
	size > 0 &&  size <= CAPACITY &&  i <= size/2 &&  i >= 0 &&  t == i/2 &&  elements[i] > x && 
	    (\forall integer j:[1..size].elements[j] >= elements[j/2]);
    */
    while (elements[t] > x) {
	elements[i] = elements[t]; i = i / 2; t = i / 2;
    }
    elements[i] = x;
}

/*@
requires size > 0 &&  size <= CAPACITY &&  (\forall integer j:[1..size].elements[j] >= elements[j/2]);
assigns elements;
ensures size >=0 &&  size <= CAPACITY-1 &&  (\forall integer j:[1..size].elements[j] >= elements[j/2]);
*/
int delete(){	/* 删除最小值elements[1] */
    int i, child;
    int lastElement, minElement;
    minElement = elements[1]; lastElement = elements[size]; size = size -1;
    if (size > 0) {
	i = 1; child = i * 2;
	if (child < size && elements[child +1] < elements[child]) {
	    child = child + 1;
	}
	/*@ loop invariant
	    size > 0 && size <= CAPACITY-1 && i > 0 && i <= size && child == i*2 && child < size && 
		elements[child] <= elements[child+1] &&
		(\forall integer j:[1..size].elements[j] >= elements[j/2]) && lastElement >= elements[i] ||
	    size > 0 && size <= CAPACITY-1 && i > 0 && i <= size && child == i*2+1 && child <= size && 
		elements[child-1] > elements[child] &&
		(\forall integer j:[1..size].elements[j] >= elements[j/2]) && lastElement >= elements[i] ||  
	    size > 0 && size <= CAPACITY-1 && i > 0 && i <= size && child == i*2 &&  child >= size && 
		(\forall integer j:[1..size].elements[j] >= elements[j/2]) &&  lastElement >= elements[i];
	*/
	while (child <= size && lastElement > elements[child]) {
	    elements[i] = elements[child]; i = child; child = i * 2;
	    if (child < size && elements[child +1] < elements[child]) {
		child = child + 1;
	    }
	}
	elements[i] = lastElement;
    }
    return minElement;
}

