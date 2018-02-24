#define CAPACITY 10000
int m = CAPACITY;

/*@
lemma property1: \forall int b[CAPACITY]. \forall integer value. \forall integer k.
    ((\forall integer n:[0..CAPACITY-2].b[n] < b[n+1]) && value > b[k] && 0 <= k < CAPACITY ==> 
    	(\forall integer n:[0..k].value > b[n]));
lemma property2: \forall int b[CAPACITY]. \forall integer value. \forall integer k.
    ((\forall integer n:[0..CAPACITY-2].b[n] < b[n+1]) && value < b[k] && 0 <= k < CAPACITY ==> 
    	(\forall integer n:[k..CAPACITY-1].value < b[n]));
*/



/*@ requires m == CAPACITY && \length(a) == m && (\forall integer i:[0.. m-2]. a[i] < a[i+1]);
    ensures m == CAPACITY && \length(a) == m && -1 <= \result && \result <= m-1 &&
    	(\result >= 0 && a[\result] == val || \result == -1 && (\forall integer i:[0.. m-1]. a[i] != val));
*/
int bsearch1(int* a, int const val){
    int n, j, k;
    n = 0;  j = m-1;
    /*@ loop invariant
	 m == CAPACITY && \length(a) == m && 0 <= n <= m && -1 <= j <= m-1 && (\forall integer i:[0..m-2]. a[i] < a[i+1]) &&
	    (j-n >= -1 && (\forall integer i:[j+1..m-1]. val < a[i]) && (\forall integer i:[0..n-1]. val > a[i]) ||
	    j-n == -2 && k == n-1 && val == a[k]);
    */
    while(n <= j) {
	k = n + (j - n)/2;
	if(val <= a[k]) j = k - 1;
	if(val >= a[k]) n = k + 1;
    }
    if(j - n == -1) k = -1;
    return k;
}




// 与上一个函数的区别仅在于用形参而不是全局变量表示数组的长度
/*@ requires mm == CAPACITY && \length(a) == mm && (\forall integer i:[0.. mm-2]. a[i] < a[i+1]);
    ensures mm == CAPACITY && \length(a) == mm && -1 <= \result && \result <= mm-1 &&
    	(\result >= 0 && a[\result] == val || \result == -1 && (\forall integer i:[0.. mm-1].  a[i] != val));
*/
int bsearch8(int* a, int const mm, int const val){
    int n, j, k;
    n = 0;  j = mm-1;
    /*@ loop invariant
	 mm == CAPACITY && \length(a) == mm && 0 <= n <= mm && -1 <= j <= mm-1 && (\forall integer i:[0..mm-2]. a[i] < a[i+1]) &&
	    (j-n >= -1 && (\forall integer i:[j+1..mm-1]. val < a[i]) && (\forall integer i:[0..n-1]. val > a[i]) ||
	    j-n == -2 && k == n-1 && val == a[k]);
    */
    while(n <= j) {
	k = n + (j - n)/2;
	if(val <= a[k]) j = k - 1;
	if(val >= a[k]) n = k + 1;
    }
    if(j - n == -1) k = -1;
    return k;
}




