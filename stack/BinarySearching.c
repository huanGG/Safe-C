// ���ֲ��ҡ����ļ��ļ����������Ǹ���ָ�������ʵ�ֵġ�
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


//�β���ָ�����ͣ�����Ͷ�������Ȼ�ǰ������������
/*@ requires m == CAPACITY && \length(a) == m && (\forall integer i:[0.. m-2]. a[i] < a[i+1]);
    ensures m == CAPACITY && \length(a) == m && -1 <= \result && \result <= m-1 &&
    	(\result >= 0 && *(a + \result) == val || \result == -1 && (\forall integer i:[0.. m-1]. a[i] != val));
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



//�β���ָ�����ͣ�����Ͷ�������Ȼ�������ǰ������������
/*@ requires m == CAPACITY && \length(a) == m && (\forall integer i:[0.. m-2]. *(a + i) < *(a + (i+1)));
    ensures m == CAPACITY && \length(a) == m && -1 <= \result && \result <= m-1 &&
    	(\result >= 0 && *(a + \result) == val || \result == -1 && (\forall integer i:[0.. m-1]. a[i] != val));
*/
int bsearch2(int* a, int const val){
    int n, j, k;
    n = 0;  j = m-1;
    /*@ loop invariant
	 m == CAPACITY && \length(a) == m && 0 <= n <= m && -1 <= j <= m-1 && (\forall integer i:[0..m-2]. *(a+i) < *(a + (i+1))) &&
	    (j-n >= -1 && (\forall integer i:[j+1..m-1]. val < *(a+i)) && (\forall integer i:[0..n-1]. val > *(a+i)) ||
	    j-n == -2 && k == n-1 && val == a[k]);
    */
    while(n <= j) {
	k = n + (j - n)/2;
	if(val <= *(a+k)) j = k - 1;
	if(val >= a[k]) n = k + 1;
    }
    if(j - n == -1) k = -1;
    return k;
}


//�β���ָ�����ͣ�����Ͷ�����ȫ������ָ�������
/*@ requires m == CAPACITY && \length(a) == m && (\forall integer i:[0.. m-2]. *(a + i) < *(a + (i+1)));
    ensures m == CAPACITY && \length(a) == m && -1 <= \result && \result <= m-1 &&
    	(\result >= 0 && *(a + \result) == val || \result == -1 && (\forall integer i:[0.. m-1]. *(a+i) != val));
*/
int bsearch3(int* a, int const val){
    int n, j, k;
    n = 0;  j = m-1;
    /*@ loop invariant
	 m == CAPACITY && \length(a) == m && 0 <= n <= m && -1 <= j <= m-1 && (\forall integer i:[0..m-2]. *(a+i) < *(a + (i+1))) &&
	    (j-n >= -1 && (\forall integer i:[j+1..m-1]. val < *(a+i)) && (\forall integer i:[0..n-1]. val > *(a+i)) ||
	    j-n == -2 && k == n-1 && val == *(a+k));
    */
    while(n <= j) {
	k = n + (j - n)/2;
	if(val <= *(a+k)) j = k - 1;
	if(val >= *(a+k)) n = k + 1;
    }
    if(j - n == -1) k = -1;
    return k;
}




/*@ requires m == CAPACITY && \length(a) == m && (\forall integer i:[0.. m-2]. a[i] < a[i+1]);
    ensures m == CAPACITY && \length(a) == m && -1 <= \result && \result <= m-1 &&
	(\result >= 0 && a[\result] == val || \result == -1 && (\forall integer i:[0.. m-1]. a[i] != val));
*/
//�β���δָ����С���������ͣ�����Ͷ�����ȫ���������������
int bsearch4(int a[], int const val){
    int n, j, k;
    n = 0;  j = m-1;
    /*@ loop invariant
	m == CAPACITY && \length(a) == m && 0 <= n <= m && -1 <= j <= m-1 && (\forall integer i:[0..m-2].a[i] < a[i+1]) &&
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



/*@ requires m == CAPACITY && \length(a) == m && (\forall integer i:[0.. m-2]. a[i] < a[i+1]);
    ensures m == CAPACITY && -1 <= \result && \result <= m-1 && \length(a) == m &&
	(\result >= 0 && a[\result] == val || \result == -1 && (\forall integer i:[0.. m-1]. a[i] != val));
*/
//�β����������ͣ�����Ͷ�����ȫ���������������
int bsearch5(int a[CAPACITY], int const val){
    int n, j, k;
    n = 0;  j = m-1;
    /*@ loop invariant
	m == CAPACITY && 0 <= n <= m && -1 <= j <= m-1 && \length(a) == m && (\forall integer i:[0..m-2].a[i] < a[i+1]) &&
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



/*@ requires m == CAPACITY && \length(a) == m && (\forall integer i:[0.. m-2]. a[i] < a[i+1]);
    ensures m == CAPACITY && -1 <= \result && \result <= m-1 && \length(a) == m && 
	(\result >= 0 && a[\result] == val || \result == -1 && (\forall integer i:[0.. m-1]. a[i] != val));
*/
//�β����������ͣ�����Ͷ�������������ָ�������
int bsearch6(int a[CAPACITY], int const val){
    int n, j, k;
    n = 0;  j = m-1;
    /*@ loop invariant
	m == CAPACITY && 0 <= n <= m && -1 <= j <= m-1 && \length(a) == m && (\forall integer i:[0..m-2].a[i] < a[i+1]) &&
	    (j-n >= -1 && (\forall integer i:[j+1..m-1]. val < a[i]) && (\forall integer i:[0..n-1]. val > a[i]) ||
	    j-n == -2 && k == n-1 && val == *(a+k));
    */
    while(n <= j) {
	k = n + (j - n)/2;
	if(val <= a[k]) j = k - 1;
	if(val >= *(a+k)) n = k + 1;
    }
    if(j - n == -1) k = -1;
    return k;
}



