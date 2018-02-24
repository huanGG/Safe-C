int m = 100;
typedef int array[100];
array a;

/*@
lemma property1: \forall array b. \forall integer value. \forall integer k.
    ((\forall integer n:[0..m-2].b[n] < b[n+1]) && value > b[k] && 0 <= k < m ==> 
    	(\forall integer n:[0..k].value > b[n]));
lemma property2: \forall array b. \forall integer value. \forall integer k.
    ((\forall integer n:[0..m-2].b[n] < b[n+1]) && value < b[k] && 0 <= k < m ==> 
    	(\forall integer n:[k..m-1].value < b[n]));
*/
/*@
requires m == 100 && (\forall integer n:[0.. m-2]. a[n] < a[n+1]);
ensures	m == 100 && -1 <= \result && \result <= m-1 &&
    (\result >= 0 && a[\result] == val || \result == -1 && (\forall integer n:[0.. m-1]. a[n] != val));
*/
int bsearch(int val){
    int i, j, k;
    i = 0;  j = m-1;
    /*@ loop invariant
	m == 100 && 0 <= i <= m && -1 <= j <= m-1 && (\forall integer n:[0..m-2].a[n] < a[n+1]) &&
	    (j-i >= -1 && (\forall integer n:[j+1..m-1]. val < a[n]) && (\forall integer n:[0..i-1]. val > a[n]) ||
	    j-i == -2 && k == i-1 && val == a[k]);
    */
    while(i <= j) {
	k = i + (j - i)/2;
	if(val <= a[k]) j = k - 1;
	if(val >= a[k]) i = k + 1;
    }
    if(j - i == -1) k = -1;
    return k;
}

