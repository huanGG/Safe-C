const int m = 10;  // 在数组较小时，没有引理也可以证明，否则见binsearch_lemma.c
int a[10];

/*@
requires m == 10 && (\forall integer n:[0.. m-2]. a[n] < a[n+1]);
ensures	m == 10 && -1 <= \result && \result <= m-1 &&
    (\result >= 0 && a[\result] == val || \result == -1 && (\forall integer n:[0.. m-1]. a[n] != val));
*/
int bsearch(int const val){
    int i, j, k;
    i = 0;  j = m-1;
    /*@ loop invariant
	m == 10 && 0 <= i <= m && -1 <= j <= m-1 && (\forall integer n:[0..m-2].a[n] < a[n+1]) &&
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

