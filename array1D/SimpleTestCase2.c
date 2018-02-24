// 几乎不会这么写程序，测试是否会把下标所在区间搞错。

#define LEN 100

int n;

/*@ 
requires \length(a) == LEN && LEN/4 <= n < LEN*3/4;
assigns a;
ensures (LEN/4 <= n < LEN/2 && (\forall integer i : [0..n-1]. a[i] == 10) && a[n] == 30 && (\forall integer i : [n+1..LEN/2-1]. a[i] == 10) && (\forall integer i : [LEN/2..LEN-1]. a[i] == 20)) ||
	(LEN/2 <= n < LEN*3/4 && (\forall integer i : [0..LEN/2-1]. a[i] == 10) && (\forall integer i : [LEN/2..n-1]. a[i] == 20) && a[n] == 30 && (\forall integer i : [n+1..LEN-1]. a[i] == 20));
*/
void test(long* const a) {
    int i;
    /*@ loop invariant \length(a) == LEN && 0 <= i <= LEN/2 && LEN/4 <= n < LEN*3/4 &&
	    (\forall integer k : [0..i-1]. a[k] == 10);
    */
    for(i=0; i < LEN/2; i = i+1) {
	a[i] = 10;
    }
    /*@ loop invariant \length(a) == LEN && LEN/2 <= i <= LEN && LEN/4 <= n < LEN*3/4 &&
	    (\forall integer k : [0..LEN/2-1]. a[k] == 10) &&
	    (\forall integer k : [LEN/2..i-1]. a[k] == 20);
    */
    for(i=LEN/2; i < LEN; i = i+1) {
	a[i] = 20;
    }
    a[n] = 30;
}

