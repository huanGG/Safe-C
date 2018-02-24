// 在最后一个循环中有，数组a分成4个区间。测试对下标变量赋值时，是否会把该下标所在区间搞错。
// 常量LEN定义为大于等于0的任意整数（在机器允许取值的范围内）都可以。
#define LEN 100

/*@ 
requires \length(a) == LEN;
assigns a;
ensures (\forall integer i : [0..LEN-1]. a[i] == 10) && \length(a) == LEN;
*/
void test(long* const a) {
    int i;
    /*@ loop invariant \length(a) == LEN && 0 <= i <= LEN/4 &&
	    (\forall integer k : [0..i-1]. a[k] == 10);
    */
    for(i=0; i < LEN/4; i = i+1) {
	a[i] = 10;
    }
    /*@ loop invariant \length(a) == LEN && LEN/4 <= i <= LEN/2 &&
	    (\forall integer k : [0..LEN/4-1]. a[k] == 10) &&
	    (\forall integer k : [LEN/4..i-1]. a[k] == 5);
    */
    for(i=LEN/4; i < LEN/2; i = i+1) {
	a[i] = 5;
    }
    /*@ loop invariant \length(a) == LEN && LEN/2 <= i <= LEN*3/4 &&
	    (\forall integer k : [0..LEN/4-1]. a[k] == 10) &&
	    (\forall integer k : [LEN/4..LEN/2-1]. a[k] == 5) &&
	    (\forall integer k : [LEN/2..i-1]. a[k] == 15);
    */
    for(i=LEN/2; i < LEN*3/4; i = i+1) {
	a[i] = 15;
    }
    /*@ loop invariant \length(a) == LEN && LEN*3/4 <= i <= LEN &&
	    (\forall integer k : [0..LEN/4-1]. a[k] == 10) &&
	    (\forall integer k : [LEN/4..LEN/2-1]. a[k] == 5) &&
	    (\forall integer k : [LEN/2..LEN*3/4-1]. a[k] == 15) &&
	    (\forall integer k : [LEN*3/4..i-1]. a[k] == 10);
    */
    for(i=LEN*3/4; i < LEN; i = i+1) {
	a[i] = 10;
    }
    /*@ loop invariant \length(a) == LEN && LEN/4 <= i <= LEN*3/4 &&
	    (\forall integer k : [0..LEN/4-1]. a[k] == 10) &&
	    (\forall integer k : [LEN/4..i-1]. a[k] == 10) &&
	    (\forall integer k : [i..LEN/2-1]. a[k] == 5) &&
	    (i <= LEN/2 && (\forall integer k : [LEN/2..LEN*3/4-1]. a[k] == 15) ||
	    	i > LEN/2 && (\forall integer k : [LEN/2..i-1]. a[k] == 10) && (\forall integer k : [i..LEN*3/4-1]. a[k] == 15)) &&
	    (\forall integer k : [LEN*3/4..LEN-1]. a[k] == 10);
    */
    for(i=LEN/4; i < LEN*3/4; i = i+1) {
	if(i < LEN/2){
	    a[i] = a[i] + 5;
	} else {
	    a[i] = a[i] - 5;
	}
    }
}

