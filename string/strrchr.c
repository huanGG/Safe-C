// ����ĳ�ַ����ַ��������һ�γ��ֵ�λ��
// ����ҵ��ͷ��ظ��ַ����һ�γ��ֵ�λ�ã����򷵻� NULL

enum bool1 {false1, true1};

//@ logic integer n, oldch; logic char *oldsrc;
/*@ requires \is_pstring(src, n) && 0 <= ch <=255 && oldch == ch && oldsrc == src;
    ensures \is_pstring(oldsrc, n) && \result == \null && !\membership(\string(oldsrc, n), oldch) ||
	\is_pstring(oldsrc, n) &&  0 <= \offset(\result)-\offset(oldsrc) < n && *(\result) == oldch &&
	\result == oldsrc + \offset(\result) - \offset(oldsrc) &&   // ��Ҫ������ԣ�����\result��oldsrcָ��ͬһ�����ݿ�
	!\membership(\suffix(\string(oldsrc, n), n - (\offset(\result) - \offset(oldsrc) +1)), oldch);
*/
char* strrchr1(const char* src, int ch){
    int m, k;
    enum bool1 exist;

    m = 0; k = 0; exist = false1;
    /*@ loop invariant \is_pstring(oldsrc, n) && 0 <= m <= n && 0 <= k <= m && src == oldsrc + m && oldch == ch &&
	(exist == false1 && !\membership(\string(oldsrc, m), ch) ||
	 exist == true1 && oldsrc[k] == ch && (\forall integer i:[k+1..m-1].oldsrc[i] != ch));
    */
    while(*src != 0) {
	if(*src == ch) {
		k = m; exist = true1;
	}
	src = src+1;
	m = m+1;
    }
    if (exist == false1) {
	return 0;
    }else {
	return (char *)(src + k);
    }
}

