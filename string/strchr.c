//@ logic integer n, oldch; logic char *oldsrc;
/*@ requires \is_pstring(src, n) && 0 <= ch <= 255 && oldch == ch && oldsrc == src;
    ensures \is_pstring(oldsrc, n) && \result == \null && !\membership(\string(oldsrc, n), oldch) ||
	\is_pstring(oldsrc, n) && 0 <= \offset(\result)-\offset(oldsrc) < n && *(\result) == oldch && 
	\result == oldsrc + \offset(\result) - \offset(oldsrc) &&  // 需要这个断言，表明\result和oldsrc指向同一个数据块
	!\membership(\prefix(\string(oldsrc, n), \offset(\result) - \offset(oldsrc)), oldch);
*/
char* strchr1(const char* src, int ch) {
    int m;

    m = 0;
    /*@ loop invariant \is_pstring(oldsrc, n) && 0 <= m <= n && src == oldsrc + m && 0 <= ch <= 255 && oldch == ch &&
			  !\membership(\prefix(\string(oldsrc,n), \offset(oldsrc+m) - \offset(oldsrc)), ch);
    */
    while(*src != 0){
	if(*src == ch) {
	    return (char *)src;
	}
	src = src+1;
	m = m+1;
    }
    return 0;
}

