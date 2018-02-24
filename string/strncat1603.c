// 库函数strncat(char* dest, char* src, size_t n)的验证

//@ logic integer m, k, oldn; logic char *oldsrc, *olddest;
/*@ requires \is_pstring(dest, m) && \is_pstring(src, k) && 0 <= n <= k &&
		m + n < \length(dest) - \offset(dest) && \old(\string(dest, m)) == \string(dest, m) &&
		\old(\string(src, k)) == \string(src, k) && oldsrc == src && olddest == dest && oldn == n;
    ensures  \is_pstring(\result, m + oldn) && \is_pstring(oldsrc, k) && \result == olddest &&
		\old(\string(oldsrc, k)) == \string(oldsrc, k) && 0 <= oldn <= k && 
		\string(\result, m + oldn) == \old(\string(olddest, m)) + \old(\string(oldsrc, oldn));
*/
char* strncat(char* dest, const char* src, unsigned int n) {
    char* cp = dest;
    int n1;
    //@ ghost int m1;

    //@ ghost m1 = 0;
    /*@	loop invariant cp == olddest + m1 && 0 <= m1 <= m && 0 <= n <= k &&
		src == oldsrc && dest == olddest && n == oldn && (*cp == '\0' ==> m == m1) &&
		\is_pstring(dest, m) && \is_pstring(src, k) && m + n < \length(dest) - \offset(dest) &&
		\old(\string(dest, m)) == \string(dest, m) && \old(\string(oldsrc, k)) == \string(oldsrc, k);
    */
    while(*cp != '\0') {
	cp = cp+1;
	//@ ghost m1 = m1 + 1;
    }
    *cp = *src;
    n1 = 0;
    /*@ loop invariant cp == olddest + m + n1 && 0 <= n1 <= n && 0 <= n <= k && src == oldsrc + n1 &&
		*cp == *src && dest == olddest && n == oldn && 
		\is_string(olddest, m + n1) && \string(olddest, m + n1) == \string(olddest, m) + \string(oldsrc, n1) &&
		\is_pstring(oldsrc, k) && m + n < \length(olddest) - \offset(olddest) &&
		\old(\string(olddest, m)) == \string(olddest, m) && \old(\string(oldsrc, k)) == \string(oldsrc, k);
    */
    while(n1 < n && *cp != '\0') {
	n1 = n1 + 1;
    	cp = cp+1; src = src+1	;
	*cp = *src;
    }
    *cp = '\0';
    return dest;
}

