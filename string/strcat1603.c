// 库函数strcat(char* dest, char* src)的验证

//@ logic integer m, n; logic char *olddest, *oldsrc;
/*@ requires \is_pstring(dest, m) && \is_pstring(src, n) && m + n < \length(dest) - \offset(dest) &&
		\old(\string(dest, m)) == \string(dest, m) && olddest == dest && oldsrc == src;
    ensures  \is_pstring(\result, m+n) && \is_pstring(oldsrc, n) && \result == olddest &&
		\old(\string(olddest, m)) == \string(olddest, m) &&
		\string(\result, m+n) == \old(\string(olddest, m)) + \string(oldsrc, n);
*/
char* strcat(char* dest, const char* src) {
    char* cp = dest;
    //@ ghost int m1, n1;

    //@ ghost m1 = 0;
    /*@	loop invariant 0 <= m1 <= m && cp == dest + m1 && (*cp == '\0' ==> m == m1) &&
		\is_pstring(dest, m) && \is_pstring(src, n) && m + n < \length(dest) - \offset(dest) &&
		\old(\string(dest, m)) == \string(dest, m) && dest == olddest && src == oldsrc;
    */
    while(*cp != '\0') {
	cp = cp+1;
	//@ ghost m1 = m1 + 1;
    }
    *cp = *src;
    //@ ghost n1 = 0;
    /*@ loop invariant 0 <= n1 <= n && cp == dest + m + n1 && *cp == *src && (*cp == '\0' ==> n == n1) &&
		\is_string(dest, m+n1) && \string(dest, m+n1) == \string(dest, m) + \string(oldsrc, n1) &&
		\is_pstring(oldsrc, n) && m + n < \length(dest) - \offset(dest) &&
		\old(\string(dest, m)) == \string(dest, m) && dest == olddest && src == oldsrc + n1;
    */	
    while(*cp != '\0') {
	//@ ghost n1 = n1 + 1;
    	cp = cp+1; src = src+1;
	*cp = *src;
    }
    return dest;
}

