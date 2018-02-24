// 库函数strncpy(char* dest, const char* src, size_t n)的验证
// 这个协议适用于dest和src指向不同的数据块

//@ logic char *olddest, *oldsrc; logic integer m, oldn;
/*@ requires \is_pstring(src, m) && \length(dest) - \offset(dest) > n && 0 <= n <= m &&
	olddest == dest && oldsrc == src && oldn == n;
    ensures \result == olddest && \is_pstring(\result, oldn) && \is_pstring(oldsrc, m) && 
	\string(\result, oldn) == \string(oldsrc, oldn);
*/
char* strncpy(char* dest, const char* src, unsigned int n){
    char* p;
    int n1;
    p = dest;
    *dest = *src;
    n1 = 0;
    /*@ loop invariant 0 <= n1 <= n <= m && dest == olddest + n1 && p == olddest &&
		src == oldsrc + n1  && \string(olddest, n1) == \string(oldsrc, n1) &&
		\is_pstring(oldsrc, m) && \length(olddest) - \offset(olddest) > n && *dest == *src && oldn == n;
    */
    while(n1 < n && *src != 0){
	dest = dest + 1;
	src = src + 1;
	*dest = *src;
	n1 = n1 + 1;
    }
    if(*dest != '\0') {
	*dest = '\0';
    }
    return p;
}


