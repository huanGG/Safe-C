// 库函数strcpy(char* dest, const char* src)的验证
// 这个协议适用于dest和src指向不同的数据块

//@ logic char *olddest, *oldsrc; logic integer m;
/*@ requires \is_pstring(src, m) && \length(dest) - \offset(dest) > m && olddest == dest && oldsrc == src;
    ensures \result == olddest && \is_pstring(\result, m) && \is_pstring(oldsrc, m) && 
		\string(\result, m) == \string(oldsrc, m);
*/
char* strcpy(char* dest, const char* src){
    char* p;
    //@ ghost int n;
    p = dest;
    *dest = *src;
    //@ ghost n = 0;
    /*@ loop invariant
	    0 <= n <= m && dest == olddest+n && src == oldsrc+n && p == olddest &&
	    \string(olddest, n) == \string(oldsrc, n) &&
	    \is_pstring(oldsrc, m) && \length(olddest) - \offset(olddest) > m && *dest == *src;
    */
    while(*src != 0){
	dest = dest + 1;
	src = src + 1;
	*dest = *src;
	//@ ghost n = n + 1;
    }
    return p;
}

