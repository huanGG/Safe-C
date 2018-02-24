// 库函数strcpy(char* dest, const char* src)的验证
// 为了测试指针的指针，改成strcpy(char** dest, const char** src)，导致对协议有较多改动，对代码也略有改动
// 这个协议适用于*dest和*src指向不同的数据块

//@ logic integer m;		
/*@ requires \is_pstring(*src_ptr, m) && \length(*dest_ptr) - \offset(*dest_ptr) > m ;
    ensures \result == dest_ptr && \is_pstring(*\result, m) && \is_pstring(*src_ptr, m) && 
		\string(*\result, m) == \string(*src_ptr, m);
*/
const char** strcpy_ptr(const char** dest_ptr, const char** src_ptr){		    
    char *dest, *src;			    
    //@ ghost int n;
    dest = *dest_ptr; 
    src = *src_ptr;	    

    *dest = *src;
    //@ ghost n = 0;
    /*@ loop invariant
	    0 <= n <= m && dest == *dest_ptr+n && src == *src_ptr+n &&		
	    \string(*dest_ptr, n) == \string(*src_ptr, n) &&
	    \is_pstring(*src_ptr, m) && \length(*dest_ptr) - \offset(*dest_ptr) > m && *dest == *src;
    */
    while(*src != 0){
	dest = dest + 1;
	src = src + 1;
	*dest = *src;
	//@ ghost n = n + 1;
    }
    return dest_ptr;			    
}

