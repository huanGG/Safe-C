// 用来计算字符串 str 中从第一个字符开始，连续有几个字符都属于字符串 accept。

//@ logic integer m, n; logic char *oldstr, *oldaccept;
/*@ requires \is_pstring(str, m) && \is_pstring(accept, n) && oldstr == str && oldaccept == accept;
    ensures \is_pstring(oldstr, m) && \is_pstring(oldaccept, n) &&
        (\forall integer i:[0..\result-1]. \membership(\string(oldaccept, n), oldstr[i])) &&
        (0 <= \result < m && !\membership(\string(oldaccept, n), oldstr[\result]) || \result == m);
*/
unsigned int strspn(const char* str, const char* accept){
    const char* p;
    const char* s;
    int count = 0;
    //@ ghost int k;
    /*@ loop invariant \is_pstring(str, m) && \is_pstring(accept, n) && 0 <= count <= m &&
	    str == oldstr && accept == oldaccept && p == str + count &&
            (\forall integer i:[0..count-1]. \membership(\string(accept, n), str[i]));
    */
    for(p = str; *p != '\0'; p = p+1){
	//@ ghost k = 0;
    	/*@ loop invariant \is_pstring(str, m) && \is_pstring(accept, n) && 0 <= count < m &&
		str == oldstr && accept == oldaccept && p == str + count && s == accept + k &&
		(\forall integer i:[0..count-1]. \membership(\string(accept, n), str[i])) &&
		!\membership(\string(accept, k), str[count]) && 0 <= k <= n;
        */	    
        for(s = accept; *s != '\0'; s = s+1){
            if(*p == *s){
                break;
            }
	    //@ ghost k = k + 1;
        }
        if(*s == '\0'){
            return count;
        }
        count = count + 1;
    }
    return count;
}

