// 从s1的第一个字符向后检索，直到'\0'，如果当前字符存在于s2中，那么返回当前字符的地址，并停止检索。找不到返回NULL。

//@ logic integer m, n; logic char *olds1, *olds2;
/*@ requires olds1 == s1 && olds2 == s2 && \is_pstring(s1, m) && \is_pstring(s2, n);
    ensures \is_pstring(olds1, m) && \is_pstring(olds2, n) &&
	(\result == \null && (\forall integer i:[0..m-1]. !\membership(\string(olds2, n), olds1[i])) ||
	0 <= \result - olds1 <= m && (\forall integer i:[0..\result-olds1-1]. !\membership(\string(olds2, n), olds1[i])) &&
	\membership(\string(olds2, n), olds1[\result - olds1]));
*/
char* strpbrk1(const char* s1, const char* s2){
    const char *c1 = s1;
    const char *c2 = s2;
    //@ ghost int m1, n1;

    if(*c1 == 0){
	return (char*) 0;
    }
    //@ ghost m1 = 0; n1 = 0;

    /*@ loop invariant
	s1 == olds1 && s2 == olds2 && \is_pstring(s1, m) && \is_pstring(s2, n) &&
	    c1 == s1 + m1 && 0 <= m1 <= m && m > 0 && c2 == s2 + n1 && 0 <= n1 <= n && *c1 != 0 &&
            (\forall integer i:[0..m1-1].!\membership(\string(s2, n), s1[i])) ||
	s1 == olds1 && s2 == olds2 && \is_pstring(s1, m) && \is_pstring(s2, n) &&
	    c1 == s1 + m1 && m1 == m && m > 0 && c2 == s2 + n1 && n1 == n && *c1 == 0 && *c2 == 0 &&
            (\forall integer i:[0..m1-1].!\membership(\string(s2, n), s1[i]))    ;
    */
    while (*c1 != 0) {
	//@ ghost n1 = 0;
    
	/*@ loop invariant s1 == olds1 && s2 == olds2 && \is_pstring(s1, m) && \is_pstring(s2, n) &&
		c1 == s1 + m1 && 0 <= m1 <= m && m > 0 && c2 == s2 + n1 && 0 <= n1 <= n &&
	        (\forall integer i:[0..m1-1]. !\membership(\string(s2, n), s1[i])) &&
		!\membership(\string(s2, n1), s1[m1]);
	*/
        for(c2 = s2; *c2 != 0; c2 = c2+1) {
            if (*c1 == *c2) break;
	    //@ ghost n1 = n1 + 1;
        }
        if (*c1 == *c2) {
	    break;
	} else {
            c1 = c1+1;
	    //@ ghost m1 = m1 + 1;
	}
    }
    if(*c2 == 0){
	c1 = 0;
    }
    return (char *) c1;
}



