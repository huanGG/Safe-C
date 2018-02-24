// 用来计算字符串str中连续有几个字符都不属于字符串substr
// 返回字符串str开头连续不属于字符串substr的字符数

//@ logic integer m, n; logic char *oldstr, *oldsubstr;
/*@ requires \is_pstring(str, m) && \is_pstring(substr, n) && oldstr == str && oldsubstr == substr;
    ensures \is_pstring(oldstr, m) && \is_pstring(oldsubstr, n) &&
        (\forall integer i:[0..\result-1].!\membership(\string(oldsubstr, n), oldstr[i])) &&
        (0 <= \result < m && \membership(\string(oldsubstr, n), oldstr[\result]) || \result == m);
*/
unsigned int strcspn1(const char* str, const char* substr){
    const char* p;
    const char* s;
    int count = 0;
    //@ ghost int k;
    /*@ loop invariant \is_pstring(str, m) && \is_pstring(substr, n) && 0 <= count <= m &&
            (\forall integer i:[0..count-1]. !\membership(\string(substr, n), str[i])) &&
	    str == oldstr && substr == oldsubstr && p == str+count ;
    */
    for(p = str; *p != '\0'; p = p+1){
        /*@ loop invariant \is_pstring(str, m) && \is_pstring(substr, n) && 0 <= count < m &&
            (\forall integer i:[0..count-1]. !\membership(\string(substr, n), str[i])) &&
            (\forall integer i:[0..k-1]. substr[i]!= str[count]) && 0 <= k <= n &&
	    str == oldstr && substr == oldsubstr && p == str+count && s == substr+k;
        */
        //@ ghost k = 0;	    
        for(s = substr; *s != '\0'; s = s+1){
            if(*p == *s){
                return count;
            }
	    //@ ghost k = k + 1;
        }
        count = count+1;
    }
    return count;
}

