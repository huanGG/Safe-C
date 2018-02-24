//@ logic char *oldstr;
/*@ requires \is_pstring(str) && oldstr == str;
    ensures \is_pstring(oldstr, \result);
*/
int strlen1(const char *str) {
    int m;

    m = 0;
    /*@ loop invariant (\exists integer n.\is_pstring(str, n) && 0 <= m <= n) && \is_string(str, m) &&
		str == oldstr;
	// loop variant \length(str) - \offset(str) - m;
    */
    while(str[m] != '\0') {
	m = m + 1;
    }
    return m;
}

