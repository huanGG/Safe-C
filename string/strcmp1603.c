// 库函数strcmp(char* str1, char* str2)的验证

//@ logic char *p1, *p2; logic integer m, n;
/*@ requires \is_pstring(str1, m) && \is_pstring(str2, n) && p1 == str1 && p2 == str2;
    ensures  \is_pstring(p1, m) && \is_pstring(p2, n) &&
		(\string(p1, m) < \string(p2, n) && \result < 0 ||
		\string(p1, m) == \string(p2, n) && \result == 0 ||
		\string(p1, m) > \string(p2, n) && \result > 0);
*/
int strcmp(const char* str1,const char* str2) {
    //@ ghost int k;

    //@ ghost k = 0; 
    /*@ loop invariant k >= 0 &&  str1 == p1 + k && str2 == p2 + k && \is_pstring(p1, m) && \is_pstring(p2, n) &&
		    (\forall integer i:[0..k-1]. p1[i] == p2[i]) && k <= m && k <= n;
    */
    while(*str1 == *str2){
		if(*str1 == '\0') {
			return 0;
		}
		str1 = str1+1;
		str2 = str2+1;
		//@ ghost k = k+1;
    }
    return *str1 - *str2;
} 




// 库函数strncmp(char* str1, char* str2)的验证，约束在n小于等于两个字符串的长度。
//@ logic char *p1, *p2; logic integer m, k, oldn;
/*@ requires \is_pstring(str1, m) && \is_pstring(str2, k) &&
	p1 == str1 && p2 == str2 && oldn == n && m >= n && k >= n && n >= 0;
    ensures \is_pstring(p1, m) && \is_string(p2, k) &&
	(\prefix(\string(p1, m), oldn) < \prefix(\string(p2, k), oldn) && \result < 0 ||
	 \prefix(\string(p1, m), oldn) == \prefix(\string(p2, k), oldn) && \result == 0 ||
	 \prefix(\string(p1, m), oldn) > \prefix(\string(p2, k), oldn) && \result > 0);
*/
int strncmp_restricted(const char* str1,const char* str2, unsigned int n) {
    int j;

    j = 0; 
    /*@ loop invariant
	    oldn == n && n >= 0 && j >= 0 && str1 == p1 + j && str2 == p2 + j && \is_pstring(p1, m) && \is_pstring(p2, k) && 
		j <= n && (\forall integer i:[0..j-1]. p1[i] == p2[i]);
    */
	   
    while(j < n && *str1 == *str2){
		if(*str1 == '\0'){
			return 0;
		}
		str1 = str1 + 1;
		str2 = str2 + 1;
		j = j + 1;
    }
    if(n == 0 || j == n){
		return 0;
    } else {
		return *str1 - *str2;
    }
} 


// 库函数strncmp(char* str1, char* str2)的验证，函数协议与对strncmp的非形式描述一致
//@ logic char *p1, *p2; logic integer m, k, oldn;
/*@ requires \is_pstring(str1, m) && \is_pstring(str2, k) &&
	p1 == str1 && p2 == str2 && oldn == n && n >= 0;
    ensures \is_pstring(p1, m) && \is_string(p2, k) &&
	(\result < 0 && 
	    (m >= oldn && k >= oldn && \prefix(\string(p1, m), oldn) < \prefix(\string(p2, k), oldn) ||
	    (m < oldn || k < oldn) && \string(p1, m) < \string(p2, k)) ||
	 \result == 0 &&
	    (m >= oldn && k >= oldn && \prefix(\string(p1, m), oldn) == \prefix(\string(p2, k), oldn) ||
	    (m < oldn || k < oldn) && \string(p1, m) == \string(p2, k)) ||
	 \result > 0 &&
	    (m >= oldn && k >= oldn && \prefix(\string(p1, m), oldn) > \prefix(\string(p2, k), oldn) ||
	    (m < oldn || k < oldn) && \string(p1, m) > \string(p2, k)));
*/
int strncmp(const char* str1,const char* str2, unsigned int n) {
    int j;

    j = 0; 
    /*@ loop invariant
	    oldn == n && n >= 0 && j >= 0 && str1 == p1 + j && str2 == p2 + j && \is_pstring(p1, m) && \is_pstring(p2, k) && 
		j <= n && (\forall integer i:[0..j-1]. p1[i] == p2[i]);
    */
	   
    while(j < n && *str1 == *str2){
		if(*str1 == '\0'){
			return 0;
		}
		str1 = str1 + 1;
		str2 = str2 + 1;
		j = j + 1;
    }
    if(n == 0 || j == n){
		return 0;
    } else {
		return *str1 - *str2;
    }
} 

