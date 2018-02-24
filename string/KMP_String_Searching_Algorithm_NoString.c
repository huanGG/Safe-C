//  用KMP算法实现字符串匹配搜索方法，见严蔚敏等的《数据结构（C语言版）》第四章P79-83。
//  该算法的实现主要包括两个方面：
//  1. 计算用于搜索的目标字符串的部分匹配表table
//  2. 在源字符串中匹配目标字符串
// 该程序可用于源字符串已静态给定（在main函数中），待搜索的目标字符串从命令行输入的场合。

//#include <stdio.h>
//#include <string.h>
//#include <stdlib.h>
#define TARGET_MAX_LENGTH 20		//设定目标字符串最大长度
#define MAX_MATCH 10			//最多记录MAX_MATCH个匹配
int kmp_table[TARGET_MAX_LENGTH + 1];	//为目标串建立的kmp表，kmp_table[0]废弃不用，是为了与书上的next表一致
int source_length, target_length;	//记住源串和目标串长度的变量
int match_position[MAX_MATCH];		//记录与目标串匹配的源串中的位置,只记录前MAX_MATCH个匹配


// 创建目标字符串的KMP表

/*@ requires \length(table) == TARGET_MAX_LENGTH+1 && \is_pstring(str,target_length) && 0 < target_length <= TARGET_MAX_LENGTH;
    ensures table[1] == 0 && \length(table) == TARGET_MAX_LENGTH+1 &&
	(\forall integer k:[2..target_length].1 <= table[k] < k) &&
	\forall integer k:[2..target_length]. \forall integer n:[1..table[k]-1].str[n-1] == str[k-table[k]+n-1];
*/
void Create_KMP_Table(char* const str, int* const table){
    int i, j;

    i = 1; table[1] = 0; j = 0;
    /*@ loop invariant
	j == 0 && 1 <= i <= target_length &&						    //条件语句的第一分支，迭代进入要满足的条件
	    j < i && table[1] == 0 && table[i] < i && \is_pstring(str,target_length) &&
	    \length(table) == TARGET_MAX_LENGTH+1 && 0 < target_length <= TARGET_MAX_LENGTH &&
	    (\forall integer k:[2..i].1 <= table[k] < k) && (\forall integer k:[2..i].\forall integer n:[1..table[k]-1].str[n-1] == str[k-table[k]+n-1]) ||

	1 <= j <= target_length - 1 && 2 <= i <= target_length && table[i] == j &&	    //条件语句的第二分支，迭代进入要满足的条件
	    j < i && table[1] == 0 && table[i] < i && \is_pstring(str,target_length) &&
	    \length(table) == TARGET_MAX_LENGTH+1 && 0 < target_length <= TARGET_MAX_LENGTH &&
	    (\forall integer k:[2..i].1 <= table[k] < k) && (\forall integer k:[2..i].\forall integer n:[1..table[k]-1].str[n-1] == str[k-table[k]+n-1]) ||

	1 <= j <= target_length - 1 && 2 < i <= target_length && table[i] == j &&	    //条件语句的第三分支，迭代进入要满足的条件 
	    j < i && table[1] == 0 && table[i] < i && \is_pstring(str,target_length) &&
	    \length(table) == TARGET_MAX_LENGTH+1 && 0 < target_length <= TARGET_MAX_LENGTH &&
	    (\forall integer k:[2..i].1 <= table[k] < k) && (\forall integer k:[2..i].\forall integer n:[1..table[k]-1].str[n-1] == str[k-table[k]+n-1]);
    */
    while (i < target_length) {
	if (j == 0){
	    i = i + 1; j = j + 1; table[i] = j;
	}else if(str[i-1] == str[j-1]){
	    i = i + 1; j = j + 1; table[i] = j;
	}else{
	    j = table[j]; table[i] = j; //table[i] = j是增加的，它使得三个分支的出口统一都有table[i]==j，循环不变式的情况减少，并免去了使用Z3证明不了的引理。
	}
    }
}


// 在源串sourceStr中搜索目标串targetStr,在kmp_table中记录目标串在源串中的位置信息,返回目标串的匹配数
/*@ requires \is_pstring(targetStr,target_length) && \is_pstring(sourceStr,source_length) &&
	0 < target_length <= TARGET_MAX_LENGTH && target_length <= source_length;
    assigns kmp_table;
    ensures (\forall integer i:[0..\result-1].\forall integer j:[1..target_length]. sourceStr[(match_position[i]-1)+j-1] == targetStr[j-1]);
*/
int Search_Keyword(char* const sourceStr, char* const targetStr){
    char *p, *q;	//p和q是两个参数串的扫描指针
    int count;	    	//记录扫描sourceStr过程中已经匹配的字节数
    int k;	    	//记录sourceStr中能与targetStr匹配的子串数
    //@ ghost char* tmp;
    //@ ghost int m;

/*@ lemma table_property:
    \forall integer old_count. 
	((\forall integer k:[2..target_length].1 <= kmp_table[k] < k) &&
	 (\forall integer k:[2..target_length].\forall integer n:[1..kmp_table[k]-1].targetStr[n-1] == targetStr[k-kmp_table[k]+n-1]) &&
	 (\forall integer j:[1..old_count].sourceStr[j-1+m- old_count] == targetStr[j-1]) &&
	 count == kmp_table[old_count + 1]-1 
    ==> 
	(\forall integer j:[1..count].sourceStr[j-1+m-count] == targetStr[j-1]));
*/
    
    Create_KMP_Table(targetStr, kmp_table); //创建目标串的KMP表
    p = sourceStr; k = 0; //@ ghost m = 0;
    /*@	loop invariant  \is_pstring(targetStr,target_length) && \is_pstring(sourceStr,source_length) && p == sourceStr + m &&
	    0 < target_length <= TARGET_MAX_LENGTH && target_length <= source_length &&
	    sourceStr <= p <= sourceStr + source_length && 0 <= k <= MAX_MATCH && kmp_table[1] == 0 &&
	    (\forall integer k:[2..target_length].1 <= kmp_table[k] < k) &&
	    (\forall integer k:[2..target_length].\forall integer n:[1..kmp_table[k]-1].targetStr[n-1] == targetStr[k-kmp_table[k]+n-1]) &&
	    (\forall integer i:[0..k-1].\forall integer j:[1..target_length]. sourceStr[(match_position[i]-1)+j-1] == targetStr[j-1]);
    */

    while(p < sourceStr + source_length){   //直至搜索到sourceStr的最后一个字符为止
	count = 0; q = targetStr;
	//@ ghost tmp = p;
    	    /*@ loop invariant  \is_pstring(targetStr,target_length) && \is_pstring(sourceStr,source_length) &&
		p == sourceStr + m && q == targetStr + count && tmp == p - count &&
		0 < target_length <= TARGET_MAX_LENGTH && target_length <= source_length &&
		sourceStr <= p <= sourceStr + source_length && 0 <= k <= MAX_MATCH && kmp_table[1] == 0 &&
		(\forall integer k:[2..target_length].1 <= kmp_table[k] < k) &&
		(\forall integer k:[2..target_length].\forall integer n:[1..kmp_table[k]-1].targetStr[n-1] == targetStr[k-kmp_table[k]+n-1]) &&
		(\forall integer i:[0..k-1].\forall integer j:[1..target_length]. sourceStr[(match_position[i]-1)+j-1] == targetStr[j-1]) &&
		0 <= count <= target_length && targetStr <= q <= targetStr + target_length &&
		sourceStr <= tmp <= sourceStr + source_length && \forall integer j:[1..count].tmp[j-1] == targetStr[j-1];	
	    */
        while(p < sourceStr + source_length && count < target_length){
            if(*q == *p){ //count表示已经有多少个字符相同了
                count = count + 1;
                p = p + 1; //@ ghost m = m + 1;
                q = q + 1;
            } else if (count == 0) {
		p = p + 1; //@ ghost m = m + 1;
		//@ ghost tmp = p;
	    } else {
		count = kmp_table[count+1] - 1;
		//@ ghost tmp = p - count;
		q = targetStr + count;
	    }
        } 
        if(count == target_length && k < MAX_MATCH){ //记录目标串在sourceStr中的位置
            match_position[k] = p - target_length - sourceStr + 1;
	    k = k + 1; 
        }
    }
    return k;
}



