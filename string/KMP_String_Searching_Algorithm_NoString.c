//  ��KMP�㷨ʵ���ַ���ƥ����������������ε���ȵġ����ݽṹ��C���԰棩��������P79-83��
//  ���㷨��ʵ����Ҫ�����������棺
//  1. ��������������Ŀ���ַ����Ĳ���ƥ���table
//  2. ��Դ�ַ�����ƥ��Ŀ���ַ���
// �ó��������Դ�ַ����Ѿ�̬��������main�����У�����������Ŀ���ַ���������������ĳ��ϡ�

//#include <stdio.h>
//#include <string.h>
//#include <stdlib.h>
#define TARGET_MAX_LENGTH 20		//�趨Ŀ���ַ�����󳤶�
#define MAX_MATCH 10			//����¼MAX_MATCH��ƥ��
int kmp_table[TARGET_MAX_LENGTH + 1];	//ΪĿ�괮������kmp��kmp_table[0]�������ã���Ϊ�������ϵ�next��һ��
int source_length, target_length;	//��סԴ����Ŀ�괮���ȵı���
int match_position[MAX_MATCH];		//��¼��Ŀ�괮ƥ���Դ���е�λ��,ֻ��¼ǰMAX_MATCH��ƥ��


// ����Ŀ���ַ�����KMP��

/*@ requires \length(table) == TARGET_MAX_LENGTH+1 && \is_pstring(str,target_length) && 0 < target_length <= TARGET_MAX_LENGTH;
    ensures table[1] == 0 && \length(table) == TARGET_MAX_LENGTH+1 &&
	(\forall integer k:[2..target_length].1 <= table[k] < k) &&
	\forall integer k:[2..target_length]. \forall integer n:[1..table[k]-1].str[n-1] == str[k-table[k]+n-1];
*/
void Create_KMP_Table(char* const str, int* const table){
    int i, j;

    i = 1; table[1] = 0; j = 0;
    /*@ loop invariant
	j == 0 && 1 <= i <= target_length &&						    //�������ĵ�һ��֧����������Ҫ���������
	    j < i && table[1] == 0 && table[i] < i && \is_pstring(str,target_length) &&
	    \length(table) == TARGET_MAX_LENGTH+1 && 0 < target_length <= TARGET_MAX_LENGTH &&
	    (\forall integer k:[2..i].1 <= table[k] < k) && (\forall integer k:[2..i].\forall integer n:[1..table[k]-1].str[n-1] == str[k-table[k]+n-1]) ||

	1 <= j <= target_length - 1 && 2 <= i <= target_length && table[i] == j &&	    //�������ĵڶ���֧����������Ҫ���������
	    j < i && table[1] == 0 && table[i] < i && \is_pstring(str,target_length) &&
	    \length(table) == TARGET_MAX_LENGTH+1 && 0 < target_length <= TARGET_MAX_LENGTH &&
	    (\forall integer k:[2..i].1 <= table[k] < k) && (\forall integer k:[2..i].\forall integer n:[1..table[k]-1].str[n-1] == str[k-table[k]+n-1]) ||

	1 <= j <= target_length - 1 && 2 < i <= target_length && table[i] == j &&	    //�������ĵ�����֧����������Ҫ��������� 
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
	    j = table[j]; table[i] = j; //table[i] = j�����ӵģ���ʹ��������֧�ĳ���ͳһ����table[i]==j��ѭ������ʽ��������٣�����ȥ��ʹ��Z3֤�����˵�����
	}
    }
}


// ��Դ��sourceStr������Ŀ�괮targetStr,��kmp_table�м�¼Ŀ�괮��Դ���е�λ����Ϣ,����Ŀ�괮��ƥ����
/*@ requires \is_pstring(targetStr,target_length) && \is_pstring(sourceStr,source_length) &&
	0 < target_length <= TARGET_MAX_LENGTH && target_length <= source_length;
    assigns kmp_table;
    ensures (\forall integer i:[0..\result-1].\forall integer j:[1..target_length]. sourceStr[(match_position[i]-1)+j-1] == targetStr[j-1]);
*/
int Search_Keyword(char* const sourceStr, char* const targetStr){
    char *p, *q;	//p��q��������������ɨ��ָ��
    int count;	    	//��¼ɨ��sourceStr�������Ѿ�ƥ����ֽ���
    int k;	    	//��¼sourceStr������targetStrƥ����Ӵ���
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
    
    Create_KMP_Table(targetStr, kmp_table); //����Ŀ�괮��KMP��
    p = sourceStr; k = 0; //@ ghost m = 0;
    /*@	loop invariant  \is_pstring(targetStr,target_length) && \is_pstring(sourceStr,source_length) && p == sourceStr + m &&
	    0 < target_length <= TARGET_MAX_LENGTH && target_length <= source_length &&
	    sourceStr <= p <= sourceStr + source_length && 0 <= k <= MAX_MATCH && kmp_table[1] == 0 &&
	    (\forall integer k:[2..target_length].1 <= kmp_table[k] < k) &&
	    (\forall integer k:[2..target_length].\forall integer n:[1..kmp_table[k]-1].targetStr[n-1] == targetStr[k-kmp_table[k]+n-1]) &&
	    (\forall integer i:[0..k-1].\forall integer j:[1..target_length]. sourceStr[(match_position[i]-1)+j-1] == targetStr[j-1]);
    */

    while(p < sourceStr + source_length){   //ֱ��������sourceStr�����һ���ַ�Ϊֹ
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
            if(*q == *p){ //count��ʾ�Ѿ��ж��ٸ��ַ���ͬ��
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
        if(count == target_length && k < MAX_MATCH){ //��¼Ŀ�괮��sourceStr�е�λ��
            match_position[k] = p - target_length - sourceStr + 1;
	    k = k + 1; 
        }
    }
    return k;
}



