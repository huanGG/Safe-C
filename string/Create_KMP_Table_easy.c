//  ��KMP�㷨ʵ���ַ���ƥ����������������ε���ȵġ����ݽṹ��C���԰棩��������P79-83��
//  ���㷨��ʵ����Ҫ�����������棺
//  1. ��������������Ŀ���ַ����Ĳ���ƥ���table
//  2. ��Դ�ַ�����ƥ��Ŀ���ַ���
// �ó��������Դ�ַ����Ѿ�̬��������main�����У�����������Ŀ���ַ���������������ĳ��ϡ�


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


