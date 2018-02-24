// ��Դ�ڣ�Դ����� - C����������c.biancheng.net/cpp/u/yuanma/
// �ļ������ʹ�ӡ�����ʱ��ע��



// #include<stdio.h>
#define Queens 8  //����������Ĵ�С��Ҳ���ǻʺ����Ŀ

typedef int S[Queens+1];
S a = {0};   //�˻ʺ�����Ļʺ����ڵ�����λ�ã��±��ʾ�У���Ӧ�±������ֵ��ʾ�У�����1��ʼ�������Լ�1

/*@ 
inductive NotSameColumn(S a, integer n) =
    n == 0 || n >= 1 && NotSameColumn(a, n-1) && (\forall integer i:[1..n-1].a[i]!=a[n]);
inductive NotSameDiagonal(S a, integer n) =
    n == 0 || n >= 1 && NotSameDiagonal(a, n-1) && (\forall integer i:[1..n-1]. a[n]!=a[i]-(i-n) && a[n]!=a[i]+(i-n));
*/
/*@ requires a[0] == 0;
    assigns a;
    ensures \true;
*/
void EightQueens(){
    int i, k, flag, not_finish=1, count=0;
   
    not_finish=1; count = 0;	//�����ó�ֵ�����δʵ�֣����ò��������������
    i=1;     //i��ʾ�кţ���ʼʱ�ڷŵ�1�еĻʺ�
    a[1]=1;  //�ӵ�1�п�ʼ����
//    printf("The possible configuration of 8 queens are:\n");
    /*@ loop invariant 1<=i<=Queens && a[0] == 0 && (\forall integer j:[1..i].a[j] > 0) &&
		not_finish==1 && NotSameColumn(a,i-1) && NotSameDiagonal(a,i-1) && count >= 0 || not_finish==0;
    */
    while(not_finish==1){  //not_finish=l:������δ����
	/*@ loop invariant 1<=i<=Queens && a[0] == 0 && (\forall integer j:[1..i].a[j] > 0) &&
		    	NotSameColumn(a,i-1) && NotSameDiagonal(a,i-1) && count >= 0 && not_finish==1 ||
		    i==Queens+1 && a[0] == 0 && (\forall integer j:[1..Queens].a[j] > 0) &&
		    	NotSameColumn(a,Queens) && NotSameDiagonal(a,Queens) && count >= 0 && not_finish==1||
		    not_finish==0; 
	*/
	while(not_finish==1 && i<=Queens){  //������δ�����һ�û������Queens��Ԫ��
	    flag=1;
	    /*@ loop invariant 1<=i<=Queens && 1<=k<=i && not_finish==1 && a[0] == 0 && (\forall integer j:[1..i].a[j] > 0) &&
			NotSameColumn(a,i-1) && NotSameDiagonal(a,i-1) && count >= 0 &&
			(flag==1 && (\forall integer j:[1..k-1].a[j]!=a[i]) || flag==0 && a[k-1]==a[i]); 
	    */ 
	    for(k=1; flag==1 && k<i; k=k+1){ //�ж��Ƿ��ж���ʺ���ͬһ����
		if(a[k]==a[i]){
		    flag=0;
		}
	    }
	    /*@ loop invariant
		    1<=i<=Queens && 1<=k<=i && a[0] == 0 && (\forall integer j:[1..i].a[j] > 0) && not_finish==1 &&
			NotSameDiagonal(a,i-1) && count >= 0 && NotSameColumn(a,i-1) && flag==0 ||
		    1<=i<=Queens && 1<=k<=i && a[0] == 0 && (\forall integer j:[1..i].a[j] > 0) && not_finish==1 &&
			NotSameDiagonal(a,i-1) && count >= 0 &&	NotSameColumn(a,i) &&
			(flag==1 && (\forall integer j:[1..k-1].a[i]!=a[j]-(j-i) && a[i]!=a[j]+(j-i)) || flag==0 && (a[i]==a[k-1]-(k-1-i) || a[i]==a[k-1]+(k-1-i)));
	    */
	    for(k=1;flag==1 && k<i; k=k+1){  //�ж��Ƿ��ж���ʺ���ͬһ�Խ�����
		if(a[i]==a[k]-(k-i) || a[i]==a[k]+(k-i)){
		    flag=0;
		}
	    }
	    if(flag==0){  //������ì�ܣ�����Ҫ�������õ�i��Ԫ��
		if(a[i]==a[i-1]){  //��a[i]��ֵ�Ѿ�����һȦ׷��a[i-1]��ֵ
		    i=i-1;  //�˻�һ����������̽����ǰһ��Ԫ��
		    if(i>1 && a[i]==Queens)
			a[i]=1;  //��a[i]ΪQueensʱ��a[i]��ֵ��1
		    else
			if(a[i]==Queens)
			    not_finish=0;  //����һ�е�ֵ�ﵽQueensʱ����
			else
			    a[i]=a[i]+1;  //��a[il��ֵȡ��һ��ֵ
		}else if(a[i]==Queens)
		    a[i]=1;
		else
		    a[i]=a[i]+1;  //��a[i]��ֵȡ��һ��ֵ
	    }else{
		i=i+1;
		if(i<=Queens){
		    if(a[i-1]==Queens)
			a[i]=1;  //��ǰһ��Ԫ�ص�ֵΪQueens��a[i]=l
		    else
			a[i]=a[i-1]+1;  //����Ԫ�ص�ֵΪǰһ��Ԫ�ص���һ��ֵ
		}
	    }
	}
	if(not_finish == 1){
	    count=count+1;
//	    printf((count-1)%3 ? "\t[%2d]:" : "\n[%2d]:", count);
	    /*@ loop invariant i==Queens+1 && a[0] == 0 && (\forall integer j:[1..Queens].a[j] > 0) && not_finish==1 &&
	    		    NotSameColumn(a,Queens) && NotSameDiagonal(a,Queens) && count >= 0 && 1<=k<=Queens+1;
	    */
	    for(k=1; k<=Queens; k=k+1) //������
//		printf(" %d", a[k])
		;
	    if(a[Queens-1]<Queens )
		a[Queens-1] = a[Queens-1]+1;  //�޸ĵ����ڶ�λ��ֵ
	    else
		a[Queens-1]=1;
	    i=Queens-1;    	//��ʼѰ����һ�����������Ľ�
	}
    }
//    printf("\n");
}

