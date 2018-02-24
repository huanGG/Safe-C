// 来源于：源码分享 - C语言中文网c.biancheng.net/cpp/u/yuanma/
// 文件包含和打印语句暂时被注释



// #include<stdio.h>
#define Queens 8  //定义结果数组的大小，也就是皇后的数目

typedef int S[Queens+1];
S a = {0};   //八皇后问题的皇后所在的行列位置（下标表示行，相应下标变量的值表示列），从1幵始算起，所以加1

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
   
    not_finish=1; count = 0;	//由于置初值语句尚未实现，不得不加上这两个语句
    i=1;     //i表示行号，初始时摆放第1行的皇后
    a[1]=1;  //从第1列开始尝试
//    printf("The possible configuration of 8 queens are:\n");
    /*@ loop invariant 1<=i<=Queens && a[0] == 0 && (\forall integer j:[1..i].a[j] > 0) &&
		not_finish==1 && NotSameColumn(a,i-1) && NotSameDiagonal(a,i-1) && count >= 0 || not_finish==0;
    */
    while(not_finish==1){  //not_finish=l:处理尚未结束
	/*@ loop invariant 1<=i<=Queens && a[0] == 0 && (\forall integer j:[1..i].a[j] > 0) &&
		    	NotSameColumn(a,i-1) && NotSameDiagonal(a,i-1) && count >= 0 && not_finish==1 ||
		    i==Queens+1 && a[0] == 0 && (\forall integer j:[1..Queens].a[j] > 0) &&
		    	NotSameColumn(a,Queens) && NotSameDiagonal(a,Queens) && count >= 0 && not_finish==1||
		    not_finish==0; 
	*/
	while(not_finish==1 && i<=Queens){  //处理尚未结束且还没处理到第Queens个元素
	    flag=1;
	    /*@ loop invariant 1<=i<=Queens && 1<=k<=i && not_finish==1 && a[0] == 0 && (\forall integer j:[1..i].a[j] > 0) &&
			NotSameColumn(a,i-1) && NotSameDiagonal(a,i-1) && count >= 0 &&
			(flag==1 && (\forall integer j:[1..k-1].a[j]!=a[i]) || flag==0 && a[k-1]==a[i]); 
	    */ 
	    for(k=1; flag==1 && k<i; k=k+1){ //判断是否有多个皇后在同一列上
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
	    for(k=1;flag==1 && k<i; k=k+1){  //判断是否有多个皇后在同一对角线上
		if(a[i]==a[k]-(k-i) || a[i]==a[k]+(k-i)){
		    flag=0;
		}
	    }
	    if(flag==0){  //若存在矛盾，则需要重新设置第i个元素
		if(a[i]==a[i-1]){  //若a[i]的值已经经过一圈追上a[i-1]的值
		    i=i-1;  //退回一步，重新试探处理前一个元素
		    if(i>1 && a[i]==Queens)
			a[i]=1;  //当a[i]为Queens时将a[i]的值置1
		    else
			if(a[i]==Queens)
			    not_finish=0;  //当第一行的值达到Queens时结束
			else
			    a[i]=a[i]+1;  //将a[il的值取下一个值
		}else if(a[i]==Queens)
		    a[i]=1;
		else
		    a[i]=a[i]+1;  //将a[i]的值取下一个值
	    }else{
		i=i+1;
		if(i<=Queens){
		    if(a[i-1]==Queens)
			a[i]=1;  //若前一个元素的值为Queens则a[i]=l
		    else
			a[i]=a[i-1]+1;  //否则元素的值为前一个元素的下一个值
		}
	    }
	}
	if(not_finish == 1){
	    count=count+1;
//	    printf((count-1)%3 ? "\t[%2d]:" : "\n[%2d]:", count);
	    /*@ loop invariant i==Queens+1 && a[0] == 0 && (\forall integer j:[1..Queens].a[j] > 0) && not_finish==1 &&
	    		    NotSameColumn(a,Queens) && NotSameDiagonal(a,Queens) && count >= 0 && 1<=k<=Queens+1;
	    */
	    for(k=1; k<=Queens; k=k+1) //输出结果
//		printf(" %d", a[k])
		;
	    if(a[Queens-1]<Queens )
		a[Queens-1] = a[Queens-1]+1;  //修改倒数第二位的值
	    else
		a[Queens-1]=1;
	    i=Queens-1;    	//开始寻找下一个满足条件的解
	}
    }
//    printf("\n");
}

