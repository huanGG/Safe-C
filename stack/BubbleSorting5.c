int n;	// aָ������Ķ��ˣ���������a - e�ķ�ʽȥ�����±������e >= 0)��
typedef int array[1000];

/*@ requires n == 1000 && \length(a) == n && \offset(a) == n-1;
    ensures n == 1000 &&(\forall integer i : [0..n-2]. *(a-n+1+i) <= *(a-n+2+i));
*/
void bubbleSort(int* const a) {
    int low, up, j, k, temp;
    low = 0; up = n-1; k = up;

    /*@ loop invariant
	    n == 1000 && low == 0 && up == n-1 && k == up && \length(a) == n && \offset(a) == n-1 &&
		(\forall integer i:[k+1..up-1].*(a - (n - i - 1)) <= *(a - (n - i - 2)))
        ||
	    n == 1000 && low == 0 && up == n-1 && low <= k < up && \length(a) == n && \offset(a) == n-1 &&
     		(\forall integer i : [low..k]. *(a - (n - i - 1)) <= *(a - (n - k - 2))) &&
		(\forall integer i : [k+1..up-1]. *(a - (n - i -1)) <= *(a - (n - i - 2)));
    */
    while( k != low) {
	j = low;
	/*@ loop invariant
	    n == 1000 && low == 0 && up == n-1 && k == up &&  low <= j <= k && \length(a) == n && \offset(a) == n-1 &&
		(\forall integer i : [low..j-1]. *(a - (n - i - 1)) <= *(a - (n - j - 1))) &&
		(\forall integer i : [k+1..up-1]. *(a - (n - i - 1)) <= *(a - (n - i - 2)))
	  ||
	    n == 1000 && low == 0 && up == n-1 && low < k < up &&  low <= j <= k && \length(a) == n && \offset(a) == n-1 &&
		(\forall integer i : [low..j-1]. *(a - (n - i - 1)) <= *(a - (n - j - 1))) &&
		(\forall integer i : [low..k]. *(a - (n - i - 1)) <= *(a - (n - k - 2))) &&
		(\forall integer i : [k+1..up-1]. *(a - (n - i - 1)) <= *(a - (n - i - 2)));
	
	*/
	while( j!=k ) {
	    if (*(a - (n - j - 1)) > *(a - (n - j - 2))) {
		temp = *(a - (n - j - 1)); *(a - (n - j - 1)) = *(a - (n - j - 2)); *(a - (n - j - 2)) = temp;
	    }
	    j = j + 1;
	}
	k = k -1;
    }
    return;
}

