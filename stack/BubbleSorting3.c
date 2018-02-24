int n;	// a指在数组的顶端，部分代码和断言仍用下标变量。
typedef int array[1000];

/*@ requires n == 1000 && \length(a1) == n;
    ensures n == 1000 &&(\forall integer i : [0..n-2]. a1[i] <= a1[i+1]);
*/
void bubbleSort(int a1[]) {
    int low, up, j, k, temp;
    low = 0; up = n-1; k = up;
    int* a ;
    a = a1 + (n-1);
    /*@ loop invariant
	    n == 1000 && low == 0 && up == n-1 && k == up && \length(a1) == n && \offset(a1) == 0 && a == a1 + (n-1) &&
		(\forall integer i:[k+1..up-1]. a1[i] <= a1[i+1])
	  ||
	    n == 1000 && low == 0 && up == n-1 && low <= k < up && \length(a1) == n && \offset(a1) == 0 && a == a1 + (n-1) &&
     		(\forall integer i : [low..k]. *(a - (n - i - 1)) <= *(a - (n - k - 2))) &&
		(\forall integer i : [k+1..up-1]. *(a - (n - i - 1)) <= *(a - (n - i - 2)));
    */
    while( k != low) {
	j = low;
	/*@ loop invariant
	    n == 1000 && low == 0 && up == n-1 && k == up &&  low <= j <= k && \length(a1) == n && \offset(a1) == 0 && a == a1 + (n-1) &&
		(\forall integer i : [low..j-1]. *(a - (n - i - 1)) <= *(a - (n - j - 1))) &&
		(\forall integer i : [k+1..up-1]. *(a - (n - i - 1)) <= *(a - (n - i - 2)))
	  ||
	    n == 1000 && low == 0 && up == n-1 && low < k < up &&  low <= j <= k && \length(a1) == n && \offset(a1) == 0 && a == a1 + (n-1) &&
		(\forall integer i : [low..j-1]. a1[i] <= a1[j]) &&
		(\forall integer i : [low..k]. a1[i] <= a1[k+1]) &&
		(\forall integer i : [k+1..up-1]. a1[i] <= a1[i+1]);
	
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

