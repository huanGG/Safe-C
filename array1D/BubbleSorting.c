int n;
typedef int array[1000];

/*@ 
requires \length(a) == n && n == 1000;
ensures (\forall integer i : [0..n-2]. a[i]<=a[i+1]) && \length(a) == n;
*/
void bubbleSort(array a) {
    int low, up, j, k, temp;
    low = 0; up = n-1; k = up; 
    /*@ loop invariant
    	    n == 1000 && low == 0 && up == n-1 && k == up && \length(a) == n && 
	    	(\forall integer i:[k+1..up-1].a[i]<=a[i+1])||
	    n == 1000 && low == 0 && up == n-1 && low <= k < up && \length(a) == n &&
     		(\forall integer i : [low..k]. a[i]<=a[k+1]) &&
		(\forall integer i : [k+1..up-1]. a[i]<=a[i+1]);
    */
    while( k != low) {
	j = low;
	/*@ loop invariant
	 	n == 1000 && low == 0 && up == n-1 && k == up &&  low <= j <= k && \length(a) == n &&
			(\forall integer i : [low..j-1]. a[i]<=a[j]) &&
			(\forall integer i : [k+1..up-1]. a[i]<=a[i+1])||
		n == 1000 && low == 0 && up == n-1 && low < k < up &&  low <= j <= k && \length(a) == n &&
			(\forall integer i : [low..j-1]. a[i]<=a[j]) &&
			(\forall integer i : [low..k]. a[i]<=a[k+1]) &&
			(\forall integer i : [k+1..up-1]. a[i]<=a[i+1]);
	
	*/
	while( j!=k ) {
	    if (a[j] > a[j+1]) {
		temp = a[j]; a[j] = a[j+1]; a[j+1] = temp;
	    }
	    j = j + 1;
	}
	k = k -1;
    }
    return;
}

