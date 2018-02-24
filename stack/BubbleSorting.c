int n;	    		// a指在数组的起始地方
typedef int array[1000];

/*@ requires n == 1000 && \length(a) == n;
    ensures n == 1000 &&(\forall integer i : [0..n-2]. *(a + i) <= *(a +(i+1)));
*/
void bubbleSort(int* const a) {
    int low, up, j, k, temp;
    low = 0; up = n-1; k = up; 
    /*@ loop invariant
    	n == 1000 && low == 0 && up == n-1 && k == up && \length(a) == n && \offset(a) == 0 &&
			(\forall integer i:[k+1..up-1].*(a + i) <= *(a + (i+1))) ||
	    n == 1000 && low == 0 && up == n-1 && low <= k < up && \length(a) == n && \offset(a) == 0 &&
     		(\forall integer i : [low..k]. *(a + i) <= *(a + (k+1))) &&
		(\forall integer i : [k+1..up-1]. *(a + i) <= *(a + (i+1)));
    */
    while( k != low) {
	j = low;
	/*@ loop invariant
	 	n == 1000 && low == 0 && up == n-1 && k == up &&  low <= j <= k && \length(a) == n && \offset(a) == 0 &&
			(\forall integer i : [low..j-1]. *(a + i) <= *(a + j)) &&
			(\forall integer i : [k+1..up-1]. *(a + i) <= *(a + (i+1)))||
		n == 1000 && low == 0 && up == n-1 && low < k < up &&  low <= j <= k && \length(a) == n && \offset(a) == 0 &&
			(\forall integer i : [low..j-1]. *(a + i) <= *(a + j)) &&
			(\forall integer i : [low..k]. *(a + i) <= *(a + (k+1))) &&
			(\forall integer i : [k+1..up-1]. *(a + i) <= *(a + (i+1)));
	
	*/
	while( j!=k ) {
	    if (*(a + j) > *(a + (j+1))) {
		temp = *(a + j); *(a + j) = *(a + (j+1)); *(a + (j+1)) = temp;
	    }
	    j = j + 1;
	}
	k = k -1;
    }
    return;
}

