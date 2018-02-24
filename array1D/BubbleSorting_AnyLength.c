/*@ requires \length(a) == m && m > 0 && \offset(a) == 0;
    ensures  \length(a) == m && m > 0 && \offset(a) == 0 && \forall integer i : [0..m-2]. a[i] <= a[i+1];
*/
void bubbleSort(int *const a, int const m) {
    int low, up, j, k, temp;
	low = 0; up = m-1; k = up; 
    /*@ loop invariant \length(a) == m && m > 0 && \offset(a) == 0 && low == 0 && up == m-1 &&
	    (k == up &&(\forall integer i:[k+1..up-1].a[i]<=a[i+1]) ||
	    low <= k < up && (\forall integer i:[low..k].a[i]<=a[k+1]) && \forall integer i:[k+1..up-1].a[i]<=a[i+1]);
	*/
    while(k != low) {
	j = low;
	/*@ loop invariant \length(a) == m && m > 0 && \offset(a) == 0 && low == 0 && up == m-1 && k != low && low <= j <= k &&
	    (k == up && (\forall integer i:[low..j-1]. a[i]<=a[j]) &&
		(\forall integer i:[k+1..up-1].a[i]<=a[i+1]) || 
		low < k < up && (\forall integer i:[low..j-1].a[i]<=a[j]) &&
		    (\forall integer i:[low..k].a[i]<=a[k+1]) && \forall integer i:[k+1..up-1].a[i]<=a[i+1]);
	*/
	while( j!=k ) {
	    if (a[j] > a[j+1]) {
		temp = a[j]; a[j] = a[j+1]; a[j+1] = temp;
	    }
	    j = j + 1;
	}
	k = k -1;
    }
}

