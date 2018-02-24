#define length   20
typedef long array[length];
array a = {2, 5, 3, -10, 30, 5, 999, -888, 250, 140, 70, 86, 352, -128, 38, -26, 69, 8, 19, 20}; 

long low, up;

/*@ requires  low == 0 && up == length - 1 && low <= low1 && low1 <= up1 && up1<= up && \length(arr) == length;
    ensures  low == 0 && up == length - 1 && 
	low <= low1 && low1 <= up1 && up1 <= up && low1 <= \result && \result <= up1 && \length(arr) == length &&
	(\forall integer i:[low1..\result-1]. *(arr+i) <= *(arr+\result)) && *(arr+\result) < *(arr+up1) &&
	(\forall integer i:[\result+1..up1]. *(arr+i) > *(arr+\result));
*/
long partition( long*  const arr, const long low1, const long up1) {
    long k, m, j, temp, ret;
    k = *(arr+up1); 	m=low1-1; j = low1;
    /*@ loop invariant low == 0 && up == length - 1 && low <= low1 && low1 <= up1 && up1 <= up &&
	    low1-1 <= m && m <= up1-1 && low1 <= j && j <= up1 && m < j && \length(arr) == length && *(arr+up1) == k && 
	    (\forall integer i:[low1..m]. *(arr+i) <= k) && (\forall integer i:[m+1..j-1]. *(arr+i) > k);
    */
    while(j != up1) {
	if( *(arr+j) <= k ) {
	    m = m+1; temp = *(arr+m); *(arr+m) = *(arr+j); *(arr+j) = temp;
	}
	j = j + 1;
    }
    temp = *(arr+up1);  *(arr+up1) = *(arr+m+1); *(arr+m+1) = temp; ret = m+1; return ret;
}

/*@
requires low == 0 && up == length - 1 && low <= low2 && up2 <= up && \length(arr) == length;
ensures low <= low2 && up2 <= up && \length(arr) == length &&
		(\forall integer i: [low2..up2-1]. *(arr+i) <= *(arr + (i+1)))
		
	;
*/
void quick_sort( long* const  arr, const long low2, const long up2 ) {
    long j;
    if( low2 < up2) {
	j = partition(arr, low2, up2 ); quick_sort(arr, low2, j - 1 ); quick_sort(arr, j + 1, up2 );
    }
    return;
}



