#define length  20
typedef long array[length];
array a = {2, 5, 3, -10, 30, 5, 999, -888, 250, 140, 70, 86, 352, -128, 38, -26, 69, 8, 19, 20}; 

long low, up;

//@ logic long* oldarr; 

/*@
requires  low == 0 && up == length - 1 && low <= low1 && low1 < up1 && up1<= up && oldarr == arr && \length(arr) == length;
ensures  low == 0 && up == length - 1 && \length(oldarr) == length && 
    low <= low1 && low1 < up1 && up1 <= up && low1 <= \result && \result <= up1 &&
    (\forall integer i:[low1..\result-1]. oldarr[i] <= oldarr[\result]) && oldarr[\result] < oldarr[up1] &&
    (\forall integer i:[\result+1..up1].oldarr[i] > oldarr[\result]);
*/
long partition(array arr, const long low1, const long up1) {
    long k, m, j, temp, ret;
    k = arr[up1]; 	m=low1-1; j = low1;
    /*@ loop invariant low == 0 && up == length - 1 && low <= low1 && low1 < up1 && up1 <= up &&
	    low1-1 <= m && m <= up1-1 && low1 <= j && j <= up1 && m < j && oldarr == arr && \length(arr) == length && arr[up1] == k && 
	    (\forall integer i:[low1..m]. arr[i] <= k) && (\forall integer i:[m+1..j-1]. arr[i] > k);
    */
    while(j != up1) {
	if( arr[j] <= k ) {
	    m = m+1; temp = arr[m]; arr[m] = arr[j]; arr[j] = temp;
	}
	j = j + 1;
    }
    temp = arr[up1];  arr[up1] = arr[m+1]; arr[m+1] = temp; ret = m+1; return ret;
}

/*@
requires low == 0 && up == length - 1 && low <= low2 && up2 <= up && oldarr == arr && \length(arr) == length;
ensures low <= low2 && up2 <= up && \length(oldarr) == length &&
		(\forall integer j: [low2..up2-1]. oldarr[j] <= oldarr[j+1]);
*/
void quick_sort(array arr, const long low2, const long up2 ) {
    long i;
    if( low2 < up2) {
	i = partition(arr, low2, up2 ); quick_sort(arr, low2, i - 1 ); quick_sort(arr, i + 1, up2 );
    }
    return;
}

/*@ requires \true;
    uses a;
    ensures (\forall integer i: [low..up-1]. a[i] <= a[i+1]);
*/
int main() {
    low = 0; up = length -1;
    quick_sort(a, low, up);
    return 0;
}



