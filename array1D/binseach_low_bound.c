// 二分查找求下界（可以有值相同的元素，查找和value相同的第1个元素的下标）

#define CAPACITY 10000
int elements[CAPACITY];

//@ logic int old_lhs, old_rhs;

/*@
requires (\forall integer j:[1.. CAPACITY-1].elements[j -1] <= elements[j]) &&
    lhs >= 0 && lhs < rhs && rhs <= CAPACITY-1 && old_lhs == lhs && old_rhs == rhs;
ensures (\forall integer j:[1..CAPACITY-1].elements[j -1] <= elements[j]) && (old_lhs < \result &&
    elements[\result -1] < value && \result == old_rhs && \result > 0 && \result <= CAPACITY-1 ||
    old_lhs == \result && elements[\result] >= value && \result >= 0 && \result< CAPACITY-1 ||
    old_lhs< \result && elements[\result -1]< value && elements[\result]>=value &&
	\result > 0 && \result < CAPACITY-1);
*/
int lower_bound(int lhs, int rhs, const int value){
    int m;
    /*@ loop invariant (\forall integer j:[1.. CAPACITY-1].elements[j -1] <= elements[j]) && old_lhs >= 0 &&
	    lhs <= rhs && old_rhs <= CAPACITY-1 &&(old_lhs == lhs && rhs == old_rhs && lhs < rhs ||
	    old_lhs < lhs && elements[lhs -1] < value && rhs == old_rhs ||
	    old_lhs == lhs && elements[rhs] >= value && rhs < old_rhs ||
	    old_lhs < lhs && elements[lhs-1] < value && elements[rhs] >= value && rhs < old_rhs);
    */
    while(lhs < rhs) {
	m = lhs + (rhs - lhs) / 2;
	if(elements[m] >= value) {
	    rhs = m;
	} else {
	    lhs = m + 1;
	}
    }
    return lhs;
}

