#define CAPACITY 100

typedef int array[CAPACITY];

array iarray; // global variable

int len;

int ret;

//@ghost array ghost_old_iarray;

/*@requires
      len >= 0 && len <= CAPACITY &&
      ( \forall integer n:[0..len-1]. ghost_old_iarray[n] == iarray[n] );
  @assigns
      iarray;
  @ensures
      (
        
        ret == -1 &&
        len >= 0 && len <= CAPACITY &&
        ( \forall integer n:[0..len-1]. ghost_old_iarray[n] == iarray[n] )
      ) ||
      (
       
        0 <= ret <= len &&
        len >= 0 && len <= CAPACITY &&
        ( \forall integer n:[0..ret-1]. ghost_old_iarray[n] == iarray[n] ) &&
        ( \forall integer n:[ret..len-1]. ghost_old_iarray[n+1] == iarray[n] )
      );
 */
int array_delete(int x)
{
    int i;

    int idx;
    
    idx = 0;

    /*@loop invariant
          len >= 0 && len <= CAPACITY &&
          0 <= idx <= len &&
          ( ( ( \forall integer n:[0..len-1]. iarray[n] != x) && idx == len ) ||
            ( ( \exists integer n:[0..len-1]. iarray[n] == x) && 0 <= idx <= len )
          )&& ( \forall integer n:[0..len-1]. ghost_old_iarray[n] == iarray[n] );
     */
    while ( idx < len ) {
        if ( iarray[idx] == x ) {
            break;
        }
        else {
            idx = idx + 1;
        }
    }
    
    if ( idx == len ) {
	    ret = -1; 
    }
    else { 
        ret = idx;
        
        /*@loop invariant
              len >= 0 && len <= CAPACITY &&
              0 <= ret < len &&
              ret + 1 <= i <= len &&
              ( ( \forall integer n:[0..ret-1]. ghost_old_iarray[n] == iarray[n] ) &&
                ( \forall integer n:[ret..i-2]. ghost_old_iarray[n+1] == iarray[n] ) &&
                ( \forall integer n:[i..len-1]. ghost_old_iarray[n] == iarray[n] )
              );
         */
        for ( i = ret + 1; i < len; i = i + 1 ) {
            iarray[i-1] = iarray[i];
        }
        len = len - 1; 
    }
    return ret;
}
