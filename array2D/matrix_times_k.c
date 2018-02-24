#include "matrix_include.h"

//  定义什么是矩阵倍乘：

/*@predicate col_times_k(MAT_TYPE m, MAT_TYPE m_k, integer i, integer j, integer k) =
      ( \forall integer n:[0..j-1]. m_k[i][n] == k * m[i][n] );

  @predicate row_times_k(MAT_TYPE m, MAT_TYPE m_k, integer i, integer k) =
      ( \forall integer n:[0..i-1]. col_times_k(m, m_k, n, CAPACITY, k) );

  @predicate matrix_times_k(MAT_TYPE m, MAT_TYPE m_k, integer k) =
      row_times_k(m, m_k, CAPACITY, k);

 */

/*@ensures
      matrix_times_k(mat1, mat2, k);
 */
void matrix_times_k(const int k)
{
    int i, j;

    /*@loop invariant
          0 <= i <= CAPACITY &&
          row_times_k(mat1, mat2, i, k);
     */
    for ( i = 0; i < CAPACITY; i = i + 1 ) {
        /*@loop invariant
              0 <= i < CAPACITY &&
              row_times_k(mat1, mat2, i, k) &&
              0 <= j <= CAPACITY &&
              col_times_k(mat1, mat2, i, j, k);
         */
        for ( j = 0; j < CAPACITY; j = j + 1 ) {
            mat2[i][j] = k * mat1[i][j];
        }
    }
}

