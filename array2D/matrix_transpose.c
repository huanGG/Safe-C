#include "matrix_include.h"
// 函数matrix_transpose的功能：对矩阵mat1做转置运算，得到转置矩阵mat2。
// 用断言定义矩阵的转置过程

/*@predicate row_transpose(MAT_TYPE m1, MAT_TYPE m2, integer i);
  @predicate col_transpose(MAT_TYPE m1, MAT_TYPE m2, integer i, integer j);
  @predicate matrix_transpose(MAT_TYPE m1, MAT_TYPE m2);


  @predicate matrix_transpose(MAT_TYPE m1, MAT_TYPE m2) =
      row_transpose(m1, m2, CAPACITY);
  
  @predicate row_transpose(MAT_TYPE m1, MAT_TYPE m2, integer i) =
      ( \forall integer n:[0..i-1]. col_transpose(m1, m2, n, CAPACITY) );

  @predicate col_transpose(MAT_TYPE m1, MAT_TYPE m2, integer i, integer j) =
      ( \forall integer n:[0..j-1]. m2[n][i] == m1[i][n] );
 */

/*@ensures
      matrix_transpose(mat1, mat2);
 */
void matrix_transpose()
{
    int i, j;
    /*@loop invariant
          0 <= i <= CAPACITY &&
	  row_transpose(mat1, mat2, i);
     */
    for ( i = 0; i < CAPACITY; i = i + 1 ) {
	/*@loop invariant
	      0 <= i < CAPACITY &&
	      row_transpose(mat1, mat2, i) &&
	      0 <= j <= CAPACITY &&
	      col_transpose(mat1, mat2, i, j);
	 */
	for ( j = 0; j < CAPACITY; j = j + 1 ) {
	    mat2[j][i] = mat1[i][j];
	}
    }
}
