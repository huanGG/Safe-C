#include "matrix_include.h"
//#define CAPACITY 100

//typedef int MAT_TYPE[CAPACITY][CAPACITY];

//MAT_TYPE mat1, mat2, mat3;

// ����matrix_plus�Ĺ��ܣ��������������ӷ����㣬�ѽ�������ڵ����������С�
// ��֤�㷨�Ƿ���ȷ����Ҫ���壺ʲô����������ļӷ���
// �����أ��˷�һ�������ɶ������ӷ������������ԡ�

/*@predicate row_plus(MAT_TYPE m1, MAT_TYPE m2, MAT_TYPE m3, integer i);
  @predicate col_plus(MAT_TYPE m1, MAT_TYPE m2, MAT_TYPE m3, integer i, integer j);
  @predicate matrix_plus(MAT_TYPE m1, MAT_TYPE m2, MAT_TYPE m3);

  
  @predicate matrix_plus(MAT_TYPE m1, MAT_TYPE m2, MAT_TYPE m3) =
      row_plus(m1, m2, m3, CAPACITY);

  @predicate row_plus(MAT_TYPE m1, MAT_TYPE m2, MAT_TYPE m3, integer i) =
      ( \forall integer n:[0..i-1]. col_plus(m1, m2, m3, n, CAPACITY) );

  @predicate col_plus(MAT_TYPE m1, MAT_TYPE m2, MAT_TYPE m3, integer i, integer j) =
      ( \forall integer n:[0..j-1]. m3[i][n] == m1[i][n] + m2[i][n]);

 */

/*@ensures
      matrix_plus(mat1, mat2, mat3);
 */
void matrix_plus()
{
    int i, j;

    /*@loop invariant
          0 <= i <= CAPACITY &&
          row_plus(mat1, mat2, mat3, i);
     */
    for ( i = 0; i < CAPACITY; i = i + 1 ) {
        /*@loop invariant
              0 <= i < CAPACITY &&
              row_plus(mat1, mat2, mat3, i) &&
              0 <= j <= CAPACITY &&
              col_plus(mat1, mat2, mat3, i, j);
         */
        for ( j = 0; j < CAPACITY; j = j + 1 ) {
            mat3[i][j] = mat1[i][j] + mat2[i][j];
        }
    }
}
