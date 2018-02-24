const int m = 100; const int k = 200; const int n = 300;
typedef int AB[100][200];
typedef int BC[200][300];
typedef int AC[100][300];

AB X; BC Y; AC Z;

//谓词原型的声明
/*@
predicate row(AB X, BC Y, AC Z, integer i); // 数组Z从0到i-1各行的元素的值都已算好
predicate column(AB X, BC Y, AC Z, integer i, integer j); // 在第i行中，元素Z[i][0], ..., Z[i][j-1]的值都已算好
predicate element(AB X, BC Y, AC Z, integer i, integer j, integer l); // 元素Z[i][j]的值的计算已经累加了X[i][l-1] * Y[l-1][j]
logic integer tmpsum(AB X, BC Y,integer i, integer j,int l); // 计算一个点的逻辑函数
*/

//谓词定义
/*@
predicate matrixMultiply(AB X, BC Y, AC Z) = row(X, Y, Z,100);  // 数组Z的所有行都已经计算好
predicate row(AB X, BC Y, AC Z, integer i) =
    \forall integer i1: [0..i-1]. column(X, Y, Z, i1, 300);
predicate column(AB X, BC Y, AC Z, integer i, integer j) =
    \forall integer j1: [0..j-1]. element(X, Y, Z, i, j1, 200);
predicate element(AB X, BC Y, AC Z, integer i, integer j, integer l) =
    Z[i][j] == tmpsum(X, Y, i, j, l); 
logic integer tmpsum(AB X, BC Y, integer i, integer j, integer l) =
    (l == 0) ? 0 : (tmpsum(X, Y, i, j, l-1) + X[i][l-1] * Y[l-1][j]);
*/

/*@ requires m == 100 && k == 200 && n == 300;   
    ensures matrixMultiply(X, Y, Z);
*/
void MatrixMultiply() {
    int i, j, l;
    /*@loop invariant 0 <= i && i <= m && row(X, Y, Z, i) && m == 100 && k == 200 && n == 300;
          loop variant m - i;
    */
    for (i = 0; i < m; i = i + 1) {
	/*@loop invariant 0 <= i && i < m && row(X, Y, Z, i) && 0 <= j && j<= n &&
              column(X, Y, Z, i, j) && m == 100 && k == 200 && n == 300;
              loop variant n - j;
	*/
	for (j = 0; j < n; j = j + 1) {
	    Z[i][j] = 0;
	    /*@loop invariant 0 <= i && i < m && row(X, Y, Z, i) && 0 <= j && j < n &&
                  column(X, Y, Z, i, j) && 0 <= l && l <= k && element(X, Y, Z, i, j, l) &&
                  m == 100 && k == 200 && n == 300;
	    */
	    for (l = 0; l < k; l = l + 1) {
		Z[i][j] = Z[i][j] + X[i][l] * Y[l][j];
	    }
	}
    }
    return;
}
