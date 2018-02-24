const int m = 100; const int k = 100; const int n = 100; const int b = 25;
typedef int AB[100][100];
typedef int BC[100][100];
typedef int AC[100][100];
int X[100][100];
int Y[100][100];
int Z[100][100];
/*@
logic integer tmpsum(AB X, BC Y, integer i, integer j,integer l) =
    (l == 0) ? 0 : (tmpsum(X, Y, i, j, l-1) + X[i][l-1] * Y[l-1][j]);

predicate element(AB X, BC Y, AC Z, integer i, integer j, integer l) =
    (Z[i][j]== tmpsum(X, Y, i, j, l));

predicate blockColumn(AB X, BC Y, AC Z, integer i, integer jj, integer j, integer ll) =
    \forall integer j1: [jj..j]. element(X, Y, Z, i, j1, ll); 
   
predicate blockRow(AB X, BC Y, AC Z, integer b, integer ii, integer i, integer jj, integer ll) =
    \forall integer i1: [ii..i]. blockColumn(X, Y, Z, i1, jj, jj+b-1, ll);
   
predicate matrixBlock(AB X, BC Y, AC Z, integer b, integer ii, integer jj, integer ll) =
    blockRow(X, Y, Z, b, ii, ii+b-1, jj, ll);
   
predicate matrixColumn(AB X, BC Y, AC Z, integer b, integer ii, integer jj) = 
    \forall integer j1: [0..jj/b-1]. matrixBlock(X, Y, Z, b, ii, j1*b, 100);
   
predicate matrixRow(AB X, BC Y, AC Z, integer b, integer ii) =
    \forall integer i1: [0..ii/b-1]. matrixColumn(X, Y, Z, b, i1*b, 100);
    
predicate matrixMultiply(AB X, BC Y, AC Z, integer b) =
    matrixRow(X, Y, Z, b, 100); 
*/

/*@
requires m == 100 && k == 100 && n == 100  && b > 0 && b==25;
assigns Z;
uses X, Y;
ensures matrixMultiply(X, Y, Z, b);
*/
void MatrixMultiply() {
    int i, j, l, ii, jj, ll;

//@ ghost int s1, s2, s3;
    /*@ loop invariant m == 100 && k == 100 && n == 100 && b == 25 && 0 <= ii <= m &&
	(\forall integer i1: [0..ii-1].( \forall integer j1: [0..n-1]. Z[i1][j1] == 0));
    */
    for(ii = 0; ii < m; ii=ii+1) {
	/*@ loop invariant m == 100 && k == 100 && n == 100 && b == 25 && 0 <= ii < m && 0 <= jj <= n &&
		(\forall integer i1: [0..ii-1]. (\forall integer j1: [0..n-1]. Z[i1][j1] == 0)) &&
		    (\forall integer j1: [0..jj-1]. Z[ii][j1] == 0);
	*/
	for(jj = 0; jj < n; jj=jj+1) {
	    Z[ii][jj] = 0;
	}
    }
    //@ ghost s1 = 0;
    /*@ loop invariant m == 100 && k == 100 && n == 100  && b == 25 &&
	    (\forall integer i1: [ii..m-1]. (\forall integer j1: [0..n-1]. Z[i1][j1] == 0)) &&
		0 <= ii <= m && ii == b * s1 && matrixRow(X, Y, Z, b, ii);
    */
    for(ii = 0; ii < m; ii = ii + b) {
	//@ ghost s2 = 0;
	/*@ loop invariant m == 100 && k == 100 && n == 100 && b == 25 &&
		(\forall integer i1: [ii..ii+b-1]. (\forall integer j1: [jj..n-1]. Z[i1][j1] == 0)) &&
		(\forall integer i1: [ii+b..m-1]. (\forall integer j1: [0..n-1]. Z[i1][j1] == 0)) &&
		0 <= ii < m && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
		0 <= jj <= n && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj);
	*/
	for(jj = 0; jj < n; jj = jj + b) {
	    //@ ghost s3 = 0;
	    /*@ loop invariant m == 100 && k == 100 && n == 100 && b == 25 &&
		    (\forall integer i1: [ii..ii+b-1]. (\forall integer j1: [jj..n-1]. Z[i1][j1] == 0)) &&
		    (\forall integer i1: [ii+b..m-1]. (\forall integer j1: [0..n-1]. Z[i1][j1] == 0)) &&
		    0 <= ii < m && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
		    0 <= jj < n && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj) &&
		    0 <= ll <= k && ll == b * s3 && matrixBlock(X, Y, Z, b, ii, jj, ll);
	    */
	    for(ll = 0; ll < k; ll = ll + b) {
		/*@ loop invariant m == 100 && k == 100 && n == 100  && b == 25 &&
			(\forall integer i1: [ii..ii+b-1].(\forall integer j1:[jj..n-1].Z[i1][j1] == 0))&&
			(\forall integer i1: [ii+b..m-1]. (\forall integer j1: [0..n-1]. Z[i1][j1] == 0)) &&
			0 <= ii < m && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
			0 <= jj < n && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj) &&
			0 <= ll < k && ll == b * s3 && ii <= i <= ii + b <= m &&
			blockRow(X, Y, Z, b, ii, i-1, jj, ll+b) && blockRow(X, Y, Z, b, i, ii+b-1, jj, ll);
		*/
		for(i = ii; i < ii + b; i=i+1) {
		    /*@ loop invariant m == 100 && k == 100 && n == 100 && b == 25 &&
			(\forall integer i1: [ii..ii+b-1].(\forall integer j1:[jj..n-1].Z[i1][j1] == 0)) &&
			(\forall integer i1: [ii+b..m-1]. (\forall integer j1: [0..n-1]. Z[i1][j1] == 0)) &&
			0 <= ii < m && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
			0 <= jj < n && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj) &&
			0 <= ll < k && ll == b * s3 && ii <= i < ii + b <= m &&
			blockRow(X, Y, Z, b, ii, i-1, jj, ll+b) && blockRow(X, Y, Z, b, i+1, ii+b-1, jj, ll) &&
			jj <= j <= jj + b <= n &&
			blockColumn(X, Y, Z, i, jj, j-1, ll+b) && blockColumn(X, Y, Z, i, j, jj+b-1, ll);
		    */
		    for(j = jj; j < jj+b; j=j+1) {
			/*@ loop invariant m == 100 && k == 100 && n == 100 && b == 25 &&
		  	    (\forall integer i1: [ii..ii+b-1].(\forall integer j1: [jj..n-1]. Z[i1][j1] == 0)) &&
			    (\forall integer i1: [ii+b..m-1].(\forall integer j1: [0..n-1]. Z[i1][j1] == 0)) &&
			    0 <= ii < m && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
			    0 <= jj < n && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj) &&
			    0 <= ll < k && ll == b * s3 && ii <= i < ii + b <=m &&
			    blockRow(X, Y, Z, b, ii, i-1, jj, ll+b) && blockRow(X, Y, Z, b, i+1, ii+b-1, jj, ll) &&
			    jj <= j < jj + b <= n &&
			    blockColumn(X, Y, Z, i, jj, j-1, ll+b) && blockColumn(X, Y, Z, i, j+1, jj+b-1, ll) &&
			    ll <= l <= ll + b <= k && element(X, Y, Z, i, j, l);
			*/
			for(l = ll; l < ll + b; l=l+1) {
			    Z[i][j] = Z[i][j] + X[i][l]*Y[l][j];
			}
		    }
		}
		//@ ghost s3 = s3 + 1;
	    }
	    //@ ghost s2 = s2 + 1;
	}
	//@ ghost s1 = s1 + 1;
    }
}


