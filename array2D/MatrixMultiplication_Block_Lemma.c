// ����ֿ���˺������Կ��С�����ƣ���������������ĳ��Ϳ�
#define ROW1 100
#define COLUMN1 200
#define ROW2 COLUMN1
#define COLUMN2 300

const int b;
typedef long AB[ROW1][COLUMN1];
typedef long BC[COLUMN1][COLUMN2];
typedef long AC[ROW1][COLUMN2];

/*@
predicate blockSize(integer b) =
    b > 0 && (\exists integer i. ROW1 == i * b) &&
		  (\exists integer j. COLUMN1 == j * b) && (\exists integer k. COLUMN2 == k * b);
    //��ʾb�ܹ�����ROW1��COLUMN1��COLUMN2

logic integer tmpsum(AB X, BC Y, integer i, integer j,integer l) =
    (l == 0) ? 0 : (tmpsum(X, Y, i, j, l-1) + X[i][l-1] * Y[l-1][j]);

predicate blockElement(AB X, BC Y, AC Z, integer i, integer j, integer l) =
    (Z[i][j]== tmpsum(X, Y, i, j, l));
    //Ԫ��Z[i][j]�ļ����Ѿ��ۼ���X[i][l-1] * Y[l-1][j]

predicate blockColumn(AB X, BC Y, AC Z, integer i, integer jj, integer j, integer ll) =
    \forall integer j1: [jj..j]. blockElement(X, Y, Z, i, j1, ll); 
    //�ڵ�i���У�����Z[i][jj], ..., Z[i][j]��ÿ��Ԫ��Z[i][j1]�ļ���
    //���Ѿ��ۼ���X[i][ll-1] * Y[ll-1][j1]

predicate blockRow(AB X, BC Y, AC Z, integer b, integer ii, integer i, integer jj, integer ll) =
    \forall integer i1: [ii..i]. blockColumn(X, Y, Z, i1, jj, jj+b-1, ll);
    //��ii��i����������[ii..i][jj..jj+b-1]��ÿ��Ԫ��Z[ii+x][jj+y]�ļ���
    //���Ѿ��ۼ���X[ii+x][ll-1] * Y[ll-1][jj+y]��ֵ

predicate matrixBlock(AB X, BC Y, AC Z, integer b, integer ii, integer jj, integer ll) =
    blockRow(X, Y, Z, b, ii, ii+b-1, jj, ll);
    //����Z�е�ii/b+1�У��Կ�Ϊ��λͳ�Ƶ��У��ĵ�jj/b+1������ 
    //ÿ��Ԫ��Z[ii+x][jj+y]�ļ��㶼���ۼ���X[ii+x][ll-1] * Y[ll-1][jj+y]��ֵ

predicate matrixColumn(AB X, BC Y, AC Z, integer b, integer ii, integer jj) = 
    \forall integer j1: [0..jj/b-1]. matrixBlock(X, Y, Z, b, ii, j1*b, COLUMN1);
    //����Z�е�ii/b+1�У��Կ�Ϊ��λͳ�Ƶ��к��У���ǰjj/b���鶼�Ѿ����

predicate matrixRow(AB X, BC Y, AC Z, integer b, integer ii) =
    \forall integer i1: [0..ii/b-1]. matrixColumn(X, Y, Z, b, i1*b, COLUMN2);
    // ����Z��ǰii/b�У��Կ�Ϊ��λͳ�Ƶ��У��Ŀ鶼�����

predicate matrixMultiply(AB X, BC Y, AC Z, integer b) =
    matrixRow(X, Y, Z, b, ROW1); //����Z�����п鶼�Ѿ����

lemma Property1: \forall AB X. \forall BC Y. \forall AC Z. \forall integer b. \forall integer ii. \forall integer jj.
			matrixColumn(X, Y, Z, b, ii, jj-b) && matrixBlock(X, Y, Z, b, ii, jj-b,COLUMN1)
		     ==> matrixColumn(X, Y, Z, b, ii, jj);
lemma Property2: \forall AB X. \forall BC Y. \forall AC Z. \forall integer b. \forall integer ii. 
			matrixRow(X, Y, Z, b, ii-b) && matrixColumn(X, Y, Z, b, ii-b, COLUMN2)
		     ==> matrixRow(X, Y, Z, b, ii);
// ��Ҫ�����������ԭ��ν��matrixRow��matrixColumn������������Ե�������ʽ���г������㡣
*/

AC Z;

/*@
requires \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b);
assigns Z;
ensures matrixMultiply(X, Y, Z, b);
*/
void MatrixMultiply(AB const X, BC const Y) {
    int i, j, l, ii, jj, ll;

    //@ ghost int s1, s2, s3;
    /*@ loop invariant \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b) &&
		0 <= ii <= ROW1 &&
		(\forall integer i1: [0..ii-1]. \forall integer j1: [0..COLUMN2-1]. Z[i1][j1] == 0);
    */
    for(ii = 0; ii < ROW1; ii=ii+1) {
	/*@ loop invariant \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b) &&
		    0 <= ii < ROW1 && 0 <= jj <= COLUMN2 &&
		    (\forall integer i1: [0..ii-1]. \forall integer j1: [0..COLUMN2-1]. Z[i1][j1] == 0) &&
		    (\forall integer j1: [0..jj-1]. Z[ii][j1] == 0);
	*/
	for(jj = 0; jj < COLUMN2; jj=jj+1) {
	    Z[ii][jj] = 0;
	}
    }
    //@ ghost s1 = 0;
    /*@ loop invariant \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b) &&
		(\forall integer i1: [ii..ROW1-1]. \forall integer j1: [0..COLUMN2-1]. Z[i1][j1] == 0) &&
		0 <= ii <= ROW1 && ii == b * s1 && matrixRow(X, Y, Z, b, ii);
    */
    for(ii = 0; ii < ROW1; ii = ii + b) {
	//@ ghost s2 = 0;
	/*@ loop invariant \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b) &&
		    (\forall integer i1: [ii..ii+b-1]. \forall integer j1: [jj..COLUMN2-1]. Z[i1][j1] == 0) &&
		    (\forall integer i1: [ii+b..ROW1-1]. \forall integer j1: [0..COLUMN2-1]. Z[i1][j1] == 0) &&
		    0 <= ii < ROW1 && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
		    0 <= jj <= COLUMN2 && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj);
	*/
	for(jj = 0; jj < COLUMN2; jj = jj + b) {
	    //@ ghost s3 = 0;
	    /*@ loop invariant \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b) &&
		    (\forall integer i1: [ii..ii+b-1]. \forall integer j1: [jj..COLUMN2-1]. Z[i1][j1] == 0) &&
		    (\forall integer i1: [ii+b..ROW1-1]. \forall integer j1: [0..COLUMN2-1]. Z[i1][j1] == 0) &&
		    0 <= ii < ROW1 && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
		    0 <= jj < COLUMN2 && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj) &&
		    0 <= ll <= COLUMN1 && ll == b * s3 && matrixBlock(X, Y, Z, b, ii, jj, ll);
	    */
	    for(ll = 0; ll < COLUMN1; ll = ll + b) {
		/*@ loop invariant \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b) &&
			(\forall integer i1: [ii..ii+b-1].\forall integer j1:[jj..COLUMN2-1].Z[i1][j1] == 0)&&
			(\forall integer i1: [ii+b..ROW1-1]. \forall integer j1: [0..COLUMN2-1]. Z[i1][j1] == 0) &&
			0 <= ii < ROW1 && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
			0 <= jj < COLUMN2 && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj) &&
			0 <= ll < COLUMN1 && ll == b * s3 && ii <= i <= ii + b <= ROW1 &&
			blockRow(X, Y, Z, b, ii, i-1, jj, ll+b) && blockRow(X, Y, Z, b, i, ii+b-1, jj, ll);
		*/
		for(i = ii; i < ii + b; i=i+1) {
		    /*@ loop invariant \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b) &&
			(\forall integer i1: [ii..ii+b-1].\forall integer j1:[jj..COLUMN2-1].Z[i1][j1] == 0) &&
			(\forall integer i1: [ii+b..ROW1-1]. \forall integer j1: [0..COLUMN2-1]. Z[i1][j1] == 0) &&
			0 <= ii < ROW1 && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
			0 <= jj < COLUMN2 && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj) &&
			0 <= ll < COLUMN1 && ll == b * s3 && ii <= i < ii + b <= ROW1 &&
			blockRow(X, Y, Z, b, ii, i-1, jj, ll+b) && blockRow(X, Y, Z, b, i+1, ii+b-1, jj, ll) &&
			jj <= j <= jj + b <= COLUMN2 &&
			blockColumn(X, Y, Z, i, jj, j-1, ll+b) && blockColumn(X, Y, Z, i, j, jj+b-1, ll);
		    */
		    for(j = jj; j < jj+b; j=j+1) {
			/*@ loop invariant \length(X) == ROW1 && \length(Y) == ROW2 && \length(Z) == ROW1 && blockSize(b) &&
		  	    (\forall integer i1: [ii..ii+b-1].\forall integer j1: [jj..COLUMN2-1]. Z[i1][j1] == 0) &&
			    (\forall integer i1: [ii+b..ROW1-1].\forall integer j1: [0..COLUMN2-1]. Z[i1][j1] == 0) &&
			    0 <= ii < ROW1 && ii == b * s1 && matrixRow(X, Y, Z, b, ii) &&
			    0 <= jj < COLUMN2 && jj == b * s2 && matrixColumn(X, Y, Z, b, ii, jj) &&
			    0 <= ll < COLUMN1 && ll == b * s3 && ii <= i < ii + b <= ROW1 &&
			    blockRow(X, Y, Z, b, ii, i-1, jj, ll+b) && blockRow(X, Y, Z, b, i+1, ii+b-1, jj, ll) &&
			    jj <= j < jj + b <= COLUMN2 &&
			    blockColumn(X, Y, Z, i, jj, j-1, ll+b) && blockColumn(X, Y, Z, i, j+1, jj+b-1, ll) &&
			    ll <= l <= ll + b <= COLUMN1 && blockElement(X, Y, Z, i, j, l);
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

