// The goal of this program is to compute a presentation for the exotic nilCoxeter algebra.
// First we set up the polynomial ring on which it acts, and the Demazure operators.
// We hard-code the braid relations and the roundabout relations, because when this is done we have a finite-dimensional algebra. This allows us to work with bases efficiently.
// Then in each degree we do linear algebra to search for relations. Then we add them to the algebra and repeat the process.


// Chapter 0: Setup

// These commands just make MAGMA output wider.
SetAutoColumns( false );
SetColumns( 0 );

// Choose n and m.
// Several things in this document are hard-coded for n=3 anyway.
n := 3;
m := 3;

// Note: this code exceeds the memory allocation for the free online magma calculator starting at m=7.

// If verbose is true, then we print various numerical data when computing the presentation.
// If very verbose is true, we print all sorts of data.

verbose := true;
veryverbose := false;

// Chapter 1: Cyclotomic field

// Our base ring A is the cyclotomic field Q(zeta), where zeta is a primitive nm-th root of unity.

A< z > := CyclotomicField( n * m );          // the variable z here matches zeta in the paper

// Here are some utility functions involving the cyclotomic field which we do not actually use in the rest of the program.

// Unbalanced quantum numbers
QuantumNumber := function( a )
	return ( z^(3*a) - 1 ) / ( z^3 - 1 );
end function;

QuantumFactorial := function( a )
	return a gt 0 select &*[ QuantumNumber( i ) : i in [ 1 .. a ] ] else 1;
end function;

QuantumBinomial := function( a, k )
	if k lt 0 or k gt a then
		return A!0;
	end if;
	return QuantumFactorial( a ) / ( QuantumFactorial( k ) * QuantumFactorial( a - k ) );
end function;

// When staring at an element of A, it is very hard to determine whether it is a power of z.
// But by enumerating the powers and searching for the element within the list, one can figure it out efficiently!
// Similarly, is an element equal to a quantum number times a power of z? Just multiply by all powers of z, and see if you get 1+z^3.

powers := [ z^i : i in [ 0 .. m*n - 1 ] ]; 


// The Simplify function takes an element of A (viewed as a polynomial in z) and multiplies it by all powers of z, choosing the result which can be printed out with the least characters! It then returns that short result, as well as the power of z needed to get there. 
// For example, if you started with a power of z, the output will be 1.
// And if you start with a power of quantum 2, the output will be 1+z^3 (except for small values of m where 1+z^3 simplifies further).

Simplify := function( c )
	local list;
	if c eq 0 then
		return 0;
	end if;
	list := [ c * powers[i] : i in [ 1 .. #powers ] ];
	lengths := [ #Sprint( i ) : i in list ];
	min, pos := Minimum( lengths );
	return list[pos], pos;
end function;




// Chapter 2: Polynomial ring and its symmetries

// Our poly ring R is A[x1, x2, x3]
R := PolynomialRing( A, n );

// The goal of AssignNames is not to do anything effective, but only to change the way MAGMA prints its output. When printing it will now write "x1" rather than "R.1"
// This does not affect any of our outputs, but for readers wishing to explore Demazure operators where the result is not degree zero, it is very helpful.
AssignNames(~R, [ "x" cat IntegerToString( i ) : i in [ 1 .. n ] ] );

// Hardcoded variable names for sanity when n=3. We don't use them.
x1 := R.1; x2 := R.2; x3 := R.3;

// Now we set up the simple reflections using linear algebra. ss(i) is the matrix representing the i-th simple reflection on the basis x1, x2, ..., xn. 
// Note: MAGMA is smart enough to take this matrix and use it to define ring homorphisms from R to itself.
// So f^(ss(i)) would be the i-th simple reflection acting on a polynomial f.
// The affine reflection is ss(n).

J := PermutationMatrix( A, [ 2 .. n ] cat [ 1 ] );			// matrix of the n-cycle
C := 2 * IdentityMatrix( A, n ) - z * J - z^-1 * J^-1;		// quantum Cartan matrix of type affine A_{n-1}

simple_roots := [ R.i - z*R.( i mod n + 1 ) : i in [ 1 .. n ] ];

ss := function( i )
  local mat;
  mat := IdentityMatrix( A, n );
  if i lt n then
    mat[i][i] := 0; mat[i+1][i+1] := 0; mat[i+1][i] := z^-1; mat[i][i+1] := z;
    return mat;
  end if;
  mat[n][n] := 0; mat[1][1] := 0; mat[1][n] := z^-1; mat[n][1] := z;
  return mat;
end function;

s := [ ss( i ) : i in [ 1 .. n ] ]; // a list of the simple reflections

// MAGMA has different kinds of groups on which one can perform different operations. Below G will be a group of matrices, while GG while be a group with a presentation. Both should be the complex reflection group acting on R.

G := MatrixGroup< n, A | s >;		// G( m, m, n ) as a matrix group, with generators s
GG,phi := FPGroup( G );				// phi: GG -> G is an isomorphism from a finitely presented group 

// Let's encode the sign representation.
GL1 := GeneralLinearGroup( 1, A ); 
I := IdentityMatrix( A, 1 );
sign := hom< G -> GL1 | [ -I, -I, -I ] >;

Sign := function( g )
  return Trace( sign( g ) );
end function;

// Now we can antisymmetrize a polynomial.
Antisym := function( f ) 
  return &+[ Sign( g ) * f^g : g in G ];
end function;

// We can also divide by disc, the product of all the "positive" roots.
roots := &cat[ &cat[ [ R.i - z^(l*n + k) * R.(i + k) : l in [ 0 .. m - 1 ] ] : k in [ 1 .. n - i ] ] : i in [ 1 .. n - 1 ] ];
disc := &*roots;

// For example, the following statement should evaluate to true
// Antisym( x1^(2*m) * x2^m ) div disc eq m^2;





// Chapter 3: Demazure operators


demazure := function( k, f )				// demazure( k, f ) is the k-th Demazure operator applied to the polynomial f
  return ( f - f^s[k] ) div simple_roots[k];
end function;

// DemazurePol takes a word w and a polynomial f and returns partial_w(f). It applies demazure operators from right to left as you should.
DemazurePol := function( w, f )
  local res, d, l; l := #w; res := f;
  for i in [ 1 .. l ] do res := demazure( w[l+1-i], res ); end for;
  return res;
end function;

// Apply Demazure operator of word w to a monomial.
DemazureOnMonomial := function(w, a, b, c)
   return DemazurePol(w, x1^a*x2^b*x3^c);
end function;


// maxdegree is the maximal degree of a generator of R over the invariant subring.
maxdegree := Binomial(n,2)*m;


// <<Brief discussion of what comes next:
// Our goal is to find relations between Demazure operators associated to words.
// A priori, one should view a Demazure operator as a matrix, and look for linear relations between these matrices.
// Since Demazure operators are homogeneous, we can lower the dimensions of matrices by studying this problem degree by degree.
// So, for each word w of length ell and each degree d, we want to encode the demazure operator of w, viewed as an operator from polynomials of degree d to degree d-ell. One might call this matrix M(w,d). Then we look for linear relations \sum a_w M(w,d) = 0, ranging over w of the same length, which hold simultaneously for all d.
// We need not consider d>maxdegree, because R is generated over R^W in smaller degrees. So this is a finite amount of work.
// We encode M(w,d) as a matrix. The basis of the source and target vector spaces is the basis of monomials in that degree, created automatically by MAGMA for polynomial rings.

// For technical reasons we use transpose matrices, so that vectors appear as row vectors, and are more easily dealt with later when we take kernels to find relations. Probably this is just a bad hack because we're not good at MAGMA.

// To construct the matrix for a word, we need to compose many individual operators. Each operator is itself a matrix, and this matrix multiplication is massively time-consuming, the largest barrier for scaling m.
// In the code below we use a very very important trick! Matrix multiplication may be associative, but the time it takes to multiply is NOT associative.
// Suppose we multiply matrices MNP, corresponding to linear maps $P: A^{n_1} \to A^{n_2}, N: A^{n_2} \to A^{n_3}, M: A^{n_3} \to A^{n_4}$, and suppose that the dimensions $n_i$ are decreasing, with $n_1 > n_2 > n_3 > n_4$. Then it is much faster to compute (MN)P than to compute M(NP). One should try to keep dimensions as small as possible when multiplying.
// The amount of runtime this saves is staggering.
// End discussion>>


// Now we construct  ds, which will contain matrices for Demazure operators from degree 1 to 0, 2 to 1, etc, up to maxdegree to (maxdegree - 1)
// more precisely, ds[k] will contain the list of (transpose) matrices for the k-th Demazure operator
// so ds[k][i] is the action of partial_k from degree i to degree i-1 (but transposed).

fooM := IdentityMatrix( A, n ) - z^-1*J;		// auxiliary matrix containing the information: Demazure operators from degree 1 to degree 0.


ds := [ [* Transpose( Matrix( fooM[i] ) ) *] : i in [ 1 .. n ] ];   // ds[k][1] is now correct.

// since multivariate polynomials are given by lists of monomials and coefficients, we need to decompose them in the monomial basis to get vectors
// This function takes a polynomial and the degree it lives in, and encodes it as a vector. 

PolynomialToVector := function( f, d )
  local coefs, mon, L, N, v;
  coefs, mon := CoefficientsAndMonomials( f );
  L := MonomialsOfDegree( R, d );
  N := #L;
  v := [ Zero( A ) : i in [ 1 .. N ] ];
  if f eq 0 then return v; end if;
  for i in [ 1 .. #mon ] do
	  v[Position( L, mon[i] )] := coefs[i];
  end for;
return v;
end function;

// conversely, we can convert a vector to a polynomial

VectorToPolynomial := function( v, d )
  local L, N;
  L := MonomialsOfDegree( R, d );
  N := #L;
  return &+[ v[i] * L[i] : i in [ 1 .. N ] ];  
end function;

// now we compute the matrices for Demazure operators between successive degrees up to maxdegree, and append them to ds

for d in [ 2 .. maxdegree ] do
  L := MonomialsOfDegree( R, d );
  for k in [ 1 .. n ] do
	  Append( ~ds[k], Matrix( [ PolynomialToVector( demazure( k, f ), d - 1 ) : f in L ] ) );
  end for;
end for;

// Let w be a word of length l(w), and d be a degree. Let partial_w be the demazure operator for w.
// Demazure( w, d ) computes the (transpose) matrix of partial_w from degree d to d - l(w).
// By the trick we discussed above, massive time is saved by computing these matrix compositions in reverse order from how one would normally compose functions.
// That is, we deal with the operators in lowest degree first.
// The matrix multiplication is reversed to what one expects because of the transpose.

Demazure := function( w, d )
  local res, l;
  l := #w;
  res := ds[w[1]][d + 1 - l];
  for i in [ 2 .. l ] do res := ds[w[i]][d - l + i] * res; end for;
  return res;
end function;

// Note: if you're going to be computing a lot with Demazure operators for large m, and time but not space is the constraint, then you should perform this matrix multiplication once and for all and memoize the answer (keep track of the matrices in a hash). We didn't.

// Applying a demazure operator to a single polynomial should be much less time consuming, since one need not keep track of entire matrices.
// Here is the LEAST EFFICIENT way to compute the demazure operator on a polynomial, unless you've already memoized the answer to Demazure.

DemazurePolAlt := function( w, f )
  local d;
  d := Degree( f );
  return VectorToPolynomial( Vector( PolynomialToVector( f, d ) ) * Demazure( w, d ), d - #w ); 
end function;





// Chapter 4: Setting up the algebra

// We start with a free algebra FA. 

FA<[d]> := FreeAlgebra( A, n );


// Define the braid relations (they are nonstandard, with a factor of z)

braid_rels := [ d[2]*d[1]*d[2] - z*d[1]*d[2]*d[1], d[3]*d[2]*d[3] - z*d[2]*d[3]*d[2], d[1]*d[3]*d[1] - z*d[3]*d[1]*d[3] ];

// Now define the roundabout relations, both clockwise and counterclockwise.

// Begin by defining clockwise and counterclockwise words. They start with i and have length l.

cw := function( i, l )
  return [ j mod n + 1 : j in [ i - 1 .. i + l - 2 ] ];
end function;

ccw := function( i, l )
  return [ -j mod n + 1 : j in [ - i + 1 .. - i + l ] ];
end function;

roundabout_rels := [
&*[ d[i] : i in cw( 1, 2*m ) ] + z^m * &*[ d[i] : i in cw( 2, 2*m ) ] + z^(2*m) * &*[ d[i] : i in cw( 3, 2*m ) ],
&*[ d[i] : i in ccw( 1, 2*m ) ] + z^m * &*[ d[i] : i in ccw( 2, 2*m ) ] + z^(2*m) * &*[ d[i] : i in ccw( 3, 2*m ) ]
 ];

// Here are all the standard relations (quadratic, braid, roundabout) put together.

original_relations := [ x^2 : x in d ] cat braid_rels cat roundabout_rels;

// Now let QA be the quotient of FA by these relations. There is a well-defined Demazure operator for each element of QA.

IA := ideal< FA | original_relations >;
QA<[e]> := quo< FA | IA >;

// This code builds a basis of QA consisting of monomials.
// M is the maximal degree of an element in QA.

// Note: basis is already a basis of QA consisting of monomials, but each monomial is expressed in the form e[1]*e[2]*e[1]*e[3]. So basis is a long list of such monomials.
// monomial_basis instead rewrites each monomial as a list [1,2,1,3]. This is now compatible with being plugged into our Demazure operator code above.
// meanwhile, monomial_basis_by_degree is a list of lists, where the i-th list is the monomials in degree i.

// To avoid dealing with the empty list, we ignore degree zero.

V,psi := VectorSpace( QA );
basis := Basis( V )@@psi;
// basis_by_degree := [ [ m : m in basis | Degree( m ) eq i ] : i in [ 1 .. M ] ];
monomial_basis := [ [ Position( e, basis[j][i] ) : i in [ 1 .. Length( basis[j] ) ] ] : j in [ 1 .. #basis ] ];
M:= #monomial_basis[#monomial_basis];
monomial_basis_by_degree := [ [ m : m in monomial_basis | #m eq i ] : i in [ 1 .. M ] ];

// The reader who wants to see the basis should write
// monomial_basis_by_degree;

if (verbose or veryverbose) then Sprintf("n = %o, m = %o.\n", n,m); end if;

if (verbose) then Sprintf("Imposing standard and roundabout relations, here is the number of surviving elements in QA in each degree, starting in degree 1.\n");
[ #i : i in monomial_basis_by_degree ];
end if;





// Chapter 5: finding more relations
// The way in which we find relations is as follows.

// Start looking for relations in degree L. In theory we could start with L=1, but this would waste time. Relations don't start appearing until degree 3m-D for relatively small D.
// When 2 <= m <= 5, D = 1. When 6 <= m <= 13, D = 2. When 14 <= m <= 20, D=3. This is as far as we have gone.
// For sanity we start with D=6. If you find no relations in degree 3m-D, then there were no relations in lower degree either.

// To find a relation, we want a linear combination of Demazure operators (associated to elements of QA) which kills all polynomials.
// We need not check ALL polynomials, since all Demazure operators are linear over R^W, so we need only check a basis of R over R^W. 
// Instead, we just check all monomials of R of degree at most N = 3m. This will contain a basis for R over R^W.
// Of course, when applying a word of length L, the result is zero for monomials in R of degree < L. So we only need to check monomials of degrees between L and N.

// Now take all the elements of length L in the monomial basis for QA defined above.
// We have computed the matrices for how these Demazure operators act on polynomials of a given degree i.
// Take this matrix and view it as a vector (that's what ElementToSequence does).
// Combine these vectors into a big matrix and find its kernel K. Each row of K is a new relation.
// This will be those linear combinations of Demazure operators which act trivially on degree i.
// Intersect these kernels for all L <= i <= N, and you have the linear combos in degree L which act by zero.
// Congrats, you found some new relations.

// Of course, relations in degree L will give rise to many linear combos that act by zero in degree L+1, but these shouldn't be new relations.
// So we should add a basis for the kernel to the list of relations, recompute the algebra QA and its basis, and then continue the computation in degree L+1.
// Now we'll only get new relations if they are algebraically independent of the old ones.

// Repeating this process for all L between 3m-D and 3m, we will have found all relations.

// Reading the verbose comments will guide you through the code below, but we added a few additional comments.


D := 6;
N := 3*m;
L := 3*m - D;
if (L le 3) then L := 4; end if;
relations := [];

if (verbose or veryverbose) then Sprintf("n = %o, m = %o.\n", n,m); Sprintf("Starting to look for relations in degree %o.\n",L); end if;

while L le N do
if (veryverbose) then Sprintf("Current degree: %o.\n",L);  end if;
K := KernelMatrix( HorizontalJoin( < Matrix( [ ElementToSequence( Demazure( w, i ) ) : w in monomial_basis_by_degree[L] ] ) : i in [ L .. N ] > ) );
// This is the kernel, but it is a matrix of numbers (the coefficients of certain words).
if NumberOfRows( K ) eq 0 then
  if (verbose or veryverbose) then Sprintf("No relations in degree %o.\n", L); end if;
  L := L + 1;
else
new_relations := [
&+[ K[j][i] * &*[ d[k] : k in monomial_basis_by_degree[L][i] ] : i in [ 1 .. #monomial_basis_by_degree[L] ] ] : j in [ 1 .. NumberOfRows( K ) ]
];
// The above line takes K and rewrites it in as a linear combination of elements of QA.
if (verbose) then Sprintf("There are %o new relations in degree %o.\n",#new_relations,L); end if;
if (veryverbose) then Sprintf("The new relations in degree %o are:\n",L); new_relations; end if;

//Now add the new relations to the existing relations, and recompute the algebra, starting from the free algebra and imposing all the relations.
relations := relations cat new_relations;
// The code below is same as above.
IA := ideal< FA | relations cat original_relations >;
QA<[e]> := quo< FA | IA >;
V,psi := VectorSpace( QA );
basis := Basis( V )@@psi;
// basis_by_degree := [ [ m : m in basis | Degree( m ) eq i ] : i in [ 1 .. M ] ];
monomial_basis := [ [ Position( e, basis[j][i] ) : i in [ 1 .. Length( basis[j] ) ] ] : j in [ 1 .. #basis ] ];
M:= #monomial_basis[#monomial_basis];
monomial_basis_by_degree := [ [ m : m in monomial_basis | #m eq i ] : i in [ 1 .. M ] ];
if (verbose) then Sprintf("Here is the number of surviving elements in QA in each degree, starting in degree 1.\n");
[ #i : i in monomial_basis_by_degree ];
end if;
if (veryverbose) then Sprintf("Here is the basis of QA in each degree, starting in degree 1.\n");
monomial_basis_by_degree;
end if;

L := L + 1;
end if;
end while;

if (verbose or veryverbose) then Sprintf("We're done finding relations. \n Here is a word in top degree. \n"); 
// The following list should have length 1, being the only survivor in top degree.
monomial_basis_by_degree[#monomial_basis_by_degree];
end if;

if (veryverbose) then Sprintf("The most recent basis is a basis for the exotic nilCoxeter algebra."); end if;

Sprintf("Here are all the additional relations.");
relations;

