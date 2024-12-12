// We verify that the quotient of NC(2,2,3) by the left ideal of gamma has graded dimension pi, see Lemma 6.3.
// This is only used to justify one statement in an example, and we have not paid as much attention to style here as in the other files.
// However, it is hard to construct left modules in MAGMA, so the code at the end where we do so may be quite useful.
// Most of the code below is duplicated from ExoticNilcoxeterPresentation.m until otherwise stated.
// See ExoticNilcoxeterPresentation.m for comments. We annotate the differences.

n := 3;

SetAutoColumns( false );
SetColumns( 175 );

////////////////////
// We must set m = 2.
m := 2;
////////////////////

////////////////
// This time we set our base ring to be the cyclotomic field, i.e. we have already specialized z to be a 3mth root of unity.
A< z > := CyclotomicField( n*m );
///////////////

R := PolynomialRing( A, n );
AssignNames(~R, [ "x" cat IntegerToString( i ) : i in [ 1 .. n ] ] );

x1 := R.1; x2 := R.2; x3 := R.3;

J := PermutationMatrix( A, [ 2 .. n ] cat [ 1 ] );			// matrix of the n-cycle
C := 2 * IdentityMatrix( A, n ) - z * J - z^-1 * J^-1;		// quantum Cartan matrix of type affine A_{n-1}


simple_roots := [ R.i - z*R.( i mod n + 1 ) : i in [ 1 .. n ] ];
ss := function( i )
  local mat;
  mat := IdentityMatrix( A, n );
  if i lt n then
    mat[i][i] := 0; mat[i+1][i+1] := 0; mat[i+1][i] := 1/z; mat[i][i+1] := z;
    return mat;
  end if;
  mat[n][n] := 0; mat[1][1] := 0; mat[1][n] := 1/z; mat[n][1] := z;
  return mat;
end function;

s := [ ss( i ) : i in [ 1 .. n ] ];

demazure := function( k, f )
  return  (f - f^s[k]) div simple_roots[k];
end function;

DemazurePol := function( w, f )
  local res, d, l; l := #w; res := f;
  for i in [ 1 .. l ] do res := demazure( w[l+1-i], res ); end for;
  return res;
end function;

DemazureOnMonomial := function(w, a, b, c)
   return DemazurePol(w, x1^a*x2^b*x3^c);
end function;

maxdegree := Binomial(n,2)*m;

fooM := IdentityMatrix( A, n ) - z^-1*J;		// auxiliary matrix containing the information: Demazure operators from degree 1 to degree 0.


ds := [ [* Transpose( Matrix( fooM[i] ) ) *] : i in [ 1 .. n ] ];   // ds[k][1] is now correct.

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

VectorToPolynomial := function( v, d )
  local L, N;
  L := MonomialsOfDegree( R, d );
  N := #L;
  return &+[ v[i] * L[i] : i in [ 1 .. N ] ];  
end function;


for d in [ 2 .. maxdegree ] do
  L := MonomialsOfDegree( R, d );
  for k in [ 1 .. n ] do
	  Append( ~ds[k], Matrix( [ PolynomialToVector( demazure( k, f ), d - 1 ) : f in L ] ) );
  end for;
end for;


Demazure := function( w, d )
  local res, l;
  l := #w;
  res := ds[w[1]][d + 1 - l];
  for i in [ 2 .. l ] do res := ds[w[i]][d - l + i] * res; end for;
  return res;
end function;


//////////

FA<[d]> := FreeAlgebra( A, n );



braid_rels := [ d[2]*d[1]*d[2] - z*d[1]*d[2]*d[1], d[3]*d[2]*d[3] - z*d[2]*d[3]*d[2], d[1]*d[3]*d[1] - z*d[3]*d[1]*d[3] ];

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

original_relations := [ x^2 : x in d ] cat braid_rels cat roundabout_rels;

IA := ideal< FA | original_relations >;
QA<[e]> := quo< FA | IA >;


V,psi := VectorSpace( QA );
basis := Basis( V )@@psi;
// basis_by_degree := [ [ m : m in basis | Degree( m ) eq i ] : i in [ 1 .. M ] ];
monomial_basis := [ [ Position( e, basis[j][i] ) : i in [ 1 .. Length( basis[j] ) ] ] : j in [ 1 .. #basis ] ];
M:= #monomial_basis[#monomial_basis];
monomial_basis_by_degree := [ [ m : m in monomial_basis | #m eq i ] : i in [ 1 .. M ] ];

D := 6;
N := 3*m;
L := 3*m - D;
if (L le 3) then L := 4; end if;
relations := [];

while L le N do
K := KernelMatrix( HorizontalJoin( < Matrix( [ ElementToSequence( Demazure( w, i ) ) : w in monomial_basis_by_degree[L] ] ) : i in [ L .. N ] > ) );
if NumberOfRows( K ) eq 0 then
  L := L + 1;
else
new_relations := [
&+[ K[j][i] * &*[ d[k] : k in monomial_basis_by_degree[L][i] ] : i in [ 1 .. #monomial_basis_by_degree[L] ] ] : j in [ 1 .. NumberOfRows( K ) ]
];
// The above line takes K and rewrites it in as a linear combination of elements of QA.

relations := relations cat new_relations;
IA := ideal< FA | relations cat original_relations >;
QA<[e]> := quo< FA | IA >;
V,psi := VectorSpace( QA );
basis := Basis( V )@@psi;
monomial_basis := [ [ Position( e, basis[j][i] ) : i in [ 1 .. Length( basis[j] ) ] ] : j in [ 1 .. #basis ] ];
M:= #monomial_basis[#monomial_basis];
monomial_basis_by_degree := [ [ m : m in monomial_basis | #m eq i ] : i in [ 1 .. M ] ];

L := L + 1;
end if;
end while;














// Done copying stuff from ExoticNilcoxeterPresentation.m


///////////////////
///////////////////
///////////// HELLO AGAIN!
///////////////////
///////////////////

// We have now constructed QA = NC(2,2,3) just as in ExoticNilcoxeterPresentation.m
// Constructing left modules over it is surprisingly thorny in MAGMA, though we are not experts.
// If someone knows a better way to do it, that would be helpful.

//////////////////////////////////////

// Keep track of the degrees of the basis of QA as a long list, e.g. 0,1,1,1,2,2,2,2,2,2,...
deg := [0] cat [ #i : i in &cat( monomial_basis_by_degree ) ];

// This is the automorphism sigma
sigma := hom< QA -> QA | [e[2],e[3],e[1]] >;

// This is a quick hack to compose two demazure operators at once.
ee := function( l ) return &*[ e[i] : i in l ]; end function;

// Here is the element gamma
gamma := ee([2,1]) - z*ee([3,2]) + z^2*ee([1,3]) - z^2*ee([3,1]) + z*ee([2,3]) - ee([1,2]);

// We verify that gamma is an eigenvector for sigma.
Sprintf("Is gamma an eigenvector for sigma?");
sigma( gamma ) eq z^2*gamma;

//gamma2 := dd([2,1]) - z*dd([3,2]) + z^2*dd([1,3]) - z^2*dd([3,1]) + z*dd([2,3]) - dd([1,2]);

// There are different kinds of algebras in MAGMA. QA was in the finitely presented algebra class. We now define QAass, an associative algebra.
QAass, a := Algebra( QA );
// The function RegularRepresentation does not produce a left module. It produces a subalgebra of matrices, the image of the algebra acting on the regular representation.
QAmat, r := RegularRepresentation( QAass );
// RModule now turns it into a left module
QAreg := RModule( QAmat );

// We coerce gamma to live in QAass and to act on the regular representation.
gammaAss := QAass!a(gamma);
gammaReg := QAreg![ gammaAss[i] : i in [ 1 .. 36 ] ];

// Now we take the quotient in left module context of the ideal generated by gammaReg. pq is the name of the quotient map, and Q the name of the quotient.
Q,pq := quo< QAreg | gammaReg >;

Sprintf("What are the degrees of the basis elements in the quotient by the left ideal of gamma?");
[ deg[j] : j in [ Position( Basis( QAreg ), Q.i@@pq ) : i in [ 1 .. Dimension( Q ) ] ] ];

// The above line uses a hack: it takes a basis element of Q and lifts it to an element of QA (that's what @@pq does).
// Thanks to the good graces of MAGMA, this happens to be a basis element of QA.
// We already know the degrees of basis elements of MAGMA, in the list deg constructed earlier.
// So we look up which basis element of QA we get, and then look up its degree.

// The commented line below verifies the good graces of MAGMA. 
// Basis( Q )@@pq;
