// We provide some code so one can see the result of applying Demazure operators to the staircase polynomial one-at-a-time.
// See ExoticNilcoxeterPresentation.m or VerificationMagic.m for comments on until otherwise stated. We annotate the major differences.

n := 3;

////////////////////
// To begin with, the reader can choose m here!
m := 5;

// The reader can choose their word here.
a := 7;
b := n*m-a-1;
i := 1;

////////////////////

SetAutoColumns( false );
SetColumns( 175 );


cw := function( i, l )
  return [ j mod n + 1 : j in [ i - 1 .. i + l - 2 ] ];
end function;

ccw := function( i, l )
  return [ -j mod n + 1 : j in [ - i + 1 .. - i + l ] ];
end function;

cwccwendi := function(a, b,i)
	return Reverse(cw(i,b) cat ccw(i+b,a+1));
end function;

////////////////
// This time we set our base ring to be the cyclotomic field, i.e. we have already specialized z to be a 3mth root of unity.
A< z > := CyclotomicField( n*m );
///////////////

R := PolynomialRing( A, n );
AssignNames(~R, [ "x" cat IntegerToString( i ) : i in [ 1 .. n ] ] );

x1 := R.1; x2 := R.2; x3 := R.3;

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

// DemazurePol takes a word w and a polynomial f and returns partial_w(f). It applies demazure operators from right to left as you should.
DemazurePol := function( w, f )
  local res, d, l; l := #w; res := f;
  for i in [ 1 .. l ] do res := demazure( w[l+1-i], res ); end for;
  return res;
end function;

DemazureOnMonomial := function(w, a, b, c)
   return DemazurePol(w, x1^a*x2^b*x3^c);
end function;

//////////////////
// New material begins here.

// MAGMA views the cyclotomic field as a quotient of a polynomial ring by a cyclotomic polynomial.
// Consequently, any element of the field is written as a polynomial in z, of degree less than that of the cyclotomic polynomial.
// Unfortunately, this means that even powers of z are not obviously notated as such, but can appear as complicated polynomials.
// For sanity, we start by printing to the screen the list of powers of z, so that the reader can compare coefficients against them.

powers := [ z^i : i in [ 1 .. m*n ] ];
Sprintf("Here are the powers of z: \n");
powers;
Sprintf("\n\n");

// The reader will note that, when m=5, all the coefficients in any power of z are in the set {-1,0,1}
// A consequence: If an element of the field is written as ... + 7 z^c + ... then,
// when writing this as a linear combination of powers of z, there must be at least 7 elements in the linear combination.


// Side note:
// If the reader ever gets sick of looking at elements of the cyclotomic field and trying to figure out if they are powers of z or not
// then this function Simplify should help. It takes an element c of the cyclotomic field, multiplies by all the powers of z, and
// returns the product cz^k which has the shortest string to print. It also returns the number k, so you can recover c.
// This is good for identifying powers of z, or scalars times powers of z, but not things like quantum numbers.

//  Simplify := function( c )
//	local list;
//	if c eq 0 then
//		return 0;
//	end if;
//	list := [ c * powers[i] : i in [ 1 .. #powers ] ];
//	lengths := [ #Sprint( i ) : i in list ];
//	min, pos := Minimum( lengths );
//	return [list[pos],pos];
//  end function;


/////////////////
// Set up the word based on parameters chosen earlier.
word := cwccwendi(a, b, i);
len := #word;

/////// 
// We start with the staircase and apply Demazure operators from the word one at a time. We keep track of the result as P.
staircase := x1^(2*m)*x2^m;
P := staircase;
Sprintf("Starting with the polynomial:");
P;

// We now apply the operators from right to left, as one should. We print j, which is how many operators we have applied so far, and then P after some processing.
for j in [ 1 .. #word ] do 
P := DemazurePol( [ word[len+1-j] ], P );
Sprintf("\n Number of simple Demazure operators applied so far: %o \n",j);

// If the reader just wants to see P, then uncomment the next line and comment what follows (don't comment the final end for;).
// P;

// What we print instead is all the terms of P which are not divisible by x_1 x_2 x_3. This eliminates most of the terms for high-degree polynomials, and such terms will never contribute to an eventual scalar. They are printed as a list, rather than a sum, for readability.

if P eq 0 then 0; 
else Terms( &+( [ m : m in Terms( P ) | not IsDivisibleBy( m, x1*x2*x3 ) ] ) ); 
end if; 


end for;


