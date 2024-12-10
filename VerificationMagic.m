// The purpose of this program is to verify a formula for
// Xi(a,b,i,k) = partial_w(x_1^k x_2^(len-k))
// where w is a word in the affine weyl group of type a_2. The word w depends on parameters (a,b,i)
// partial_w is the corresponding z-deformed demazure operator
// len is the length of w, so that the result is a scalar.

// This formula is complicated, describing Xi as a product of many individual factors.

// A second purpose is to verify a simplified formula for 
// xi(a,b,i) = partial_w(x_1^(2m) x_2^m)
// after z is specialized to a 3m-th root of unity.

// Chapter 1 of this program sets up the polynomial ring, defines demazure operators, and actually computes this scalar Xi.

// Chapter 2 of this program sets up the individual factors defined in the formula.

// Chapter 3 of this program builds the formula for the scalar. Note that there are a million edge cases to consider. This part of the code figures out which case you're in and uses the correct formula accordingly.

// Chapter 4 tests that the scalars computed in chapter 1 agree with the scalars given by the formula in Chapter 3. We fix a test range, and test all cases in this range.

// Chapter 5 introduces additional functions for the simplified formula at a root of unity.

// Chapter 6 tests the formula at a root of unity. We choose to test the formula at a root of unity against the ordinary formula (from Chapter 3) rather than the true computation (from Chapter 2), as it is much faster.

// In Chapter 0 there are several boolean variables which determine which part of the code to run. We also fix a test range.





// Chapter 0: setup

// These commands just make MAGMA output wider.
SetAutoColumns( false );
SetColumns( 175 );

// Set n. 
n := 3;
// Aside from chapter 1, we have made no attempt to generalize our code beyond n=3.


// CHAPTER 0.1: Printing options

// Here's what the code prints by default.
// Before beginning a testing loop (chapter 4, or chapter 6) it prints that it starts.
// if the formula is wrong (e.g. in Chapter 4, if Chapter 3 does not match Chapter 1), it will print some information. 
//         if the formula said zero but it wasn't, will say so, and print the actual answer.
//         otherwise, will print the true scalar divided by the formula. This will be zero only if the formula thought it was nonzero.
//         will also print the value of a, b, i, k.
// if the formula is right, it will increment a counter, and print the total number of correct checks at the end of the testing loop.

verbose := false;
// If verbose or veryverbose is true, it will also print the values of a, b, w, i, len every time one changes.

veryverbose := false;
// If veryverbose is true, then even if the formula is right, will either print "zero as expected" or will print the nonzero scalar.
// if the formula is wrong, will print the scalar and the ratio
// It will also indicate the value of k.


// CHAPTER 0.2: Testing ranges
// You can set the variables here to test certain ranges and special cases.

// Should we do chapter 4 at all?
checktheformula := true;
// Should we do chapter 6 at all?
checkrou := true;

// In chapter 4, we restrict to len being in this range.
lenrange := [1 .. 15];

// These booleans say which cases for k to do. The three cases are: 0 < k < len, k = len, and k = 0.
dokmain := true;
doklen := true;
dokzero := true;

// In chapter 6, where len = 3m, we restrict to m being in this range. lenrange is no longer relevant.
mrange := [3 .. 6];

// For both chapters 4 and 6, we restrict which words w(a,b,i) to investigate based on the following parameters.

// b is in this range. 
brange := [1 .. 10];
// Since len = a+b+1, this determines a.

// This boolean just says to check all possible values of b (given the booleans below) for the given length or value of m. In other words, it sets brange to [0 .. len-1]
doallb := true;

// i is in this range. Note that i is required to be either 1, 2, or 3.
irange := [1 .. 3];

// These booleans say whether to restrict based on the parity of b or len, or whether to touch the edge cases a=0 or b=0
// NOTE: if dobzero is true, then the case b=0 will be done, even if b=0 is not within brange.
doaeven := true;
doaodd := true;
doazero := true;
dobeven := true;
dobodd := true;
dobzero := true;











// CHAPTER 1: SETTING UP THE DEMAZURE CALCULATION



// CHAPTER 1.1: First we define the words we use.

// Note to reader: in MAGMA, k mod 3 is always a number between 0 and 2, while our indices are between 1 and 3.
// To go from k mod 3 to the corresponding index, one can do something like: ((k-1) mod 3) + 1.
// We use this indexing trick a few times below.

// Starts with i and goes clockwise, overall length is l. The input i need not be between 1 and 3.
cw := function( i, l )
  return [ j mod n + 1 : j in [ i - 1 .. i + l - 2 ] ];
end function;

// Starts with i and goes counterclockwise, overall length is l. The input i need not be between 1 and 3.
ccw := function( i, l )
  return [ -j mod n + 1 : j in [ - i + 1 .. - i + l ] ];
end function;

// In the paper we define a word w(a,b,i), of length a+b+1, which is:
// first clockwise for length a, ending in j
// then j+1
// then counterclockwise for length b, starting in j.
// It ends in the index i; the indices i and j determine each other.
// More precisely, j+1 = i + b mod n.
// This works even when a and/or b are zero.

cwccwendi := function(a, b,i)
	return Reverse(cw(i,b) cat ccw(i+b,a+1));
end function;



// CHAPTER 1.2: Set up the polynomial ring.

// Our base ring A is Q(p).
A<p> := FieldOfFractions(PolynomialRing(Rationals(), 1));
// Our poly ring R is A[x1, x2, x3]
R := PolynomialRing( A, n );
// We introduce some scalars which are powers of p for convenience. See the paper.
// These are global variables used in all functions.
q := p^(-n);
z := p^2;

// This is the p-antilinear automorphism of the base ring, sending p to its inverse. Think of it as complex conjugation.
bar := hom<A -> A| p^(-1)>;

// The goal of AssignNames is not to do anything effective, but only to change the way MAGMA prints its output. When printing it will now write "x1" rather than "R.1"
// This does not affect any of our outputs, but for readers wishing to explore Demazure operators where the result is not degree zero, it is very helpful.
AssignNames(~R, [ "x" cat IntegerToString( i ) : i in [ 1 .. n ] ] );



// CHAPTER 1.3: Set up Demazure operators.

// Set up a list of simple roots.
simple_roots := [ R.i - z*R.( i mod n + 1 ) : i in [ 1 .. n ] ];

// Now we set up the simple reflections using linear algebra. ss(i) is the matrix representing the i-th simple reflection on the basis x1, x2, ..., xn. 
// Note: MAGMA is smart enough to take this matrix and use it to define ring homorphisms from R to itself.
// So f^(ss(i)) would be the i-th simple reflection acting on a polynomial f.
// The affine reflection is ss(n).
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

// s is a list of simple reflections. s[i] is the i-th simple reflection matrix.
s := [ ss( i ) : i in [ 1 .. n ] ];

// demazure(k,f) takes an index k and a polynomial f and returns partial_k(f).
demazure := function( k, f )
  return  (f - f^s[k]) div simple_roots[k];
end function;

// DemazurePol takes a word w and a polynomial f and returns partial_w(f). It applies demazure operators from right to left as you should.
DemazurePol := function( w, f )
  local res, d, l; l := #w; res := f;
  for i in [ 1 .. l ] do res := demazure( w[l+1-i], res ); end for;
  return res;
end function;


// Now a couple lines assuming n=3.
// We give names to our variables for internal use as well. 
x1 := R.1; x2 := R.2; x3 := R.3;

// DemazureOnMonomial applies partial_w to the monomial x1^a x2^b x3^c.
DemazureOnMonomial := function(w, a, b, c)
   return DemazurePol(w, x1^a*x2^b*x3^c);
end function;



// Examples of computing demazure operators.
// word := cwccwendi(3, 5, 2);
// DemazureOnMonomial(word,4,7,0);
// DemazureOnMonomial(word,4,5,0);





// CHAPTER 2: DEFINING THE CRAZY FORMULA

// CHAPTER 2.1: Functions used in the formula

// rho(k) is the product for i from 1 to k of (q^i - q^(-i)).
// this is [k]! times a power of (q-q^(-1)).
// rhoalt(k) is the product of (1 - q^(-2i))
// Note that rho(0) = 1, and rho(k)= 0 for k<0.

rho := function(k)
    local res; res := 1;
    if (k lt 0) then
        return 0;
    end if;
    for i in [1 .. k] do
        res := res*(q^i-q^(-i));
    end for;
    return res;
end function; 


rhoalt := function(k)
    local res; res := 1;
    if (k lt 0) then
        return 0;
    end if;
    for i in [1 .. k] do
        res := res*(1-q^(-2*i));
    end for;
    return res;
end function; 

// The quantum number

quantum := function(k)
	return (q^k-q^(-k))/(q-q^(-1));
end function;

// The quantum binomial coefficient.
// We define the quantum binomial by taking ratios of [k]!, and we use rho as a replacement for [k]! since the powers of (q-q^(-1)) cancel out.
// Note that m choose k is zero when k is negative. When m is positive and k is bigger then m, it is also zero.
// But when m is negative it is never zero for positive k, and is equal to a sign times a binomial coefficient for some m positive.
// However, since rho(k) = 0 for k negative, when m is negative we jury rig the answer to be correct.

quantumbinomial := function(m,k) // m choose k
        if (k lt 0) then return 0;
        elif (m lt k) and (-1 lt m) then return 0;
        elif (-1 lt m) then
                return rho(m)/(rho(k) * rho(m-k));
        else
            return (-1)^k*rho(k-m-1)/(rho(k) * rho(-m-1));
        end if;
end function;

// The term from the magic function
magicterm := function(nu,k,beta,offset,j)
	return quantumbinomial(k-1,beta-j)*quantumbinomial(nu-k-1,j)*q^(j*(2*k-3*nu-2*offset));
end function;

// The magic function. It is a weird q-deformation of a binomial coefficient, similar to the sum appearing in the chu-vandermonde identity, but not the same.

magicbinomial := function(nu,k,beta, offset)
	local res;
	res := 0;
	for j in [0 .. beta] do
		res := res + magicterm(nu,k,beta,offset,j);
	end for;
	return res;
end function;


// EXAMPLES OF MAGIC
// magicbinomial(9,2,5,0);
// magicbinomial(9,3,5,0);
// magicbinomial(9,4,5,0);
// magicbinomial(9,3,5,-1);
// magicbinomial(10,3,5,0);
// for k in [1 .. 9] do k; magicbinomial(10,k,5,0); end for;


// CHAPTER 2.2: Setting up the scalars lambda, kappa, and gamma from the paper.

// LAMBDA

lambda1 := function(beta, len)
	return z^(Binomial(beta,2))*z^(-Binomial(len+1,2))*p^(-(beta+1)*(len+3*beta));
end function;

lambda2 := function(beta,a)
	local res;
	res := z^(beta);
	if IsEven(a) then res := z^(-beta-3); end if;
	return res;
end function;

lambda3 := function(beta,len,b)
	local res;
	res := 1;
	if IsOdd(b) then res := z^(len+1); end if;
	return res;
end function;

lambda4 := function(a, b, beta)
	local res;
	res := p^(-beta-3);
	if IsEven(a) then res := res * p^(beta+3); end if;
	if IsEven(b) then res := res * p^(beta+3); end if;
	return res;
end function;


lambda5 := function(i,len)
	local res;
	res := 1;
	if (i eq 2) then res := z^(len);
	elif (i eq 3) then res := z^(-len);
	end if;
	return res;
end function;

// KAPPA

kappa1 := function(beta,len,k)
	return z^k*q^(k*(k - beta - len));
end function;

kappa2 := function(i,k)
	local res;
	res := 1;
	if (i eq 2) then res := q^(2*k);
	end if;
	return res;
end function;

// THE SIGN mu

mu := function(beta,k)
	return (-1)^(beta+k);
end function;

// GAMMA

gamma1 := function(alpha,beta)
	return rhoalt(beta)*rhoalt(alpha);
end function;

gamma2 := function(a,b,i,k)
	local res, alpha, beta, nu, len;
	alpha := Quotrem(a-1,2);
	beta := Quotrem(b-1,2);
	nu := alpha + beta + 2;
	len := a+b+1;
	if (IsEven(a) and IsOdd(b)) then
		res := q^(-1*nu)*(q^(k-nu)-q^(nu-k));
	elif (IsOdd(a) and IsOdd(b)) then
		res := 1;
	elif (IsOdd(a) and IsEven(b)) then
		if (i eq 1) then
			res := q^(-1*nu)*(q^(nu-k)-q^(k-nu));
		elif (i eq 2) then
			res := q^(-1*(len-1))*(q^(len-1-k)-q^(k+1-len));
		elif (i eq 3) then
			res := q^(-1*(len-1))*(q^(1-k)-q^(k-1));
		end if;
	elif (IsEven(a) and IsEven(b)) then
		if (i eq 1) then
			res := q^(-1*len)*(q^(k-nu)-q^(nu-k))*(q^(nu+1-k) - q^(k-1-nu));
		elif (i eq 2) then
			res := q^(-1*(len+nu-1))*(q^(k-nu)-q^(nu-k))*(q^(len-1-k) - q^(k+1-len));
		elif (i eq 3) then
			res := q^(-1*(len+nu-1))*(q^(k-1)-q^(1-k))*(q^(nu+1-k) - q^(k-1-nu));
		end if;
	end if;
return res;
end function;

gamma3 := function(a,b,i,k)
	local res, alpha, beta, nu;
	alpha := Quotrem(a-1,2);
	beta := Quotrem(b-1,2);
	nu := alpha + beta + 2;
	
	if (IsEven(a) and IsOdd(b)) then
		res := magicbinomial(nu,k,beta,0);
	elif (IsOdd(a) and IsOdd(b)) then
		res := magicbinomial(nu,k,beta,-1);
	elif (IsOdd(a) and IsEven(b)) then
		if (i eq 1) then
			res := magicbinomial(nu,k,beta,0);
		elif (i eq 2) then
			res := magicbinomial(nu,k,beta,-1);
		elif (i eq 3) then
			res := q^(beta)*magicbinomial(nu,k-1,beta,-1);
		end if;
	elif (IsEven(a) and IsEven(b)) then
		if (i eq 1) then
			res := magicbinomial(nu,k,beta,+1);
		elif (i eq 2) then
			res := magicbinomial(nu,k,beta,0);
		elif (i eq 3) then
			res := q^(beta)*magicbinomial(nu,k-1,beta,0);
		end if;
	end if;
	return res;
end function;

///// FUNCTIONS FOR THE EDGE CASES

nabla := function(i,len)
	if (i eq 1) then return 1;
	elif (i eq 2) then return 0;
	elif (i eq 3) then return -z^(-len);
	end if;
end function;


// CHANGE THIS ONES NAME WHEN WE DECIDE

lambda7 := function(a,i,k)
	local len; len := a+1;
    if (i eq 1) and IsOdd(a) then
        return 0;
    elif (i eq 1) and IsEven(a) then
        return p^(-2*len);
    elif (i eq 2) and IsOdd(a) then
        return p^(-3*k);
    elif (i eq 2) and IsEven(a) then
        return p^(3*len-6*k-3);
    elif (i eq 3) and IsOdd(a) then
        return -p^(-len-3*k);
    elif (i eq 3) and IsEven(a) then
        return p^(-len-3);
end if;
end function;


// CHAPTER 2.3: Symmetries

// These functions just manipulate the index i to account for the action of certain symmetries.
// For example, the inverse of sigma sends w(a,b,i) to w(a,b,sigmainv(i)).
// See the paper, section 3.1.

sigmainv := function(i)
	if (i eq 1) then return 3;
	else return i-1;
	end if;
end function;

sitau := function(i)
	if (i eq 1) then return 1;
	elif (i eq 2) then return 3;
	elif (i eq 3) then return 2;
	end if;
end function;



// CHAPTER 3: DEFINING THE FORMULA IN EACH CASE

// Note: what are the special cases we need to keep track of?
// kmain means that k is not zero or equal to the length. Those two are special cases. However, one special case can be determined from the other using (rotational, sigma) symmetry, which is what we do here.
// b=0 is a special case.
// a=0 is a special case which can be determined from b=0 by symmetry, which is what we do here.
// These special cases combine, so k=0 and b=0 is a special special case.
// See section 3 from the paper for more details.

// The code itself does the following flow, to avoid calling too many functions for obvious answers:
// if length = 1, so a=b=0, it gives the immediate answer.
// if we're in a case guaranteed to be zero for some easy reason, it returns zero.
// otherwise, it checks if b is zero or not, and calls a function accordingly.
// within those functions (one for each b case), it checks if k=0 or k = len calls a function accordingly if so. Otherwise, it gives the resulting formula for the case 0<k<len.

// However, the functions below are defined in reverse order, from most obscure case to least obscure.
// MAGMA is happy to have functions call other functions if those other functions are defined first in the file, which explains the order we put the functions in.
// So the last function, scalarfunction, is the one which ultimately returns the scalar we seek!
// We strongly recommend reading from bottom to top, or comments are more confusing.


	

// klenbzerocase is the case when k=len and b=0. A very edgy case.

klenbzerocase := function(a,i,k) 
	local res, len, alpha, beta, nu, l7;
	len := a+1;
	res := 23000;
	if (k ne len) then
		Sprintf("k is wrong");
	elif (i eq 2) then
		Sprintf("Why am I here?");
		res := 0;
	else
		
		alpha := Quotrem(a, 2);
		// THIS VALUE OF ALPHA DISAGREES FROM THE MAIN CASE!!! 
		
		res := (-1)^a * nabla(i,len) * rhoalt(alpha)*z^(-Binomial(len,2));
	end if;
	return res;
end function;
	

// kmainbzerocase handles the case when a>0 and b=0. It calls another function if k=ell or k=0.

bzerocase := function(a,i,k)
	local res, len, alpha, beta, nu;
	len := a+1;
	res := 23000;
	if (k eq len) then
		res := klenbzerocase(a,i,len);
	elif (k eq 0) then
		res := klenbzerocase(a,sigmainv(i),len);
	
	// Now we're in the main case for k.
	elif (IsOdd(a) and (i eq 1)) then
		res := 0;
	else
    	beta := 0;
		alpha := Quotrem(a-1, 2);
		nu := alpha+beta+2;
		
		res := (-1)^(k+1)*q^(2*Binomial(k,2))*rhoalt(alpha)*z^(-Binomial(len,2))*p^(3*k*len-k)*lambda7(a,i,k);

	
	end if;
	return res;
end function;
		





// Now we handle the case a,b > 0 and k=len.
// This function should never be called when i=2 since the result is zero and this is handled earlier in the flow.

klencase := function(a,b,i,k)
	local res, len, alpha, beta, nu;
	len := a+b+1;
	res := 190000;
	if (k ne len) then
		Sprintf("k isnt len");
//	elif (a eq 0) or (b eq 0) then
//		Sprintf("wrong case");
	elif (i eq 2) then
		Sprintf("Why am I here?");
		res := 0;

	elif IsOdd(b) then
		res := 0;
	else
		alpha := Quotrem(a, 2); // THIS VALUE OF ALPHA DISAGREES FROM THE MAIN CASE!!! 
		beta := Quotrem(b-1, 2);
		nu := alpha+beta+2;
		
		res := (-1)^(beta + len)*rhoalt(alpha+1+beta)*nabla(i,len)*z^(-Binomial(len,2))*p^((2*len+beta)*(beta + 1));
	
	end if;
	return res;
end function;


// bmaincase is the case when $a,b > 0$.
// If k=len it calls the appropriate edge function.
// If k=0 it uses \eqref{sionXi} BE:REPLACE LATER and calls the appropriate special case function for k=len instead.
// Otherwise, it treats the standard regime as in the paper. BE:CITE THEOREM


bmaincase := function(a,b,i,k)
	local res, len;
	len := a+b+1;
	res := 23000;
	if (b eq 0) or (a eq 0) then
		Sprintf("case is wrong");
	elif (k eq len) then
		res := klencase(a,b,i,len);
	elif (k eq 0) then
		res := klencase(a,b,sigmainv(i),len);
	else
// STANDARD REGIME
		beta := Quotrem(b-1, 2);
		alpha := Quotrem(a-1, 2);
		nu := alpha+beta+2;
		
		l1:= lambda1(beta, len); 
		
		l2 := lambda2(beta,a);

		l3 := lambda3(beta, len, b); 	
		
		l4 := lambda4(a,b,beta);	

		l5 := lambda5(i,len);

		k1 := kappa1(beta,len,k);
		
		k2 := kappa2(i,k);
				
		sign := mu(beta,k);
		
		g1:= gamma1(alpha,beta);	

		g2 := gamma2(a,b,i,k);

		g3 := gamma3(a,b,i,k);
		
		res := l1*l2*l3*l4*l5*k1*k2*sign*g1*g2*g3;		
	end if;
	return res;
end function;	


		

/// FINALLY, here is the function which takes a,b,i,k, figures out what case you're in, and returns the ultimate scalar given by the formula.
// Within, it treats the special case a=b=0, i.e. len=1.
// It also treats the zero case.
// If $a=0$ but $b>0$ it applies symmetry, eqref{sitauonXi}. BE:FILL IN WITH CORRECT REFERENCE LATER
// If $b=0$ it calls the function where $b=0$.
// If $a, b > 0$ if calls the main case.
// Later it will be disambiguated whether $k$ is special.


scalarfunction := function(a,b,i,k)
	local res, len;
	len := a+b+1;
	res := 17000;
	if (a lt 0) or (b lt 0) then
		Sprintf("a or b is negative!");
	elif (len lt k) or (k lt 0) then
		Sprintf("k is out of range!");
	elif (i eq 2) and (k eq len) then
		res:=0;
	elif (i eq 3) and (k eq 0) then
		res:=0;
	elif (len eq 1) then
		if (i eq 2) and (k eq 0) then
			res:=1;
		elif (i eq 3) and (k eq 1) then
			res:=-z^(-1);
		elif (i eq 1) and (k eq 0) then
			res:=-z^(-1);
		elif (i eq 1) and (k eq 1) then
			res:=1;
		end if;
	elif (a eq 0) then
		res := (-z)^(-len)*bar(bzerocase(b,sitau(i),len-k));
	elif (b eq 0) then
		res:=bzerocase(a,i,k);
	else
		res:=bmaincase(a,b,i,k);
	end if;
	return res;
end function;
		
// INTERLUDE

// A function to decide based on booleans whether I should do this particular value of a and b.

dothiscase := function(b,len)
   local a, doit;
   a := len -1-b;
   doit := false;
   if ((b eq 0) and dobzero) or ((a eq 0) and doazero) then
      doit := true;
   elif (b lt (len-1)) and (b gt 0) then
   	  if ((dobodd and IsOdd(b)) or (dobeven and IsEven(b))) and ((doaodd and IsOdd(a)) or (doaeven and IsEven(a))) then
	     doit := true;
	  end if;
   end if;
   return doit;
end function;
	



// CHAPTER 4: TESTING THE FORMULA

// CHAPTER 4.1: Testing setup

if checktheformula then
numcorrect := 0;
Sprintf("Checking the formula");

// Do some conditional loops to make sure we're doing the correct set of tests.

for len in lenrange do
if (len eq 0) then
 Sprintf("len can't be zero");
else
  
// next we set up the range for b. If b=0 or a=0 wasn't already in there, add it. Later we'll check the boolean.
  truebrange := brange;
  if doallb then truebrange := [0 .. len-1]; end if;
  if (Index(truebrange,0) eq 0) then truebrange := [0] cat truebrange; end if;
  if (Index(truebrange,len-1) eq 0) then truebrange := truebrange cat [len-1]; end if;
  
  for b in truebrange do
   if dothiscase(b,len) then

   a := len-1-b;

 // Only doing the right values of a,b now.
	for i in irange do

// We're now looping over the correct words.	 
		word := cwccwendi(a, b, i);
		if (verbose or veryverbose) then Sprintf("length = %o, a = %o, b = %o, i = %o, word = %o\n", len, a, b, i, word); end if;

		for k in [0 .. len] do
		  if ((k eq 0) and dokzero) or ((k eq len) and doklen) or ((k gt 0) and (k lt len) and dokmain) then
// Now we're looping over the right values of k.


// CHAPTER 4.2: Do the testing.

							
			//Compute the true demazure scalar, and the guess from the formula
			scalar := DemazureOnMonomial(word,k,len-k,0);
			scalarguess := scalarfunction(a, b, i, k);
			
			// Check guess and print output

			if (scalarguess eq 0) and (scalar ne 0) then
				Sprintf("k = %o, predicted zero but %o \n",  k, scalar);
			
			elif (scalarguess eq 0) and (scalar eq 0) then
				numcorrect := numcorrect + 1;
			    if veryverbose then Sprintf("k = %o, zero as predicted \n", k); end if;
				
			elif (scalarguess eq scalar) then
				if veryverbose then	Sprintf("k = %o, formula correct, demazure = %o\n", k, scalar);
				end if;
				numcorrect := numcorrect + 1;
				
			else
	        	rescalar := scalar / scalarguess;
				if veryverbose then
					Sprintf("k = %o, demazure = %o, demazure over guess = %o \n", k, scalar, rescalar);
				else
					Sprintf("k = %o, demazure over guess = %o \n", k, rescalar);
				end if;			
			end if;
			
			
			
			
		  end if;
		end for;
		// End of loop on k
	
    end for;
	// end of loop on i
	
   end if;
  end for;
  // End of loop on b
  
 end if;
end for;
// end of loop on len
  
  
// CHAPTER 4.3: indicate glorious success.
Sprintf("Formula testing done, %o correct checks",numcorrect);

end if;
// end of checktheformula






// CHAPTER 5: Setup for checking a root of unity.
//
// We introduce functions involved in the simplified formula for xi at a root of unity.
// BE: CHANGE NAME LATER

blahblah := function(a,m)
	local b, beta, d;
	d := Quotrem(m,2);
	b := 3*m-a-1;
	beta := Quotrem(b-1,2);
	if IsEven(a) and IsOdd(b) then
		return p^(-2*beta^2-6*beta-4);
	elif IsOdd(a) and IsEven(b) then
		return p^(-2*beta^2-2*beta);
	elif IsOdd(a) and IsOdd(b) then
		return p^(-2*beta^2-3*beta-1);
	elif IsEven(a) and IsEven(b) then
		return p^(-2*beta^2-5*beta-3+3*d);
	end if;
end function;

InNonzeroRange := function(a,m)
	local ha, hb, b;
	b := 3*m-1-a;
	alpha := Quotrem(a-1,2);
	beta := Quotrem(b-1,2);
	if (alpha ge m) then
		return false;
	elif (beta ge m) then
		return false;
	else
		return true;
	end if;
end function;

FindBottom := function(a,m)
	local b,d;
	d := Quotrem(m,2);
	b := 3*m-a-1;
	if (IsOdd(a) and IsOdd(b)) then
		return d;
	else
		return d-1;
	end if;
end function;

// This is the function which returns the formula for xi(a,m). Note that we have not yet specialized p to a root of unity! (If we had, then the formula for quantum binomial coefficients will not work, as we often divide zero by zero.)

rouscalarfunction := function(a,m)
	local b,d,beta, alpha, bottom, sign, powerofq;
	if (not InNonzeroRange(a,m)) then
		return 0;
	else

	d := Quotrem(m,2);
	b := 3*m-a-1;
	alpha := Quotrem(a-1,2);
	beta := Quotrem(b-1,2);
	bottom := FindBottom(a,m);

	sign := (-1)^(d+a+beta);
	powerofq := q^(Binomial(d+1,2) - Binomial(alpha+1,2) - Binomial(beta+1,2));
	
	return sign*z^(2*m)*blahblah(a,m)*m^2*quantumbinomial(m-1-bottom,alpha - bottom)*powerofq;
	end if;
end function;


// CHAPTER 6: TESTING THE SIMPLIFIED FORMULA AT ROU
//
// 

// Chapter 6.1: Testing setup

if checkrou then
numcorrect := 0;
Sprintf("Checking at rou");


for m in mrange do
if (m lt 2) then
	Sprintf("m is too small");
else
// We're looping over the correct values of m.


len := 3*m;
k := 2*m;
d := Quotrem(m,2);

// Now we define a function specialize which specializes p to the appropriate root of unity.
C< zeta > := CyclotomicField( 6*m );
specialize := hom< A -> C | zeta >;

// Now we set up the proper range for a and b
// Note that we ignore any values not within the nonzero range
  truebrange := brange;
  if doallb then truebrange := [1 .. len-2]; end if;
  for b in truebrange do
   a := len-1-b;
   if InNonzeroRange(a,m) and dothiscase(b,len) then
// We're now doing the correct values of a and b within the nonzero range.  


// CHAPTER 6.2: Test the result

	guess := rouscalarfunction(a,m);
	for i in irange do
		if verbose or veryverbose then Sprintf("m = %o, a = %o, b = %o, i = %o", m, a, b, i); end if;
		trueanswer := scalarfunction(a,b,i,k);
		if (specialize(guess) eq specialize(trueanswer)) then
			numcorrect := numcorrect + 1;
			if veryverbose then Sprintf("rou formula correct, scalar = %o\n", guess); end if;
		else
			if veryverbose then Sprintf("formula wrong, formula = %o, ratio = %o\n", specialize(guess), specialize(guess)/specialize(trueanswer));
			else Sprintf("formula wrong, ratio = %o\n", specialize(guess)/specialize(trueanswer)); end if;
		end if;
	end for;
	// end of loop on i
	
// CHAPTER 6.3: indicate glorious success
	
end if; //dothiscase and InNonzeroRange
end for; // b

end if;
end for; // m

Sprintf("ROU Formula testing done, %o correct checks",numcorrect);

end if; //checkrou

