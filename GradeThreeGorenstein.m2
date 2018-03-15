-- To do list:

-- 1. Tweak beMatrix to work over ZZ/2.
-- 2. 
-- 3. 
-- 4. 
-- 5. 

-----------------------------------------------------------------------------
-- PURPOSE : The BEMatrix package for Macaulay2 computes a Buchsbaum-Eisenbud
-- matrix for a homogeneous grade three Gorenstein ideal in a polynomial
-- ring.
--
-- Copyright (C) 2018 Brett Barwick
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the GNU General Public License version 2
-- as published by the Free Software Foundation.--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
-----------------------------------------------------------------------------

newPackage(
	"GradeThreeGorenstein",
    	Version => ".5", 
    	Date => "March 14, 2018",
    	Authors => {{Name => "Brett Barwick", Email => "bbarwick@uscupstate.edu", HomePage => "http://faculty.uscupstate.edu/bbarwick/"}},
    	Headline => "computations involving homogeneous grade three Gorenstein ideals in polynomial rings",
	PackageExports => {"Depth"},
	DebuggingMode => false
    	)

export {

-- Options
     "CheckGorenstein",
--     "CheckUnimodular",
     
-- Helper methods
--     "numMonomials",
     "signedPfaffians",
     "isGorMinGenDegSeq",
     "randomGorMinGenDegSeq",
     "codimThreeGorBetti",
     "genericGorSyzMatrix",
     "beMatrix"
          
-- Main methods for QuillenSuslin algorithm
--     "changeVar",
--     "computeFreeBasis"
     
}

------------------------------------------------------------
-- Small helper methods ------------------------------------
------------------------------------------------------------

-- Method: signedPfaffians
-- Input: Matrix -- A matrix M of size (2n+1) x (2n+1) over a ring R.
-- Output: List -- An ordered list of the signed sub-maximal (2n x 2n) pfaffians of M.
signedPfaffians = method();
signedPfaffians(Matrix) := M -> (
    local m; local n;
    m = numrows M;
    n = numcols M;
    
    -- Check that the given matrix is actually skew-symmetric with an odd number
    -- of rows and columns.
    if (m != n) then error "Error: Expected a square matrix.";
    if (M + transpose(M) != 0) then error "Error: Expected a skew-symmetric matrix.";
    if not odd m then error "Error: Expected an odd number of rows and columns.";
    
    -- If the matrix is skew-symmetric with an odd number of rows and columns,
    -- use the existing 'pfaffians' command in M2 to compute the pfaffians of
    -- the principal (n-1) x (n-1) skew-symmetric submatrices and affix signs
    -- as appropriate.
    return apply(m, i -> if submatrix'(M,{i},{i}) == 0 then 0 else (-1)^i*(gens pfaffians(n-1,submatrix'(M,{i},{i})))_(0,0));
)

-- Method: numMonomials
-- Input: (ZZ,ZZ) -- The degree d of the monomials in a polynomial ring in n variables.
-- Output: ZZ -- The number of monomials of degree d in a polynomial ring in n variables.
numMonomials = method();
numMonomials(ZZ,ZZ) := (d,n) -> (
     return binomial(n+d-1,d);
)

-- Method: isGorMinGenDeqSeq
-- Input: List -- A non-decreasing list of positive integers representing a possible degree sequence for
-- a set of minimal generators for a homogeneous grade three Gorenstein ideal.
-- Output: Boolean -- Whether there exists a homogeneous grade three Gorenstein ideal
-- minimally generated in these degrees.  See Susan Diesel's paper 'Irreducibility
-- and Dimension Theorems for Families of Height 3 Gorenstein Algebras,' Sections 2.2 and 3.1.
isGorMinGenDegSeq = method();
isGorMinGenDegSeq(List) := degList -> (
     local theta; local n; local m; local result;
     n = #degList;
     if not odd n then return false; -- The number of minimal generators must be odd.
     m = sub((n-1)/2,ZZ);
     if sum(degList) % m != 0 then return false;
     theta = sub(sum(degList)/m,ZZ);
     if min degList <= 0 then error "Error: Expected a sequence of positive integers.";
     if degList != sort degList then error "Error: Expected a non-decreasing sequence.";
     -- If theta <= degList#i+degList#(n-i) for some i=0,..,m-1, then return false,
     -- else return true.
     result = scan(m, i -> if theta <= degList#(i+1)+degList#(n-1-i) then break false);
     return result === null;
)

-- Method: randomGorMinGenDeqSeq
-- Input: (ZZ,ZZ) -- The length n of the desired degree sequence and an upper bound M on the allowed degrees.
-- Output: List -- A degree sequence of length n with degrees bounded above by M such that there exists a
-- homogeneous grade three Gorenstein ideal minimally generated in these degrees.
randomGorMinGenDegSeq = method();
randomGorMinGenDegSeq(ZZ,ZZ):= (n,M) ->(
    
    if not odd n then error "Error: A degree sequence for a set of minimal generators of a homogeneous grade three Gorenstein ideal must have odd length.";
    
    local D;
    
    D = {1,1};
    while not isGorMinGenDegSeq(D) do (
                D = sort apply(n, i-> random(1,M));
    );

    return D;
)


-- Method: codimThreeGorBetti
-- Input: List -- A non-decreasing list of positive integers representing a possible degree sequence for
-- a set of minimal generators for a homogeneous grade three Gorenstein ideal I.
-- Output: BettiTally -- The Betti table of R/I. 
codimThreeGorBetti = method();
codimThreeGorBetti(List):= degList ->(
    if  not isGorMinGenDegSeq(degList) then error "Error: The degree sequence is not the degree sequence of minimal generators for any homogeneous grade three Gorenstein ideal.";
    
    local m; local theta; local K; local degFreq; local C; local D;
    
    m = sub((#degList-1)/2,ZZ);
    theta = sub(sum(degList)/m,ZZ);
    K = max L;
    
    -- Create a list of the number of times that each generator degree occurs.
    degFreq = apply(toList(1..K), i -> #positions(degList, j -> j==i));
    
    -- Create the hash table with the Betti numbers.
    C = apply(toList(1..K), i -> if degFreq#(i-1) != 0 then (1,{i},i) => degFreq#(i-1));
    D = apply(toList(1..K), i -> if degFreq#(i-1) != 0 then (2,{theta-i},theta-i) => degFreq#(i-1));
    C = {(0,{0},0) => 1}|C|D|{(3,{theta},theta) => 1};
    C = delete(null,C);
    return new BettiTally from new HashTable from C;
)


-- Given a list of degrees of generators and the ambient polynomial ring, create a generic
-- syzygy matrix for a homogeneous grade three Gorenstein ideal minimally generated in those degrees.
genericGorSyzMatrix = method();
genericGorSyzMatrix(List,Ring) := (degList,R) -> (
    local n; local theta; local syzDeg; local r; local polyDeg; local coeffList;
    local S; local origVars; local polyDegsOnly; local maxPolyDeg; local monBases;
    local M; local m;
       
    n = #degList; -- n is odd.
    theta = sub(sum(degList)/sub((n-1)/2,ZZ),ZZ);
    syzDeg = apply(n, i -> theta - degList#i); -- The degrees of the syzygies.
    r = numgens R;
    
    -- Compute the degree of the homogeneous polynomial in the (i,j) position of the
    -- syzygy matrix for each entry above the main diagonal.
    polyDeg = apply(n-1, i -> 
	 apply(toList((i+1)..(n-1)), j -> {i,j,syzDeg#j-degList#i})
    );

    polyDeg = flatten polyDeg;	     
	     
    -- Create a list of variables to represent the unknown coefficients in the matrix.
    coeffList = apply(polyDeg, L -> (
	 apply(numMonomials(L#2,r), k -> c_{L#0,L#1,k})
    ));

    coeffList = flatten coeffList;
    
    S = (coefficientRing R)(monoid [(gens R)|coeffList]); -- New polynomial ring containing additional variables representing unknown coefficients.
    origVars = sub(vars R,S); -- A matrix of the original variables, considered as elements of S.
    
    -- Compute a basis of monomials of degree d in R for each degree appearing in the syzygy matrix.
    polyDegsOnly = apply(polyDeg, L -> L#2);
    maxPolyDeg = max polyDegsOnly; -- The largest degree of a polynomial appearing in the syzygy matrix.
    -- The next line only computes the monomial bases that we actually need.
    monBases = {map(S^1,S^1,1_S)}|apply(toList(1..maxPolyDeg), d -> if any(polyDegsOnly, i -> i == d) then gens (ideal origVars)^d);
    
    -- Create the generic syzygy matrix.
    M = mutableMatrix(S,n,n);
    scan(polyDeg, L -> (
	m = numMonomials(L#2,r);
	M_(L#0,L#1) = (map(S^1,S^m,{apply(m, k -> (c_{L#0,L#1,k})_S)})*map(S^m,S^1,transpose(monBases#(L#2))))_(0,0);
        M_(L#1,L#0) = -M_(L#0,L#1);
    ));
    
    return matrix M;
    
)

-- Method: beMatrix
-- Input: Matrix -- A set of minimal generators for a homogeneous grade three Gorenstein ideal
-- in a polynomial ring.
-- Output: Matrix -- A Buchsbaum-Eisenbud matrix for the given minimal generating set.  The
-- signed sub-maximal pfaffians of this matrix are equal to a scalar multiple of the given
-- generators.

-- Todo: Modify this method to work for polynomial rings in >=3 variables.
beMatrix = method(Options => {CheckGorenstein => false})
beMatrix(Matrix) := opts -> d -> (
     local I; local R; local r; local n; local degList; local theta; local syzDeg;
     local genSyzMatrix; local S; local origVars; local cVars; local equations;
     local cCoeff; local eqnMatrix; local kerGens; local solCoeff; local solMatrices;
     local trueBEMatrix;
     
     I = ideal d;
     R = ring d;
     r = numgens R;
     n = numcols d;
     degList = apply(n, i -> (degree d_(0,i))#0); -- Degree sequence for the generators, in non-decreasing order.
     
     -- Check that the generators satisfy the required conditions.
     if not isGorMinGenDegSeq(sort degList) then error "Error: The given generators do not minimally generate a homogeneous grade three Gorenstein ideal.";
     if not isHomogeneous I then error "Error: Expected generators of a homogeneous ideal.";
     
     -- If the user passes the CheckGorenstein option, check that the given set
     -- minimally generates a grade three Gorenstein ideal.
     if opts.CheckGorenstein then (
     	 if n != numcols mingens I then error "Error: The given generating set is not minimal.";
     	 if not isCM(comodule I) or depth(I,R) != 3 or rank (res comodule I)_3 != 1 then error "Error: The given polynomials do not generate a grade 3 Gorenstein ideal.";
     );
 
     theta = sub(sum(degList)/sub((n-1)/2,ZZ),ZZ);
     syzDeg = apply(n, i -> theta - degList#i); -- The degrees of the syzygies.
     
     genSyzMatrix = genericGorSyzMatrix(degList,R); -- A generic syzygy matrix with coefficients we need to solve for.
     S = ring genSyzMatrix; -- S contains variables of the form c_{i,j,k} representing the unknown coefficients.
     origVars = flatten entries sub(vars R,S); -- The original variables from R, treated as elements of S.
     cVars = gens S; -- All variables, including the new c_{i,j,k} variables.
     scan(origVars, i -> cVars = delete(i,cVars)); -- Now cVars only contains the new c_{i,j,k} variables.
     
     equations = sub(d,S)*genSyzMatrix; -- The entry in the i-th column of `equations' will be homogeneous of degree syzDeg#i.
     
     -- Since all of the coefficients in the product must vanish, this next line
     -- extracts all of these equations in terms of the c_{i,j,k}'s.
     cCoeff = apply(n, i -> (coefficients(equations_(0,i), Variables => origVars, Monomials => flatten entries sub(gens (ideal vars R)^(syzDeg#i),S)))#1);
     eqnMatrix = map(S^0,S^(#cVars),0);
     
     -- The vectors in ker eqnMatrix will correspond to coefficients of the Buchsbaum-Eisenbud matrix.
     scan(n, i -> scan(numMonomials(syzDeg#i,r), j -> eqnMatrix = eqnMatrix||(transpose (coefficients((cCoeff#i)_(j,0),Variables => cVars, Monomials => cVars))#1)));
     kerGens = transpose mingens ker eqnMatrix;
     solCoeff = apply(numrows kerGens, i -> sub(vars R,S)|kerGens^{i});
     solMatrices = apply(#solCoeff, i -> sub(genSyzMatrix,solCoeff#i));
     trueBEMatrix = scan(solMatrices, M -> (if rank M == (n - 1) then break sub(M,R)));
     return trueBEMatrix;
)

-- Method: randomGorenstein
-- Inputs: (ZZ,ZZ,Ring) -> (Number of minimal generators,bound on the degrees of the generators,polynomial ring in 3 variables over a field)
-- Output: Minimal generators of a homogeneous grade 3 Gorenstein ideal in the given polynomial ring.

-- Note: Can we modify this to work for polynomial rings in >=3 variables?
-- Currently there are errors in this method where theta can be rational.  Need to check divisibility before performing division.
randomGorenstein = method();
randomGorenstein(ZZ,ZZ,Ring) := (numGens,genLimit,SRing) -> (
     local RRing; local foundExample; local aboveDiag; local randomDegSeq;
     local theta; local degCheck; local syzDeg; local G; local randomMatrix;
     local subMatrix; local proposedGens;
     if not odd numGens then error "Error: Expected an odd number of generators.";
     foundExample = false;
     aboveDiag = sub((numGens*(numGens-1))/2,ZZ);
     RRing = (coefficientRing SRing)[flatten entries vars SRing,vars(52..51+aboveDiag)];
     while foundExample == false do (
	  print "Running through the loop.";
     	  randomDegSeq = sort apply(numGens, i -> random(1,genLimit));
     	  -- Make sure the random sequence satisfies the properties required for a degree sequence of the generators of a Gorenstein ideal.
     	  theta = sub(sum(randomDegSeq)/sub((numGens-1)/2,ZZ),ZZ);
     	  degCheck = apply(toList(1..sub((numGens-1)/2,ZZ)), i -> theta - randomDegSeq#(i) - randomDegSeq#(numGens-i));
     	  while sum(randomDegSeq) % sub((numGens-1)/2,ZZ) != 0 or min degCheck <= 0 do (
	       randomDegSeq = sort apply(numGens, i -> random(1,genLimit));
     	       theta = sub(sum(randomDegSeq)/sub((numGens-1)/2,ZZ),ZZ);
     	       degCheck = apply(toList(1..sub((numGens-1)/2,ZZ)), i -> theta - randomDegSeq#i - randomDegSeq#(numGens-i));
     	  );
     	  print randomDegSeq;
          syzDeg = apply(numGens, i -> theta - randomDegSeq#i);
     	  G = flatten apply(numGens-1, i -> apply(toList((i+1)..(numGens-1)), j -> sub(random(syzDeg#j-randomDegSeq#i,SRing),RRing)));
	  randomMatrix = genericSkewMatrix(RRing,x0,numGens);
     	  subMatrix = sub(matrix{flatten {flatten entries sub(vars SRing,RRing),G}},RRing);
     	  randomMatrix = sub(sub(randomMatrix,subMatrix),SRing);
     	  print("randomMatrix: ",randomMatrix);
	  proposedGens = sub(matrix{ordPfaff(numGens-1,randomMatrix)},SRing);
	  if rank randomMatrix == (numGens - 1) and depth(ideal proposedGens,SRing) == 3 and numcols(mingens ideal proposedGens) == numGens then foundExample = true;
     );
     return proposedGens;
)

-- Method: randomDSGorenstein
-- Inputs: List: A list containing the desired degrees of the generators of a grade 3 Gorenstein ideal in k[x,y,z].
--         Ring: The polynomial ring in which to create the ideal.
-- Output: A random grade 3 Gorenstein ideal whose generators have the given degree sequence.

-- Note: Can we modify this to work in polynomial rings with >=3 variables?
randomDSGorenstein = method();
randomDSGorenstein(List,Ring) := (degList,SRing) -> (
     local RRing; local foundExample; local aboveDiag; local randomDegSeq;
     local theta; local degCheck; local syzDeg; local G; local randomMatrix;
     local subMatrix; local proposedGens;
     numGens = #degList;
     if not odd numGens then error "Error: Expected an odd number of generators.";
     if not admissibleDegSeq(degList) then error "Error: Expected an admissible degree sequence for the minimal generators of a homogeneous grade 3 Gorenstein ideal.";
     theta = sub(sum(degList)/((#degList -1)/2),ZZ);
     foundExample = false;
     aboveDiag = sub((numGens*(numGens-1))/2,ZZ);
     RRing = (coefficientRing SRing)[flatten entries vars SRing,vars(52..51+aboveDiag)];
     while foundExample == false do (
	  print "Running through the loop.";
     	  -- Make sure the random sequence satisfies the properties required for a degree sequence of the generators of a Gorenstein ideal.
     	  syzDeg = apply(numGens, i -> theta - degList#i);
     	  G = flatten apply(numGens-1, i -> apply(toList((i+1)..(numGens-1)), j -> sub(random(syzDeg#j-degList#i,SRing),RRing)));
	  randomMatrix = genericSkewMatrix(RRing,x0,numGens);
     	  subMatrix = sub(matrix{flatten {flatten entries sub(vars SRing,RRing),G}},RRing);
     	  randomMatrix = sub(sub(randomMatrix,subMatrix),SRing);
     	  print("randomMatrix: ",randomMatrix);
	  proposedGens = sub(matrix{ordPfaff(numGens-1,randomMatrix)},SRing);
	  if rank randomMatrix == (numGens - 1) and depth(ideal proposedGens,SRing) == 3 and numcols(mingens ideal proposedGens) == numGens then foundExample = true;
     );
     return proposedGens;
)


-- Method: randomPureGorenstein - Generate a random grade 3 Gorenstein ideal with a pure resolution. (All generators have same degree.)
-- Inputs: ZZ: Number of generators of desired ideal. (Must be odd.)
--         ZZ: Upper bound on the degrees of the generators. (All generators will have the same degree.)
--         Ring: The polynomial ring in which to create the ideal.
-- Output: A random grade 3 Gorenstein ideal with a pure resolution.

-- Note: Does this work if the ring has >=3 variables?
randomPureGorenstein = method();
randomPureGorenstein(ZZ,ZZ,Ring) := (numGens,genLimit,SRing) -> (
     local RRing; local foundExample; local aboveDiag; local randomDegSeq;
     local theta; local degCheck; local syzDeg; local G; local randomMatrix;
     local subMatrix; local randomInt;
     if not odd numGens then error "Error: Expected an odd number of generators.";
     foundExample = false;
     aboveDiag = sub((numGens*(numGens-1))/2,ZZ);
     RRing = (coefficientRing SRing)[flatten entries vars SRing,vars(52..51+aboveDiag)];
     while foundExample == false do (
	  print "Running through the loop.";
     	  randomInt = random(1,genLimit);
	  randomDegSeq = sort apply(numGens, i -> randomInt);
     	  -- Make sure the random sequence satisfies the properties required for a degree sequence of the generators of a Gorenstein ideal.
     	  theta = sub(sum(randomDegSeq)/sub((numGens-1)/2,ZZ),ZZ);
     	  degCheck = apply(toList(1..sub((numGens-1)/2,ZZ)), i -> theta - randomDegSeq#i - randomDegSeq#(numGens-i));
     	  while sum(randomDegSeq) % sub((numGens-1)/2,ZZ) != 0 or min degCheck <= 0 do (
	       randomInt = random(1,genLimit);
	       randomDegSeq = sort apply(numGens, i -> randomInt);
     	       theta = sub(sum(randomDegSeq)/sub((numGens-1)/2,ZZ),ZZ);
     	       degCheck = apply(toList(1..sub((numGens-1)/2,ZZ)), i -> theta - randomDegSeq#i - randomDegSeq#(numGens-i));
     	  );
     	  print randomDegSeq;
          syzDeg = apply(numGens, i -> theta - randomDegSeq#i);
     	  G = flatten apply(numGens-1, i -> apply(toList((i+1)..(numGens-1)), j -> sub(random(syzDeg#j-randomDegSeq#i,SRing),RRing)));
	  randomMatrix = genericSkewMatrix(RRing,x0,numGens);
     	  subMatrix = sub(matrix{flatten {flatten entries sub(vars SRing,RRing),G}},RRing);
     	  randomMatrix = sub(sub(randomMatrix,subMatrix),SRing);
     	  proposedGens = sub(matrix{ordPfaff(numGens-1,randomMatrix)},SRing);
	  if rank randomMatrix == (numGens - 1) and depth(ideal proposedGens,SRing) == 3 and numcols(mingens ideal proposedGens) == numGens then foundExample = true;
     );
     return proposedGens;
)

end


-- Examples of how to use the command beMatrix.

restart
loadPackage "GradeThreeGorenstein"
R = QQ[x,y,z]
I = ideal(x^4,y^4,z^4):(ideal(x+y+z))^4 -- 5 generated homogeneous grade 3 Gorenstein ideal in QQ[x,y,z]
betti res comodule I -- 4 generators of degree 3 and 1 of degree 4.
Gens = gens I
gbPresMatrix = map(R^5,R^5,(res comodule I).dd_2) -- Does not give alternating presentation matrix.
transpose gbPresMatrix == -gbPresMatrix -- Check that it's not alternating.
d2 = map(R^5,R^5,beMatrix Gens) -- Calculate an alternating presentation matrix.
transpose d2 == -d2 -- Check that it is alternating.
Gens*d2
pfaffians(4,d2) == I
matrix{signedPfaffians(d2)} == 60*Gens -- Check that the signed maximal order pfaffians are a scalar multiple of the given generating set.

restart
load "BEMatrices.m2"
R = QQ[x,y,z]
I = ideal(x^6,y^6,z^6):(ideal(x+y+z))^6 -- 7 generated homogeneous grade 3 Gorenstein ideal in QQ[x,y,z]
betti res comodule I -- 6 generators of degree 5 and 1 of degree 6
Gens = gens I
gbPresMatrix = map(R^7,R^7,(res comodule I).dd_2) -- Does not give an alternating presentation matrix.
transpose gbPresMatrix == -gbPresMatrix -- Check that it's not alternating.
d2 = map(R^7,R^7,beMatrix Gens)
transpose d2 == -d2 -- Check that it is alternating.
Gens*d2
pfaffians(6,d2) == I
matrix{ordPfaff(6,d2)} == -15120*Gens -- Check that the signed maximal order pfaffians are a scalar multiple of the given generating set.

restart
load "BEMatrices.m2"
R = ZZ/5[x,y,z]
I1 = ideal randomGorenstein(5,9,R)
apply(flatten entries gens I1, i -> (degree i)#0) -- Look at the degree sequence.
BE1 = map(R^5,R^5,beMatrix gens I1)
transpose(BE1) == -BE1 -- Check that it is alternating.
matrix{ordPfaff(4,BE1)} -- Compare signed maximal ordered pfaffians
gens I1                 -- with original generators.

restart
load "BEMatrices.m2"
R = ZZ/5[x,y,z]
I2 = ideal randomDSGorenstein({4,5,6,6,8,8,8},R)
apply(flatten entries gens I2, i -> (degree i)#0) -- Look at the degree sequence.
BE2 = map(R^7,R^7,beMatrix gens I2)
transpose(BE2) == -BE2 -- Check that it is alternating.
matrix{ordPfaff(6,BE2)} -- Compare signed maximal ordered pfaffians
gens I2                 -- with original generators.

restart
load "BEMatrices.m2"
R = ZZ/5[x,y,z]
I3 = ideal randomPureGorenstein(7,15,R)
apply(flatten entries gens I3, i -> (degree i)#0) -- Look at the degree sequence.
BE3 = map(R^7,R^7,beMatrix gens I3)
transpose(BE3) == -BE3 -- Check that it is alternating.
matrix{ordPfaff(6,BE3)} -- Compare signed maximal ordered pfaffians
gens I3                 -- with original generators.




-- Tests

restart
loadPackage "GradeThreeGorenstein"
R = QQ[x,y,z]
d = randomGorMinGenDegSeq(5,11)
genericGorSyzMatrix(d,R)
d
sum(d)/2
