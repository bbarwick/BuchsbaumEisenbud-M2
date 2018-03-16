-- To do list:

-- 1. Tweak beMatrix (really genericGorSyzMatrix) to work over ZZ/2.
-- 2. Figure out error with unexported unset symbol c from genSyzMatrix method.
-- 3. Write documentation using simpledoc.
-- 4. Write tests.
-- 5. 

-----------------------------------------------------------------------------
-- PURPOSE : The GradeThreeGorenstein package for Macaulay2 computes a Buchsbaum-Eisenbud
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
     "IterationLimit",
     
-- Helper methods
--     "genericGorSyzMatrix",
--     "numMonomials",
     "submaximalPfaffians",

-- Main package methods
     "beMatrix",
     "gradeThreeGorensteinBetti",
     "isGorMinGenDegSeq",
     "randomGorMinGenDegSeq",
     "randomGradeThreeGorenstein",
     "randomGradeThreeDSGorenstein",
     "randomGradeThreePureGorenstein"

}

------------------------------------------------------------
-- Small helper methods ------------------------------------
------------------------------------------------------------

-- Method: submaximalPfaffians
-- Input: Matrix -- A skew-symmetric matrix M of size (2n+1) x (2n+1) over a ring R.
-- Output: Matrix -- An matrix containing the signed sub-maximal (2n x 2n) pfaffians of M.
submaximalPfaffians = method();
submaximalPfaffians(Matrix) := M -> (
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
    return matrix{apply(m, i -> if submatrix'(M,{i},{i}) == 0 then 0 else (-1)^i*(gens pfaffians(n-1,submatrix'(M,{i},{i})))_(0,0))};
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
     if min degList <= 0 then return false; -- The minimal generators must have positive degree.
     m = sub((n-1)/2,ZZ);
     if sum(degList) % m != 0 then return false; -- See Diesel's paper.
     
     theta = sub(sum(degList)/m,ZZ);
     degList = sort degList; -- Make sure the list is in non-decreasing order.
     
     -- If theta <= degList#i+degList#(n-i) for some i=0,..,m-1, then return false,
     -- else return true.
     result = scan(m, i -> if theta <= degList#(i+1)+degList#(n-1-i) then break false);
     return result === null;
)

-- Method: randomGorMinGenDeqSeq
-- Input: (ZZ,ZZ) -- The length n of the desired degree sequence and an upper bound M on the allowed degrees.
-- Output: List -- A degree sequence of length n with degrees bounded above by M such that there exists a
-- homogeneous grade three Gorenstein ideal minimally generated in these degrees.
randomGorMinGenDegSeq = method(Options => {IterationLimit => 1000});
randomGorMinGenDegSeq(ZZ,ZZ):= opts -> (n,M) ->(
    if not odd n then error "Error: A degree sequence for a set of minimal generators of a homogeneous grade three Gorenstein ideal must have odd length.";
    
    local D; local iterations;
    
    iterations = 0;
    D = {1,1};
    while not isGorMinGenDegSeq(D) do (
	iterations = iterations+1;
	if iterations > opts.IterationLimit then error("Error: Unable to find an ideal in "|toString(iterations)|" attempts.");
	D = sort apply(n, i-> random(1,M));
    );
    return D;
)


-- Method: gradeThreeGorensteinBetti
-- Input: List -- A non-decreasing list of positive integers representing a possible degree sequence for
-- a set of minimal generators for a homogeneous grade three Gorenstein ideal I.
-- Output: BettiTally -- The Betti table of R/I. 
gradeThreeGorensteinBetti = method();
gradeThreeGorensteinBetti(List):= degList ->(
    if  not isGorMinGenDegSeq(degList) then error "Error: The degree sequence is not the degree sequence of minimal generators for any homogeneous grade three Gorenstein ideal.";
    
    local m; local theta; local K; local degFreq; local C; local D;
    
    m = sub((#degList-1)/2,ZZ);
    theta = sub(sum(degList)/m,ZZ);
    K = max degList;
    
    -- Create a list of the number of times that each generator degree occurs.
    degFreq = apply(toList(1..K), i -> #positions(degList, j -> j==i));
    
    -- Create the hash table with the Betti numbers.
    C = apply(toList(1..K), i -> if degFreq#(i-1) != 0 then (1,{i},i) => degFreq#(i-1));
    D = apply(toList(1..K), i -> if degFreq#(i-1) != 0 then (2,{theta-i},theta-i) => degFreq#(i-1));
    C = {(0,{0},0) => 1}|C|D|{(3,{theta},theta) => 1};
    C = delete(null,C);
    return new BettiTally from new HashTable from C;
)


-- Method: genericGorSyzMatrix
-- Input: (List,Ring) -- A non-decreasing list of positive integers representing a possible degree sequence for
-- a set of minimal generators for a homogeneous grade three Gorenstein ideal I, and a polynomial ring R.
-- Output: Matrix -- A matrix of generic homogeneous forms having the correct degrees to be a 
-- Buchsbaum-Eisenbud matrix for a set of minimal generators having the given degree sequence.
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
	 apply(numMonomials(L#2,r), k -> (vars(2))_{L#0,L#1,k})
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
	if L#2 >= 0 then (
	    m = numMonomials(L#2,r);
	    M_(L#0,L#1) = (map(S^1,S^m,{apply(m, k -> ((vars(2))_{L#0,L#1,k})_S)})*map(S^m,S^1,transpose(monBases#(L#2))))_(0,0);
            M_(L#1,L#0) = -M_(L#0,L#1);
	);
    ));
    
    return matrix M;
    
)

-- Method: beMatrix
-- Input: Matrix -- A set of minimal generators for a homogeneous grade three Gorenstein ideal
-- in a polynomial ring.
-- Output: Matrix -- A Buchsbaum-Eisenbud matrix for the given minimal generating set.  The
-- signed sub-maximal pfaffians of this matrix are equal to a scalar multiple of the given
-- generators.
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
     degList = apply(n, i -> (degree d_(0,i))#0); -- Degree sequence for the generators.
     
     -- If the user passes the CheckGorenstein option, check that the given set
     -- minimally generates a grade three Gorenstein ideal.
     if opts.CheckGorenstein then (
     	 if not isGorMinGenDegSeq(sort degList) then error "Error: The given generators do not minimally generate a homogeneous grade three Gorenstein ideal.";
     	 if not isHomogeneous I then error "Error: Expected generators of a homogeneous ideal.";
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
     
     -- One of the matrices must have rank n-1.  By the Buchsbaum-Eisenbud acyclicity criterion,
     -- this matrix will be a Buchsbaum-Eisenbud matrix for the given generating set.
     trueBEMatrix = scan(solMatrices, M -> (if rank M == n-1 then break sub(M,R)));
     return trueBEMatrix;
)

-- Method: randomGradeThreeGorenstein
-- Inputs: (ZZ,ZZ,Ring) -- (Number of minimal generators, bound on the degrees of the generators, polynomial ring over a field)
-- Output: Matrix -- Minimal generators of a homogeneous grade 3 Gorenstein ideal in the given polynomial ring.
randomGradeThreeGorenstein = method(Options => {IterationLimit => 1000});
randomGradeThreeGorenstein(ZZ,ZZ,Ring) := opts -> (numGens,genLimit,R) -> (
     local foundExample; local iterations; local randomDegSeq; local genSyzMatrix;
     local S; local origVars; local numCVars; local T; local randomCoeffMatrix;
     local randomMatrix; local possibleGens;
     
     if not odd numGens then error "Error: Expected an odd number of generators.";
     if numgens R < 3 then error "Error: Expected a polynomial ring with at least three variables.";
     
     foundExample = false;
     iterations = 0;
          
     while foundExample == false do (
	  iterations = iterations + 1;
	  if iterations > opts.IterationLimit then error("Error: Unable to find an ideal in "|toString(iterations)|" attempts.");
	  randomDegSeq = randomGorMinGenDegSeq(numGens,genLimit);
     	  genSyzMatrix = genericGorSyzMatrix(randomDegSeq,R);
	  S = ring genSyzMatrix;
	  origVars = sub(vars R,S); -- Matrix of the original variables from R in S.
	  numCVars = numgens S - numgens R; -- Number of generic coefficient variables in genSyzMatrix.
	  T = coefficientRing S;
	  randomCoeffMatrix = origVars|(matrix {apply(numCVars, i -> random(T))}); -- Create a list of random coefficients.
	  randomMatrix = sub(sub(genSyzMatrix,randomCoeffMatrix),R); -- Create a random skew-symmetric matrix of forms having the correct degrees.
     	  possibleGens = submaximalPfaffians(randomMatrix);
	  if rank randomMatrix == (numGens-1) and depth(ideal possibleGens,R) == 3 and numcols mingens ideal possibleGens == numGens then foundExample = true;
     );
 
     return possibleGens;
)

-- Method: randomGradeThreeDSGorenstein
-- Inputs: (List,Ring) -- A list containing the desired degrees of the generators of a grade 3 Gorenstein ideal in the polynomial ring R.
-- Output: Matrix -- A matrix containing minimal generators of a random grade 3 Gorenstein ideal whose minimal generators have the given degree sequence.
randomGradeThreeDSGorenstein = method(Options => {IterationLimit => 1000});
randomGradeThreeDSGorenstein(List,Ring) := opts -> (degList,R) -> (
     local foundExample; local iterations; local randomDegSeq; local genSyzMatrix;
     local S; local origVars; local numCVars; local T; local randomCoeffMatrix;
     local randomMatrix; local possibleGens;
     
     if not isGorMinGenDegSeq(degList) then error "Error: There does not exist a homogeneous grade three Gorenstein ideal whose minimal generators have the given degree sequence.";
     if numgens R < 3 then error "Error: Expected a polynomial ring with at least three variables.";
     
     foundExample = false;
     iterations = 0;
     genSyzMatrix = genericGorSyzMatrix(degList,R);
     S = ring genSyzMatrix;
     origVars = sub(vars R,S); -- Matrix of the original variables from R in S.
     numCVars = numgens S - numgens R; -- Number of generic coefficient variables in genSyzMatrix.
     T = coefficientRing S;
          
     while foundExample == false do (
	  iterations = iterations + 1;
	  if iterations > opts.IterationLimit then error("Error: Unable to find an ideal in "|toString(iterations)|" attempts.");
	  randomCoeffMatrix = origVars|(matrix {apply(numCVars, i -> random(T))}); -- Create a list of random coefficients.
	  randomMatrix = sub(sub(genSyzMatrix,randomCoeffMatrix),R); -- Create a random skew-symmetric matrix of forms having the correct degrees.
     	  possibleGens = submaximalPfaffians(randomMatrix);
	  if rank randomMatrix == (#degList-1) and depth(ideal possibleGens,R) == 3 and numcols mingens ideal possibleGens == #degList then foundExample = true;
     );
 
     return possibleGens;
)

-- Method: randomGradeThreePureGorenstein - Generate a random grade 3 Gorenstein ideal with a pure resolution. (All generators have same degree.)
-- Inputs: ZZ: Number of generators of desired ideal. (Must be odd.)
--         ZZ: Desired degree of all of the generators.
--         Ring: The polynomial ring in which to create the ideal.
-- Output: A random grade 3 Gorenstein ideal with a pure resolution.
randomGradeThreePureGorenstein = method(Options => {IterationLimit => 1000});
randomGradeThreePureGorenstein(ZZ,ZZ,Ring) := opts -> (numGens,genDegree,R) -> (
     local foundExample; local iterations; local degSeq;
     local genSyzMatrix; local S; local origVars; local numCVars; local T;
     local randomCoeffMatrix; local randomMatrix; local possibleGens;
     
     if not odd numGens then error "Error: Expected an odd number of generators.";
     if numgens R < 3 then error "Error: Expected a polynomial ring with at least three variables.";
     
     foundExample = false;
     iterations = 0;
     degSeq = apply(numGens, i -> genDegree);
     if not isGorMinGenDegSeq(degSeq) then error("Error: There does not exist a grade three Gorenstein ideal minimally generated in degrees: "|toString(degSeq)|".");
     
     while foundExample == false do (
	  iterations = iterations + 1;
	  if iterations > opts.IterationLimit then error("Error: Unable to find an ideal in "|toString(iterations)|" attempts.");
	  genSyzMatrix = genericGorSyzMatrix(degSeq,R);
	  S = ring genSyzMatrix;
	  origVars = sub(vars R,S); -- Matrix of the original variables from R in S.
	  numCVars = numgens S - numgens R; -- Number of generic coefficient variables in genSyzMatrix.
	  T = coefficientRing S;
	  randomCoeffMatrix = origVars|(matrix {apply(numCVars, i -> random(T))}); -- Create a list of random coefficients.
	  randomMatrix = sub(sub(genSyzMatrix,randomCoeffMatrix),R); -- Create a random skew-symmetric matrix of forms having the correct degrees.
     	  possibleGens = submaximalPfaffians(randomMatrix);
	  if rank randomMatrix == (numGens-1) and depth(ideal possibleGens,R) == 3 and numcols mingens ideal possibleGens == numGens then foundExample = true;
     );
 
     return possibleGens;
)

--------------------------------------------------------------------
-- Documentation ---------------------------------------------------
--------------------------------------------------------------------

-- Options
--     "CheckGorenstein",
--     "IterationLimit",
     
-- Helper methods
--     "genericGorSyzMatrix",
--     "numMonomials",
--     "submaximalPfaffians",

-- Main package methods
--     "beMatrix",
--     "gradeThreeGorensteinBetti",
--     "isGorMinGenDegSeq",
--     "randomGorMinGenDegSeq",
--     "randomGradeThreeGorenstein",
--     "randomGradeThreeDSGorenstein",
--     "randomGradeThreePureGorenstein"

beginDocumentation()

doc ///
Key
    GradeThreeGorenstein
Headline
    A package for computations involving homogeneous grade three Gorenstein ideals.
Description
  Text
    This package contains methods for performing computations involving homogeneous grade
    three Gorenstein ideals in polynomial rings.
    
    Given a non-decreasing sequence of positive integers having odd length, it is well understood by work of Diesel the necessary and sufficient
    conditions under which this sequence is the sequence of degrees of a minimal generating set of a homogeneous
    grade three Gorenstein ideal I (see Sections 2.2 and 3.1 of Diesel's {\em Irreducibility
    and dimension theorems for families of height 3 Gorenstein algebras}), and the package can test whether a given degree sequence satisfies these
    requirements.  Given such a degree sequence for a set of minimal generators of a Gorenstein ideal I, this package  
    can display the Betti diagram corresponding to a minimal graded free resolution of R/I numerically, without the
    need to compute the syzygies.  There are also various methods provided for generating random homogeneous grade three
    Gorenstein ideals in polynomial rings.
    
    The primary method provided by this package is @TO beMatrix@, which computes
    a Buchsbaum-Eisenbud matrix for a given set of minimal generators of a homogeneous grade three Gorenstein ideal.
    A Buchsbaum-Eisenbud matrix is an alternating presentation matrix for the ideal such that the signed submaximal
    Pfaffians of the matrix are equal (up to scalar multiple) to the given generating set.  The existence of such a
    presentation matrix was proved in 1977 by Buchsbaum and Eisenbud in the paper {\em Algebra structures for finite free
    resolutions, and some structure theorems for ideals of codimension 3}.
  
    References:
    
        $\bullet$ Diesel, Susan J, {\em Irreducibility and dimension theorems for families of height 3 Gorenstein algebras},
    Pacific J. Math. 172 (1996), no. 2, 365-397.    
    
        $\bullet$ Buchsbaum, David and Eisenbud, David, {\em Algebra structures for finite free resolutions, and some structure theorems for ideals of codimension 3},
    Amer. J. Math. 99 (1977), no. 3, 447-485. 

///

doc ///
Key
    CheckGorenstein
Headline
    an optional parameter.
Description
  Text
    An optional parameter (default value {\tt false}) which allows the user to specify
    that they would like for the method to check whether the given generating set actually
    generates a grade three Gorenstein ideal.  Setting this option to {\tt true} will
    increase computation time.
///

doc ///
Key
    IterationLimit
Headline
    an optional parameter.
Description
  Text
    An optional parameter (default value {\tt 1000}) which allows the user to specify
    how many iterations the method will go through when trying to compute a random
    Gorenstein ideal with the given properties.
///

doc ///
Key
    beMatrix
Headline
    computes a Buchsbaum-Eisenbud matrix for a given generating set.
Usage
    B = beMatrix(g)
Inputs
    g:Matrix
      a minimal generating set for a homogeneous grade three Gorenstein ideal.
    CheckGorenstein => Boolean
      an option which allows the user to check whether the given generating set minimally generates a homogeneous grade three Gorenstein ideal.
Outputs
    B:Matrix
      a Buchsbaum-Eisenbud matrix for the given minimal generating set.
Description
  Text
    Given a generating set for a homogeneous grade three Gorenstein ideal, Buchsbaum and Eisenbud
    proved that there exists a skew-symmetric presentation matrix for the ideal whose signed submaximal
    Pfaffians are (up to scalar multiple) equal to the given generators.  We refer to such a presentation
    matrix as a Buchsbaum-Eisenbud matrix.  Standard algorithms for computing a presentation matrix
    for an ideal do not take into account the existence of a presentation matrix having this special
    structure, and will typically not return a skew-symmetric presentation matrix.  This method has the
    ability to compute a Buchsbaum-Eisenbud matrix for a given minimal generating set.

  Example
    R = ZZ/5[x,y,z]
    g = matrix {{-x^2+x*y+2*x*z, -2*x^2+x*y-2*y^2+2*y*z+2*z^2, -2*x*y+x*z, x^4+x*y^3-x^3*z+x^2*y*z-2*x*y^2*z+2*y^3*z-x^2*z^2-x*y*z^2+y*z^3+z^4, x^3*y-x^2*y^2+y^4+x^3*z+x*y^2*z+y^3*z+x*y*z^2+y^2*z^2+2*x*z^3+2*y*z^3+z^4}}
    I = ideal(g)
    
    P = (res comodule I).dd_2 -- Presentation matrix given natively by Macaulay2.
    P + transpose(P) == 0 -- The matrix is not skew-symmetric.
    
    B = beMatrix(g) -- Compute a skew-symmetric presentation matrix.
    B + transpose(B) == 0
    g*B == 0 -- The columns of B are relations on the given generating set.
    submaximalPfaffians(B)
    submaximalPfaffians(B) == -g -- The signed submaximal Pfaffians of B are a scalar multiple of g.
    
Caveat
    If the given generating set is not minimal, the method may give unexpected results or fail entirely.
///

doc ///
Key
    (beMatrix,Matrix)
///

doc ///
Key
    gradeThreeGorensteinBetti
Headline
    computes the Betti table for the minimal graded free resolution of a homogeneous grade three Gorenstein ideal, given the generator degrees.
Usage
    B = gradeThreeGorensteinBetti(d)
Inputs
    d:List
      a non-decreasing list of positive integers representing the degrees of a minimal generating set for a homogeneous grade three Gorenstein ideal {\tt I} in a polynomial ring {\tt R}.
Outputs
    B:BettiTally
      the Betti table for the resolution of {\tt R/I}.
Description
  Text
    The degrees of the forms in a minimal generating set for a homogeneous grade three Gorenstein ideal
    completely determine the graded Betti numbers of R/I.  This method computes the graded Betti numbers
    from the given generator degrees, without needing to compute the free resolution.  If the given degree
    sequence cannot occur as the degree sequence of a minimal generating set for a homogeneous grade
    three Gorenstein ideal, an error is thrown.

  Example
    d = {5,5,8,8,9,9,10}
    B = gradeThreeGorensteinBetti(d)
    
///

doc ///
Key
    (gradeThreeGorensteinBetti,List)
///

doc ///
Key
    isGorMinGenDegSeq
Headline
    determines whether a given sequence of integers occurs as the minimal generator degrees of a homogeneous grade three Gorenstein ideal.
Usage
    b = isGorMinGenDegSeq(L)
Inputs
    L:List
      a list of integers.
Outputs
    b:Boolean
      whether there exists a homogeneous grade three Gorenstein ideal minimally generated in the given degrees.
Description
  Text
    Given a sequence of positive integers, the necessary and sufficient conditions for the sequence to occur as
    the degrees of a minimal generating set for a homogeneous grade three Gorenstein ideal are understood (see
    Diesel's paper {\em Irreduciblity and dimension theorems for families of height 3 Gorenstein algebras}, Sections 2.2 and 3.1).

    In particular, given a sequence of degrees $\{d_1,\ldots,d_{2m+1}\}$, define $\theta = (d_1 + \cdots + d_{2m+1})/m$.  Then we must have:
    
    $\bullet \ \ \theta$ is an integer (i.e., $d_1+\cdots+d_{2m+1}$ is divisible by $m$), and
    
    $\bullet \ \ \theta > d_{i+1} + d_{2m+2-i}$ for each $1 \leq i \leq m$.
    
    This method checks these conditions on a given integer sequence.
    
  Example
    d1 = {2,2,4,4}
    isGorMinGenDegSeq(d1) -- A grade three Gorenstein ideal must be minimally generated by an odd number of forms.
    
    d2 = {3,5,5,7,9}
    isGorMinGenDegSeq(d2) -- The sum of the degrees must be divisible by theta = (5-1)/2 = 2.
    
    d3 = {3,5,5,7,10}
    isGorMinGenDegSeq(d3) -- Notice that theta = 15, and 15 <= 5+10, violating the second condition above. 
    
    d4 = {4,4,5,6,6,8,9}
    isGorMinGenDegSeq(d4) -- All conditions are met.
    
SeeAlso
    randomGorMinGenDegSeq
    randomGradeThreeDSGorenstein
///

doc ///
Key
    (isGorMinGenDegSeq,List)
///

doc ///
Key
    randomGorMinGenDegSeq
Headline
    computes a random non-decreasing sequence of positive integers that represents the degrees of a minimal generating set of a homogeneous grade three Gorenstein ideal.
Usage
    d = randomGorMinGenDegSeq(m,n)
Inputs
    m:ZZ
      a positive integer, the number of generators.
    n:ZZ
      a positive integer, an upper bound on the degrees of the generators.
    IterationLimit => ZZ
      an optional parameter providing a limit for how many iterations are attempted when computing the random degree sequence.
Outputs
    d:List
      a list of degrees of a minimal generating set for a homogeneous grade three Gorenstein ideal.
Description
  Text
    This method computes a random degree sequence which occurs as the degrees of a minimal generating set
    for a homogeneous grade three Gorenstein ideal.

  Example
    d = randomGorMinGenDegSeq(9,13) -- Find a random degree sequence for an ideal with 9 generators of degree <= 13.
    gradeThreeGorensteinBetti(d) -- The Betti diagram for a grade three Gorenstein ideal having these generator degrees.
    
SeeAlso
    gradeThreeGorensteinBetti
    isGorMinGenDegSeq
    randomGradeThreeDSGorenstein
///

doc ///
Key
    (randomGorMinGenDegSeq,ZZ,ZZ)
///

doc ///
Key
    randomGradeThreeDSGorenstein
Headline
    computes a random set of minimal generators for a homogeneous grade three Gorenstein ideal with the given degree sequence.
Usage
    g = randomGradeThreeDSGorenstein(L,R)
Inputs
    L:List
      the desired sequence of degrees of the minimal generators.
    R:Ring
      a polynomial ring in which to construct the ideal.
    IterationLimit => ZZ
      an optional parameter providing a limit for how many iterations are attempted when computing the random generating set.
Outputs
    g:Matrix
      a minimal generating set for a homogeneous grade three Gorenstein ideal having the desired generator degrees.
Description
  Text
    This method computes a random set of minimal generators for a homogeneous grade three Gorenstein ideal in the given ring
    having the given generator degrees. If the given polynomial ring does not contain at least 3
    variables, or if the given degree sequence cannot occur as the degrees of a minimal generating set for
    a homogeneous grade three Gorenstein ideal, an error is thrown.
  Example
    d = randomGorMinGenDegSeq(5,9) -- Find a random degree sequence for an ideal with 5 generators of degree <= 9.
    R = ZZ/5[x,y,z]
    randomGradeThreeDSGorenstein(d,R) -- Find a random set of minimal generators for a grade three Gorenstein ideal in R having these generator degrees.
    
SeeAlso
    isGorMinGenDegSeq
    randomGorMinGenDegSeq
///

doc ///
Key
    (randomGradeThreeDSGorenstein,List,Ring)
///


--------------------------------------------------------------------
-- Tests -----------------------------------------------------------
--------------------------------------------------------------------

-- beMatrix Tests --
TEST ///
    R = ZZ/5[x,y,z]
    g = matrix {{-x^2+x*y+2*x*z, -2*x^2+x*y-2*y^2+2*y*z+2*z^2, -2*x*y+x*z, x^4+x*y^3-x^3*z+x^2*y*z-2*x*y^2*z+2*y^3*z-x^2*z^2-x*y*z^2+y*z^3+z^4, x^3*y-x^2*y^2+y^4+x^3*z+x*y^2*z+y^3*z+x*y*z^2+y^2*z^2+2*x*z^3+2*y*z^3+z^4}}
    I = ideal(g)
    B = beMatrix(g)
    assert(B + transpose(B) == 0)
    assert(g*B == 0)
    assert(submaximalPfaffians(B) == -g)
    ///

-- randomGradeThreeDSGorenstein Tests --
TEST ///
    R = QQ[x,y,z];
    d = randomGorMinGenDegSeq(7,10);
    g = randomGradeThreeDSGorenstein(d,R);
    M = map(R^7,R^7,beMatrix g);
    assert(M + transpose(M) == 0);
    assert(d*M == 0);
    ///

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
loadPackage "GradeThreeGorenstein"
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
loadPackage "GradeThreeGorenstein"
R = ZZ/5[x,y,z]
I1 = ideal randomGradeThreeGorenstein(5,9,R)
apply(flatten entries gens I1, i -> (degree i)#0) -- Look at the degree sequence.
gens I1
betti res comodule I1
beMatrix gens I1
BE1 = map(R^5,R^5,beMatrix gens I1)
transpose(BE1) == -BE1 -- Check that it is alternating.
matrix{ordPfaff(4,BE1)} -- Compare signed maximal ordered pfaffians
gens I1                 -- with original generators.

restart
loadPackage "GradeThreeGorenstein"
R = ZZ/5[x,y,z]
I2 = ideal randomGradeThreeDSGorenstein({4,5,6,6,8,8,8},R)
apply(flatten entries gens I2, i -> (degree i)#0) -- Look at the degree sequence.
BE2 = map(R^7,R^7,beMatrix gens I2)
transpose(BE2) == -BE2 -- Check that it is alternating.
matrix{submaximalPfaffians(BE2)} -- Compare signed maximal ordered pfaffians
gens I2                 -- with original generators.

restart
loadPackage "GradeThreeGorenstein"
R = ZZ/5[x,y,z]
I3 = ideal randomGradeThreePureGorenstein(7,15,R)
apply(flatten entries gens I3, i -> (degree i)#0) -- Look at the degree sequence.
BE3 = map(R^7,R^7,beMatrix gens I3)
transpose(BE3) == -BE3 -- Check that it is alternating.
matrix{submaximalPfaffians(BE3)} -- Compare signed maximal ordered pfaffians
gens I3                 -- with original generators.


--------------------------

restart
uninstallPackage "GradeThreeGorenstein"
installPackage "GradeThreeGorenstein"
viewHelp GradeThreeGorenstein
viewHelp CheckGorenstein
R = QQ[x,y,z]
d = randomGorMinGenDegSeq(5,11)


restart
loadPackage "GradeThreeGorenstein"
R = QQ[x,y,z]
d = randomGorMinGenDegSeq(5,9)
g = randomGradeThreeDSGorenstein(d,R)
betti res comodule ideal g
