restart;

needsPackage "Depth"

-- Assume we're given an odd-size skew-symmetric matrix.
-- This will return the list of signed nxn Pfaffians, ordered correctly.
ordPfaff = method();
ordPfaff(ZZ,Matrix) := (n,M) -> (
    --return apply(n+1, i -> (-1)^i*product(#(factor det submatrix'(M,{i},{i})), j -> (((factor det submatrix'(M,{i},{i}))#j)#0)^((((factor det submatrix'(M,{i},{i}))#j)#1)/2)));
    return apply(numcols M, i -> if submatrix'(M,{i},{i}) == 0 then 0 else (-1)^i*(gens pfaffians(n,submatrix'(M,{i},{i})))_(0,0));
)


-- Computes the number of monomials of degree d in n variables.

numMonomials = method();
numMonomials(ZZ,ZZ) := (d,n) -> (
     return binomial(n+d-1,d);
)

--numMonomials = method();
--numMonomials(RingElement,ZZ) := (d,n) -> (
--     return binomial(n+d-1,d);
--)

-- This method checks whether a proposed degree sequence can occur
-- as the sequence of degrees of minimal generators of a homogeneous grade 3
-- Gorenstein ideal in k[x,y,z].
admissibleDegSeq = method();
admissibleDegSeq(List) := degList -> (
     local diffList; local theta; local n; local m;
     n = #degList;
     if not odd n then return false;
     m = sub((n-1)/2,ZZ);
     if sum(degList) % m != 0 then return false;
     theta = sum(degList)/m;
     diffList = apply(n-1, i -> theta-degList#(i+1)-degList#(n-1-i));
     if min diffList > 0 then return true else return false;
)

monAndEqns = method();
monAndEqns(List) := degList -> (
     local theta; local syzDegMatrix; local diagMatrix;
     local monomialTotal; local eqnTotal; local n; local m;
     if not admissibleDegSeq(degList) then error "Error: Expected admissible degree sequence.";
     n = #degList;
     m = sub((n-1)/2,ZZ);
     theta = sub(sum(degList)/m,ZZ);
     syzDegMatrix = mutableMatrix(ZZ,n,n);
     diagMatrix = mutableMatrix(ZZ,n,n);
     scan(n-1, i -> scan((i+1)..(n-1), j -> syzDegMatrix_(i,j) = theta-degList#i-degList#j));
     scan(n, i -> diagMatrix_(i,i) = theta-2*(degList#i));
     syzDegMatrix = matrix syzDegMatrix;
     diagMatrix = matrix diagMatrix;
     syzDegMatrix = syzDegMatrix+transpose(syzDegMatrix);
     syzDegMatrix = syzDegMatrix+diagMatrix;
     monomialTotal = sum flatten apply(n-1, i -> apply(toList((i+1)..(n-1)), j -> numMonomials(syzDegMatrix_(i,j),3)));
     eqnTotal = sum(n, i -> numMonomials(degList#0+syzDegMatrix_(0,i),3));
     return (monomialTotal,eqnTotal);
)

dimS = method();
dimS(List,Ring) := (degList,RRing) -> (
     local d1; local d2;
     if not admissibleDegSeq(degList) then error "Error: Expected admissible degree sequence.";
     d1 = randomDSGorenstein(degList,RRing);
     d2 = beMatrix d1;
     if class d2 === List then return #d2 else return 1;
)


-- Given a set of generators for a homogeneous grade 3 Gorenstein ideal
-- in 3 variables, this method computes an alternating Buchsbaum-Eisenbud
-- matrix. (or currently returns a list if the space is more than 1-dimensional.)

beMatrix = method();
beMatrix(Matrix) := d1 -> (
     local I; local J; local numGens; local genDeg; local syzDeg; local aboveDiag;
     local coeffList; local SRing; local RRing; local G; local d2; local subMatrix;
     local Mat; local equations; local cCoeff; local eqnMatrix; local genSubs;
     local subMatrix2; local BEMatrix; local theta; local M; local count;
     I = ideal d1;
     numGens = numcols d1;
     -- Check that I_1(d1) satisfies the required condition.
     if numcols vars ring d1 != 3 or not isHomogeneous I or not odd numGens or not isCM(comodule ideal d1) or depth(I,ring d1) != 3 or rank (res comodule I)_3 != 1 then error "Error: Expected an odd number of generators of a grade 3 Gorenstein ideal in a polynomial ring in 3 variables.";
     genDeg = apply(numGens, i -> (degree d1_(0,i))#0); -- What are the degrees of the generators?
     theta = sub(sum(genDeg)/sub((numGens-1)/2,ZZ),ZZ);
     syzDeg = apply(numGens, i -> theta - genDeg#i); -- The degrees of the syzygies.
     aboveDiag = sub(((numGens-1)*numGens)/2,ZZ); -- The number of elements above the diagonal in a skew symmetric matrix.
     count = 1;
     coeffList = {};
     scan(numGens-1, i -> scan(toList((i+1)..(numGens-1)), j -> (
	       scan(numMonomials(syzDeg#j-genDeg#i,3), k -> coeffList = append(coeffList,c_{count,k}));
	       count = count+1;
     	       )
     ));
     SRing = ring d1;
     RRing = (coefficientRing(SRing))[flatten entries vars SRing,coeffList,vars(52..51+aboveDiag)];
     count = 1;
     coeffList = {};
     scan(numGens-1, i -> scan(toList((i+1)..(numGens-1)), j -> (
	       scan(numMonomials(syzDeg#j-genDeg#i,3), k -> coeffList = append(coeffList,c_{count,k}));
	       count = count+1;
     	       )
     ));
     coeffList = apply(coeffList, i -> sub(i,RRing));
     G = {};
     count = 1;
     scan(numGens-1, i -> apply(toList((i+1)..(numGens-1)), j -> (G = append(G,sum(numMonomials(syzDeg#j - genDeg#i,3), k -> sub(c_{count,k},RRing) * sub((flatten entries gens (ideal vars SRing)^(syzDeg#j - genDeg#i))#k,RRing))); count = count+1;)));
     d2 = genericSkewMatrix(RRing,x0,numGens);
     subMatrix = sub(vars SRing,RRing)|matrix{flatten {coeffList,G}};
     Mat = sub(d2,subMatrix);
     equations = sub(d1,RRing)*Mat;
     -- The entry in the i-th column of `equations' will be homogeneous of degree syzDeg#i.
     -- Since all of the coefficients in the product must vanish, this next line
     -- extracts all of these equations in terms of the c_{i,j}'s.
     cCoeff = apply(numGens, i -> (coefficients(equations_(0,i), Variables => flatten entries sub(vars SRing,RRing), Monomials => flatten entries sub(gens (ideal vars SRing)^(syzDeg#i),RRing)))#1);
     print cCoeff; -- Prints the equations which must be satisfied.
     eqnMatrix = map(RRing^0,RRing^#coeffList,0);
     -- The vectors in ker eqnMatrix will correspond to coefficients of the Buchsbaum-Eisenbud matrix.
     scan(numGens, i -> scan(numMonomials(syzDeg#i,3), j -> eqnMatrix = eqnMatrix||(transpose (coefficients((cCoeff#i)_(j,0),Variables => coeffList, Monomials => coeffList))#1)));
     print eqnMatrix;
     print numrows eqnMatrix;
     print mingens ker eqnMatrix;
     print numcols mingens ker eqnMatrix;
     print mingens image eqnMatrix;
     print numcols mingens image eqnMatrix;
     genSubs = transpose mingens ker eqnMatrix;
     subMatrix2 = apply(numrows genSubs, i -> sub(vars SRing,RRing)|genSubs^{i}|submatrix'(vars RRing,,{0..(#coeffList+2)}));
     BEMatrix = apply(#subMatrix2, i -> sub(Mat,subMatrix2#i));
     use SRing; -- Bad. Get rid of this.
     if #BEMatrix == 1 then return sub(BEMatrix#0,SRing) else return apply(#BEMatrix, i -> sub(BEMatrix#i,SRing));
)

-- Method: randomGorenstein
-- Inputs: (ZZ,ZZ,Ring) -> (Number of minimal generators,bound on the degrees of the generators,polynomial ring in 3 variables over a field)
-- Output: Minimal generators of a homogeneous grade 3 Gorenstein ideal in the given polynomial ring.
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

restart
load "gorensteinTest.m2"
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

restart
load "gorensteinTest.m2"
R = QQ[x,y,z]
I = ideal(x^6,y^6,z^6):(ideal(x+y+z))^6 -- 7 generated homogeneous grade 3 Gorenstein ideal in QQ[x,y,z]
betti res comodule I -- 6 generators of degree 5 and 1 of degree 6
Gens = gens I
gbPresMatrix = map(R^7,R^7,(res comodule I).dd_2) -- Does not give an alternating presentation matrix.
transpose gbPresMatrix == -gbPresMatrix -- Check that it's not alternating.
d2 = map(R^7,R^7,beMatrix Gens)
transpose d2 == -d2
Gens*d2
pfaffians(6,d2) == I


-- Running random examples to try to find a BE matrix space that has
-- dimension larger than 1.

restart
load "gorensteinTest.m2"
R = QQ[x,y,z]
n = 5 -- n is the number of generators.
dimension = 1
while dimension == 1 do (
     R = QQ[x,y,z];
     print "Computing a new d1.";
     d1 = randomGorenstein(n,3,R); -- The middle parameter is a bound on the degrees of the generators.
     d2 = beMatrix(d1);
     if class d2 === Matrix then dimension = 1 else dimension = #d2;
     print concatenate("Dimension found: ",toString dimension);
)
scan(#d2, i -> print(i,rank d2#i, pfaffians(n-1,d2#i) == ideal d1));
print toString d1;
print toString d2#1;
--
found = false
while found == false do (
     a = random(1,3);
     b = random(0,4);
     c = random(1,3);
     d = random(0,4);
     if rank(a*d2#(b) + c*d2#(d)) == 4 then found = true;
);
print (a,b,c,d)
--
rank(d2#5+d2#6)
pfaffians(n-1,d2#5+d2#6) == ideal d1
d2#5


-- Example
restart
load "gorensteinTest.m2"
R = QQ[x,y,z]
-- minimal generators in degrees {2,5,5,7,7}
d1 = matrix {{-(1969/175)*x^2-(181/30)*x*y+(14/15)*y^2-(793/30)*x*z-(67/9)*y*z-(50/21)*z^2, (107/18)*x^5+(11699/540)*x^4*y+(83/18)*x^3*y^2+(191/50)*x^2*y^3+(3509/200)*x*y^4+(147/40)*y^5+(5611/675)*x^4*z+(7787/270)*x^3*y*z+(1441/70)*x^2*y^2*z+(2159/225)*x*y^3*z+(89/40)*y^4*z+(479/45)*x^3*z^2+(269/9)*x^2*y*z^2+(5533/420)*x*y^2*z^2+(19/8)*y^3*z^2+(8251/1350)*x^2*z^3+(3847/1575)*x*y*z^3+(28/45)*y^2*z^3+(2197/630)*x*z^4-(22/63)*y*z^4-(25/126)*z^5, (51/350)*x^5+(1439/630)*x^4*y+(741/350)*x^3*y^2+(359/140)*x^2*y^3+(467/350)*x*y^4-(153/100)*y^5+(73/105)*x^4*z+(2153/525)*x^3*y*z+(8479/1470)*x^2*y^2*z+(93/28)*x*y^3*z+(1623/700)*y^4*z+(502/105)*x^3*z^2+(41/15)*x^2*y*z^2-(27/28)*x*y^2*z^2+(13/140)*y^3*z^2+(913/105)*x^2*z^3+(1828/175)*x*y*z^3+(253/175)*y^2*z^3+(148/35)*x*z^4+(172/245)*y*z^4+(115/49)*z^5, -(41/20)*x^7-(2953/360)*x^6*y-(100037/1800)*x^5*y^2-(35033/420)*x^4*y^3-(5039/100)*x^3*y^4-(3209/100)*x^2*y^5-(3541/90)*x*y^6-(733/45)*y^7-(1663/315)*x^6*z-(390367/22680)*x^5*y*z-(1258843/45360)*x^4*y^2*z-(1249607/52920)*x^3*y^3*z-(155387/8400)*x^2*y^4*z-(11437/525)*x*y^5*z-(2971/270)*y^6*z-(52147/1620)*x^5*z^2-(441479/6300)*x^4*y*z^2-(585259/5880)*x^3*y^2*z^2-(256967/3780)*x^2*y^3*z^2-(74759/900)*x*y^4*z^2-(10447/420)*y^5*z^2-(8839/420)*x^4*z^3-(530419/7350)*x^3*y*z^3-(27763/630)*x^2*y^2*z^3-(578107/11025)*x*y^3*z^3-(63437/3150)*y^4*z^3-(265999/6300)*x^3*z^4-(4047/50)*x^2*y*z^4-(113467/1050)*x*y^2*z^4-(113209/3150)*y^3*z^4-(5111/315)*x^2*z^5-(6451/315)*x*y*z^5-(79/35)*y^2*z^5-(119843/9450)*x*z^6+(126271/28350)*y*z^6-(53/105)*z^7, (403/1400)*x^7+(29191/2520)*x^6*y+(106271/3780)*x^5*y^2+(1643879/58800)*x^4*y^3+(19457/560)*x^3*y^4+(64229/2800)*x^2*y^5+(5147/400)*x*y^6+(853/60)*y^7-(2143/630)*x^6*z+(32191/1800)*x^5*y*z+(31145/882)*x^4*y^2*z+(1495547/75600)*x^3*y^3*z+(25139/1260)*x^2*y^4*z+(59383/5040)*x*y^5*z+(163/20)*y^6*z-(17231/3780)*x^5*z^2+(651307/11760)*x^4*y*z^2+(1554499/25200)*x^3*y^2*z^2+(235409/11760)*x^2*y^3*z^2+(90317/1680)*x*y^4*z^2+(59057/2520)*y^5*z^2-(8889/700)*x^4*z^3+(6811/120)*x^3*y*z^3+(138373/3780)*x^2*y^2*z^3+(31943/1260)*x*y^3*z^3+(41717/2520)*y^4*z^3+(407/35)*x^3*z^4+(165923/2940)*x^2*y*z^4+(2129/126)*x*y^2*z^4+(52013/2520)*y^3*z^4-(2161/1470)*x^2*z^5-(4517/1260)*x*y*z^5-(3581/756)*y^2*z^5+(40/63)*x*z^6-(24127/945)*y*z^6-(4/5)*z^7}}
mingens ideal d1 -- 5 minimal generators
d2 = {matrix {{0, -38556*x^6-604380*x^5*y-560196*x^4*y^2-678510*x^3*y^3-353052*x^2*y^4+404838*x*y^5-183960*x^5*z-1085112*x^4*y*z-1526220*x^3*y^2*z-878850*x^2*y^3*z-613494*x*y^4*z-1265040*x^4*z^2-723240*x^3*y*z^2+255150*x^2*y^2*z^2-24570*x*y^3*z^2-2300760*x^3*z^3-2763936*x^2*y*z^3-382536*x*y^2*z^3-1118880*x^2*z^4-185760*x*y*z^4-621000*x*z^5, 1572900*x^6+5732510*x^5*y+1220100*x^4*y^2+1010772*x^3*y^3+4642407*x^2*y^4+972405*x*y^5+2199512*x^5*z+7631260*x^4*y*z+5446980*x^3*y^2*z+2538984*x^2*y^3*z+588735*x*y^4*z+2816520*x^4*z^2+7908600*x^3*y*z^2+3485790*x^2*y^2*z^2+628425*x*y^3*z^2+1617196*x^3*z^3+646296*x^2*y*z^3+164640*x*y^2*z^3+922740*x^2*z^4-92400*x*y*z^4-52500*x*z^5, 0, 0}, {38556*x^6+604380*x^5*y+560196*x^4*y^2+678510*x^3*y^3+353052*x^2*y^4-404838*x*y^5+183960*x^5*z+1085112*x^4*y*z+1526220*x^3*y^2*z+878850*x^2*y^3*z+613494*x*y^4*z+1265040*x^4*z^2+723240*x^3*y*z^2-255150*x^2*y^2*z^2+24570*x*y^3*z^2+2300760*x^3*z^3+2763936*x^2*y*z^3+382536*x*y^2*z^3+1118880*x^2*z^4+185760*x*y*z^4+621000*x*z^5, 0, 2977128*x^3+1596420*x^2*y-246960*x*y^2+6994260*x^2*z+1969800*x*y*z+630000*x*z^2, 0, 0}, {-1572900*x^6-5732510*x^5*y-1220100*x^4*y^2-1010772*x^3*y^3-4642407*x^2*y^4-972405*x*y^5-2199512*x^5*z-7631260*x^4*y*z-5446980*x^3*y^2*z-2538984*x^2*y^3*z-588735*x*y^4*z-2816520*x^4*z^2-7908600*x^3*y*z^2-3485790*x^2*y^2*z^2-628425*x*y^3*z^2-1617196*x^3*z^3-646296*x^2*y*z^3-164640*x*y^2*z^3-922740*x^2*z^4+92400*x*y*z^4+52500*x*z^5, -2977128*x^3-1596420*x^2*y+246960*x*y^2-6994260*x^2*z-1969800*x*y*z-630000*x*z^2, 0, 0, 0}, {0, 0, 0, 0, 0}, {0, 0, 0, 0, 0}}, matrix {{0, -38556*x^5*y-604380*x^4*y^2-560196*x^3*y^3-678510*x^2*y^4-353052*x*y^5+404838*y^6-183960*x^4*y*z-1085112*x^3*y^2*z-1526220*x^2*y^3*z-878850*x*y^4*z-613494*y^5*z-1265040*x^3*y*z^2-723240*x^2*y^2*z^2+255150*x*y^3*z^2-24570*y^4*z^2-2300760*x^2*y*z^3-2763936*x*y^2*z^3-382536*y^3*z^3-1118880*x*y*z^4-185760*y^2*z^4-621000*y*z^5, 1572900*x^5*y+5732510*x^4*y^2+1220100*x^3*y^3+1010772*x^2*y^4+4642407*x*y^5+972405*y^6+2199512*x^4*y*z+7631260*x^3*y^2*z+5446980*x^2*y^3*z+2538984*x*y^4*z+588735*y^5*z+2816520*x^3*y*z^2+7908600*x^2*y^2*z^2+3485790*x*y^3*z^2+628425*y^4*z^2+1617196*x^2*y*z^3+646296*x*y^2*z^3+164640*y^3*z^3+922740*x*y*z^4-92400*y^2*z^4-52500*y*z^5, 0, 0}, {38556*x^5*y+604380*x^4*y^2+560196*x^3*y^3+678510*x^2*y^4+353052*x*y^5-404838*y^6+183960*x^4*y*z+1085112*x^3*y^2*z+1526220*x^2*y^3*z+878850*x*y^4*z+613494*y^5*z+1265040*x^3*y*z^2+723240*x^2*y^2*z^2-255150*x*y^3*z^2+24570*y^4*z^2+2300760*x^2*y*z^3+2763936*x*y^2*z^3+382536*y^3*z^3+1118880*x*y*z^4+185760*y^2*z^4+621000*y*z^5, 0, 2977128*x^2*y+1596420*x*y^2-246960*y^3+6994260*x*y*z+1969800*y^2*z+630000*y*z^2, 0, 0}, {-1572900*x^5*y-5732510*x^4*y^2-1220100*x^3*y^3-1010772*x^2*y^4-4642407*x*y^5-972405*y^6-2199512*x^4*y*z-7631260*x^3*y^2*z-5446980*x^2*y^3*z-2538984*x*y^4*z-588735*y^5*z-2816520*x^3*y*z^2-7908600*x^2*y^2*z^2-3485790*x*y^3*z^2-628425*y^4*z^2-1617196*x^2*y*z^3-646296*x*y^2*z^3-164640*y^3*z^3-922740*x*y*z^4+92400*y^2*z^4+52500*y*z^5, -2977128*x^2*y-1596420*x*y^2+246960*y^3-6994260*x*y*z-1969800*y^2*z-630000*y*z^2, 0, 0, 0}, {0, 0, 0, 0, 0}, {0, 0, 0, 0, 0}}, matrix {{0, 642073068*x^6+10245567780*x^5*y+12163486188*x^4*y^2+13926546270*x^3*y^3+9061586856*x^2*y^4-5085953334*x*y^5-1898690220*y^6+3005651880*x^5*z+18026572536*x^4*y*z+29665022940*x^3*y^2*z+20775695850*x^2*y^3*z+13808744082*x*y^4*z+3484543860*y^5*z+20790771120*x^4*z^2+16349485320*x^3*y*z^2-3146347350*x^2*y^2*z^2-2105764290*x*y^3*z^2-805007700*y^4*z^2+36416996280*x^3*z^3+55733530608*x^2*y*z^3+19715956848*x*y^2*z^3+1757238840*y^3*z^3+15181568640*x^2*z^4+4195104480*x*y*z^4+297410400*y^2*z^4+8663193000*x*z^5+2633850000*y*z^5-931500000*z^6, -26193503700*x^6-102840390030*x^5*y-47203797200*x^4*y^2-22554655116*x^3*y^3-82050524451*x^2*y^4-37966349295*x*y^5-4560579450*y^6-34269123336*x^5*z-128800319060*x^4*y*z-124669017340*x^3*y^2*z-66311878752*x^2*y^3*z-14748428415*x*y^4*z-1302559650*y^5*z-43604239560*x^4*z^2-133464504600*x^3*y*z^2-86969724870*x^2*y^2*z^2-23005040625*x*y^3*z^2-2064210750*y^4*z^2-22706384988*x^3*z^3-6484516528*x^2*y*z^3-544193160*x*y^2*z^3+170475900*y^3*z^3-12940595220*x^2*z^4-1819469400*x*y*z^4+680316000*y^2*z^4+2258392500*x*z^5+107625000*y*z^5-78750000*z^6, 0, 0}, {-642073068*x^6-10245567780*x^5*y-12163486188*x^4*y^2-13926546270*x^3*y^3-9061586856*x^2*y^4+5085953334*x*y^5+1898690220*y^6-3005651880*x^5*z-18026572536*x^4*y*z-29665022940*x^3*y^2*z-20775695850*x^2*y^3*z-13808744082*x*y^4*z-3484543860*y^5*z-20790771120*x^4*z^2-16349485320*x^3*y*z^2+3146347350*x^2*y^2*z^2+2105764290*x*y^3*z^2+805007700*y^4*z^2-36416996280*x^3*z^3-55733530608*x^2*y*z^3-19715956848*x*y^2*z^3-1757238840*y^3*z^3-15181568640*x^2*z^4-4195104480*x*y*z^4-297410400*y^2*z^4-8663193000*x*z^5-2633850000*y*z^5+931500000*z^6, 0, -49578112584*x^3-40547912580*x^2*y-3374584920*x*y^2+1158242400*y^3-112009719780*x^2*z-63211528800*x*y*z-9608802000*y^2*z+945000000*z^3, 0, 0}, {26193503700*x^6+102840390030*x^5*y+47203797200*x^4*y^2+22554655116*x^3*y^3+82050524451*x^2*y^4+37966349295*x*y^5+4560579450*y^6+34269123336*x^5*z+128800319060*x^4*y*z+124669017340*x^3*y^2*z+66311878752*x^2*y^3*z+14748428415*x*y^4*z+1302559650*y^5*z+43604239560*x^4*z^2+133464504600*x^3*y*z^2+86969724870*x^2*y^2*z^2+23005040625*x*y^3*z^2+2064210750*y^4*z^2+22706384988*x^3*z^3+6484516528*x^2*y*z^3+544193160*x*y^2*z^3-170475900*y^3*z^3+12940595220*x^2*z^4+1819469400*x*y*z^4-680316000*y^2*z^4-2258392500*x*z^5-107625000*y*z^5+78750000*z^6, 49578112584*x^3+40547912580*x^2*y+3374584920*x*y^2-1158242400*y^3+112009719780*x^2*z+63211528800*x*y*z+9608802000*y^2*z-945000000*z^3, 0, 0, 0}, {0, 0, 0, 0, 0}, {0, 0, 0, 0, 0}}, matrix {{0, 636826932*x^6+5472687220*x^5*y+13365688812*x^4*y^2+16425908730*x^3*y^3+8072950644*x^2*y^4-275661666*x*y^5+2594262720*y^6+2468348120*x^5*z+12548902464*x^4*y*z+22947987060*x^3*y^2*z+18562404150*x^2*y^3*z+13778168418*x*y^4*z+5442263640*y^5*z+15560228880*x^4*z^2+17144464680*x^3*y*z^2+6006547350*x^2*y^2*z^2+2999576790*x*y^3*z^2+6593920200*y^4*z^2+23622003720*x^3*z^3+46335919392*x^2*y*z^3+22516723152*x*y^2*z^3+8846291160*y^3*z^3+14365431360*x^2*z^4+13823795520*x*y*z^4+15967389600*y^2*z^4+7386807000*x*z^5+6102400000*y*z^5+1606500000*z^6, -11160246300*x^6-57970609970*x^5*y-46529440300*x^4*y^2-15090769884*x^3*y^3-44908335549*x^2*y^4-37310854455*x*y^5-5153976800*y^6-15993676664*x^5*z-84363190940*x^4*y*z-96232157660*x^3*y^2*z-44266246248*x^2*y^3*z-27746016585*x*y^4*z-5145709100*y^5*z-11058760440*x^4*z^2-93911345400*x^3*y*z^2-87571775130*x^2*y^2*z^2-31470721875*x*y^3*z^2-4305570500*y^4*z^2-14573515012*x^3*z^3-26606338472*x^2*y*z^3+3332363160*x*y^2*z^3+3227324100*y^3*z^3-3827904780*x^2*z^4-4676355600*x*y*z^4+7446684000*y^2*z^4+2204107500*x*z^5+16233000000*y*z^5+866250000*z^6, 1102500000*x^4+4200000000*x^3*y+1102500000*x^2*y^2+1968750000*x*y^3+3543750000*y^4+1575000000*x^3*z+4725000000*x^2*y*z+2362500000*x*y^2*z+1181250000*y^3*z+2625000000*x^2*z^2+6300000000*x*y*z^2+1968750000*y^2*z^2+1575000000*x*z^3+450000000*y*z^3+900000000*z^4, 350000000*x^4+4200000000*x^3*y+4725000000*x^2*y^2+2835000000*x*y^3+2835000000*y^4+1260000000*x^3*z+525000000*x^2*y*z+900000000*x*y^2*z+945000000*y^3*z+4725000000*x^2*z^2+7875000000*x*y*z^2+1575000000*y^2*z^2+2205000000*x*z^3+630000000*y*z^3+1575000000*z^4}, {-636826932*x^6-5472687220*x^5*y-13365688812*x^4*y^2-16425908730*x^3*y^3-8072950644*x^2*y^4+275661666*x*y^5-2594262720*y^6-2468348120*x^5*z-12548902464*x^4*y*z-22947987060*x^3*y^2*z-18562404150*x^2*y^3*z-13778168418*x*y^4*z-5442263640*y^5*z-15560228880*x^4*z^2-17144464680*x^3*y*z^2-6006547350*x^2*y^2*z^2-2999576790*x*y^3*z^2-6593920200*y^4*z^2-23622003720*x^3*z^3-46335919392*x^2*y*z^3-22516723152*x*y^2*z^3-8846291160*y^3*z^3-14365431360*x^2*z^4-13823795520*x*y*z^4-15967389600*y^2*z^4-7386807000*x*z^5-6102400000*y*z^5-1606500000*z^6, 0, -21306337416*x^3-20255277420*x^2*y-5654890080*x*y^2+6345057600*y^3-60821780220*x^2*z-63773896200*x*y*z-10801448000*y^2*z, 2025000000*x+630000000*y+4725000000*z, 315000000*x+1575000000*y+1800000000*z}, {11160246300*x^6+57970609970*x^5*y+46529440300*x^4*y^2+15090769884*x^3*y^3+44908335549*x^2*y^4+37310854455*x*y^5+5153976800*y^6+15993676664*x^5*z+84363190940*x^4*y*z+96232157660*x^3*y^2*z+44266246248*x^2*y^3*z+27746016585*x*y^4*z+5145709100*y^5*z+11058760440*x^4*z^2+93911345400*x^3*y*z^2+87571775130*x^2*y^2*z^2+31470721875*x*y^3*z^2+4305570500*y^4*z^2+14573515012*x^3*z^3+26606338472*x^2*y*z^3-3332363160*x*y^2*z^3-3227324100*y^3*z^3+3827904780*x^2*z^4+4676355600*x*y*z^4-7446684000*y^2*z^4-2204107500*x*z^5-16233000000*y*z^5-866250000*z^6, 21306337416*x^3+20255277420*x^2*y+5654890080*x*y^2-6345057600*y^3+60821780220*x^2*z+63773896200*x*y*z+10801448000*y^2*z, 0, 2520000000*x+3675000000*y+1312500000*z, 14175000000*x+5512500000*y+1750000000*z}, {-1102500000*x^4-4200000000*x^3*y-1102500000*x^2*y^2-1968750000*x*y^3-3543750000*y^4-1575000000*x^3*z-4725000000*x^2*y*z-2362500000*x*y^2*z-1181250000*y^3*z-2625000000*x^2*z^2-6300000000*x*y*z^2-1968750000*y^2*z^2-1575000000*x*z^3-450000000*y*z^3-900000000*z^4, -2025000000*x-630000000*y-4725000000*z, -2520000000*x-3675000000*y-1312500000*z, 0, 0}, {-350000000*x^4-4200000000*x^3*y-4725000000*x^2*y^2-2835000000*x*y^3-2835000000*y^4-1260000000*x^3*z-525000000*x^2*y*z-900000000*x*y^2*z-945000000*y^3*z-4725000000*x^2*z^2-7875000000*x*y*z^2-1575000000*y^2*z^2-2205000000*x*z^3-630000000*y*z^3-1575000000*z^4, -315000000*x-1575000000*y-1800000000*z, -14175000000*x-5512500000*y-1750000000*z, 0, 0}}}
F = chainComplex(map(R^1,R^5,d1),map(R^5,R^5,d2#3),map(R^5,R^1,transpose(d1)))
--G = chainComplex(map(R^1,R^5,d1),map(R^5,R^5,d2#3),map(R^5,R^1,transpose(d1)))
G = chainComplex(map(R^1,R^5,d1),map(R^5,R^5,syz d1),map(R^5,R^1,syz(syz d1)))
-- Make sure F is a complex.
(F.dd_1)*(F.dd_2)
(F.dd_2)*(F.dd_3)
-- Make sure G is a complex.
(G.dd_1)*(G.dd_2)
(G.dd_2)*(G.dd_3)

f = extend(G,F,id_(R^1), Verify => true) -- Find comparison maps between complexes.
print f_2
rank f_2
print det f_2
f_2*transpose(d1)
(f_1)*(d2#3) - (G.dd_2)*(f_2)
syz d1
rank f_2

mingens image f_2


-- An example where none of the given generators for the vector space
-- have the correct rank.
-- *** This example has 7 (not minimal) generators of degrees {3,3,4,4,4,4,5}. ***
-- *** If we know the minimal generators, then this cannot happen. ***
-- We can perturb the generators until we find an element of rank 6,
-- and it seems to always be the case that such an element has its
-- 6x6 pfaffians generating the same ideal as d1.

-- *** Note: These 7 polynomials don't minimally generate the Gorenstein ideal.
-- It only requires 5 generators. ***
d1 = matrix {{(9307/378)*x^3-(48863/1890)*x^2*y-(23237/189)*x*y^2+(809/14)*y^3-(58519/16200)*x^2*z-(404327/4320)*x*y*z-(37319/420)*y^2*z-(6762149/90720)*x*z^2-(531467/7560)*y*z^2-(4105/72)*z^3, -(793/432)*x^3+(220607/7560)*x^2*y+(249959/1620)*x*y^2+(1943/135)*y^3-(61519/6048)*x^2*z+(118721/540)*x*y*z+(2671181/37800)*y^2*z+(1116377/60480)*x*z^2+(736877/6300)*y*z^2+(5471/108)*z^3, -(2921/135)*x^4-(151211/10800)*x^3*y+(4769953/226800)*x^2*y^2-(3817/60)*x*y^3-(1137/14)*y^4-(46141/8640)*x^3*z-(893171/43200)*x^2*y*z+(55987/1200)*x*y^2*z-(12109/1260)*y^3*z+(299393/6480)*x^2*z^2+(242819/7200)*x*y*z^2+(1196627/37800)*y^2*z^2+(37309/1080)*x*z^3+(269707/5400)*y*z^3+(47/540)*z^4, -(758669/5040)*x^4-(67339/720)*x^3*y-(789259/7560)*x^2*y^2-(6876181/13230)*x*y^3-(63629/945)*y^4-(920569/4725)*x^3*z-(3029431/12600)*x^2*y*z-(2538623/12600)*x*y^2*z-(840026/4725)*y^3*z-(824347/4725)*x^2*z^2-(5494037/25200)*x*y*z^2-(2848493/9450)*y^2*z^2-(1973099/15120)*x*z^3+(72637/6300)*y*z^3-(5359/100)*z^4, (225491/4320)*x^4+(264641/4320)*x^3*y+(1130351/18144)*x^2*y^2+(810239/3780)*x*y^3+(227701/1620)*y^4+(262619/4320)*x^3*z+(1914503/15120)*x^2*y*z+(62635/756)*x*y^2*z+(294451/5670)*y^3*z+(149407/4320)*x^2*z^2+(99719/945)*x*y*z^2+(544123/7560)*y^2*z^2+(686383/12960)*x*z^3-(23693/420)*y*z^3+(170039/3240)*z^4, -(197881/11340)*x^4-(682523/22680)*x^3*y-(79232/8505)*x^2*y^2-(1520767/39690)*x*y^3+(3296/189)*y^4-(37974647/907200)*x^3*z-(32321033/907200)*x^2*y*z-(804977/13608)*x*y^2*z+(431309/22680)*y^3*z-(2586613/75600)*x^2*z^2-(164279/3024)*x*y*z^2-(57451/840)*y^2*z^2-(2358529/90720)*x*z^3-(275087/25200)*y*z^3-(22679/1200)*z^4, (49579/10080)*x^5+(1372327/25200)*x^4*y+(49924319/453600)*x^3*y^2-(6456211/529200)*x^2*y^3+(39069617/238140)*x*y^4-(6103/945)*y^5+(706123/19200)*x^4*z+(17674297/80640)*x^3*y*z+(149804417/1944000)*x^2*y^2*z+(479299447/1587600)*x*y^3*z+(220931/4536)*y^4*z+(95110633/1814400)*x^3*z^2+(4904883/28000)*x^2*y*z^2+(665837/3240)*x*y^2*z^2+(2129459/11340)*y^3*z^2+(25902797/544320)*x^2*z^3+(10724257/75600)*x*y*z^3+(14012713/75600)*y^2*z^3+(290467/20160)*x*z^4+(4422139/56700)*y*z^4+(190961/10800)*z^5}}
mingens ideal d1 -- 5 minimal generators
d2 = beMatrix(d1)
#d2
scan(#d2, i -> print(i,rank d2#i, pfaffians(6,d2#i) == ideal d1));

found = false
while found == false do (
     a = random(1,3);
     b = random(0,4);
     c = random(1,3);
     d = random(0,4);
     if rank(a*d2#(b) + c*d2#(d)) == 6 then found = true;
);
print (a,b,c,d)
pfaffians(6,a*d2#(b) + c*d2#(d)) == ideal d1

P = ideal d1
F = chainComplex(map(R^1,R^7,d1),map(R^7,R^7,a*d2#(b) + c*d2#(d)),map(R^7,R^1,transpose(d1)))
G = res comodule P
-- Make sure F is a complex.
(F.dd_1)*(F.dd_2)
(F.dd_2)*(F.dd_3)

f = extend(G,F,id_(R^1))
f_1

-- {2,2,2,3,3} Example
restart
load "gorensteinTest.m2"
R = QQ[x,y,z]
-- minimal generators in degrees {2,2,2,3,3}
d1 = matrix {{(41/10)*x^2+(2353/350)*x*y-(226/315)*y^2+(1798/75)*x*z-(1501/210)*y*z+(1/30)*z^2, -(1823/90)*x^2-(77/15)*x*y-(4/9)*y^2-(503/72)*x*z-(253/90)*y*z-(399/200)*z^2, (1331/630)*x^2+(6383/2100)*x*y+(565/36)*y^2+(2365/216)*x*z+(148/945)*y*z+(371/60)*z^2, -(527/168)*x^3-(2333/2100)*x^2*y-(41791/15120)*x*y^2-(9731/504)*y^3+(799/336)*x^2*z-(34/15)*x*y*z-(1871/1008)*y^2*z-(613/600)*x*z^2-(47/84)*y*z^2+(29/30)*z^3, (209/252)*x^3+(2791/420)*x^2*y+(1609343/16200)*x*y^2+(4679/648)*y^3+(9073/2520)*x^2*z-(4939/1800)*x*y*z-(983/360)*y^2*z+(7939/360)*x*z^2-(5761/720)*y*z^2-(281/60)*z^3}}
d2 = {matrix {{0, 79860*x^2+114894*x*y+593250*y^2+413875*x*z+5920*y*z+233730*z^2, 765660*x^2+194040*x*y+16800*y^2+264075*x*z+106260*y*z+75411*z^2, 0, 0}, {-79860*x^2-114894*x*y-593250*y^2-413875*x*z-5920*y*z-233730*z^2, 0, 154980*x^2+254124*x*y-27120*y^2+906192*x*z-270180*y*z+1260*z^2, 0, 0}, {-765660*x^2-194040*x*y-16800*y^2-264075*x*z-106260*y*z-75411*z^2, -154980*x^2-254124*x*y+27120*y^2-906192*x*z+270180*y*z-1260*z^2, 0, 0, 0}, {0, 0, 0, 0, 0}, {0, 0, 0, 0, 0}}, matrix {{0, -159000*x^2-227772*x*y-1161300*y^2-823970*x*z-11210*y*z-460740*z^2, -1525650*x^2-385560*x*y-30765*y^2-525945*x*z-207480*y*z-147798*z^2, 280*x+1960*y+630*z, 4200*x+630*y+1260*z}, {159000*x^2+227772*x*y+1161300*y^2+823970*x*z+11210*y*z+460740*z^2, 0, -304920*x^2-505728*x*y+55360*y^2-1809864*x*z+542250*y*z, 2520*x+2520*y+12600*z, 252*x+1800*y+5880*z}, {1525650*x^2+385560*x*y+30765*y^2+525945*x*z+207480*y*z+147798*z^2, 304920*x^2+505728*x*y-55360*y^2+1809864*x*z-542250*y*z, 0, 25200*x+2016*y+1008*z, 252*x+5040*y+1260*z}, {-280*x-1960*y-630*z, -2520*x-2520*y-12600*z, -25200*x-2016*y-1008*z, 0, 4032}, {-4200*x-630*y-1260*z, -252*x-1800*y-5880*z, -252*x-5040*y-1260*z, -4032, 0}}}


d2 = matrix {{0, -159000*x^2-227772*x*y-1161300*y^2-823970*x*z-11210*y*z-460740*z^2, -1525650*x^2-385560*x*y-30765*y^2-525945*x*z-207480*y*z-147798*z^2, 280*x+1960*y+630*z, 4200*x+630*y+1260*z}, {159000*x^2+227772*x*y+1161300*y^2+823970*x*z+11210*y*z+460740*z^2, 0, -304920*x^2-505728*x*y+55360*y^2-1809864*x*z+542250*y*z, 2520*x+2520*y+12600*z, 252*x+1800*y+5880*z}, {1525650*x^2+385560*x*y+30765*y^2+525945*x*z+207480*y*z+147798*z^2, 304920*x^2+505728*x*y-55360*y^2+1809864*x*z-542250*y*z, 0, 25200*x+2016*y+1008*z, 252*x+5040*y+1260*z}, {-280*x-1960*y-630*z, -2520*x-2520*y-12600*z, -25200*x-2016*y-1008*z, 0, 4032}, {-4200*x-630*y-1260*z, -252*x-1800*y-5880*z, -252*x-5040*y-1260*z, -4032, 0}}
mingens ideal d1 -- 5 minimal generators
F = chainComplex(map(R^1,R^5,d1),map(R^5,R^5,d2#3),map(R^5,R^1,transpose(d1)))
--G = chainComplex(map(R^1,R^5,d1),map(R^5,R^5,d2#3),map(R^5,R^1,transpose(d1)))
G = chainComplex(map(R^1,R^5,d1),map(R^5,R^5,syz d1),map(R^5,R^1,syz(syz d1)))
-- Make sure F is a complex.
(F.dd_1)*(F.dd_2)
(F.dd_2)*(F.dd_3)
-- Make sure G is a complex.
(G.dd_1)*(G.dd_2)
(G.dd_2)*(G.dd_3)

f = extend(G,F,id_(R^1), Verify => true) -- Find comparison maps between complexes.
print f_2
rank f_2
print det f_2
f_2*transpose(d1)
(f_1)*(d2#3) - (G.dd_2)*(f_2)
syz d1
rank f_2


------------------ Example for the dissertation ---------------------
restart;
load "gorensteinTest.m2"
--d1 = randomGorenstein(5,5,ZZ/5[x,y,z])
--numcols mingens ideal d1 == numcols d1
--print toString d1
R = ZZ/5[x,y,z]
d1 = matrix {{-x^2+x*y+2*x*z, -2*x^2+x*y-2*y^2+2*y*z+2*z^2, -2*x*y+x*z, x^4+x*y^3-x^3*z+x^2*y*z-2*x*y^2*z+2*y^3*z-x^2*z^2-x*y*z^2+y*z^3+z^4, x^3*y-x^2*y^2+y^4+x^3*z+x*y^2*z+y^3*z+x*y*z^2+y^2*z^2+2*x*z^3+2*y*z^3+z^4}}
B = beMatrix(d1)
#B
scan(B,i -> (print i;print newline;))
tex B
scan(B,i -> print rank i)
d2 = (B)#3
tex d2
rank d2
D2=d2-3*(B#0)-2*(B#1)
rank D2
ordPfaff(4,D2) == ordPfaff(4,d2)
d1
tex matrix{ordPfaff(4,d2)}
d1
tex flatten entries d1


-----------------------------------------------------------------
-- Testing whether the algorithm works in characteristic 2
-----------------------------------------------------------------

-- Does Macaulay2 allow nonzero elements on a generic skew-symmetric matrix
-- in characteristic 2?
restart;
R = ZZ/2[x,y,z]
S = ZZ/2[vars(52)..vars(70)]
vars S
M = genericSkewMatrix(S,x0,5)

-- Apparently not... so these are really generic *alternating* matrices on ZZ/2.

-- This code generates random grade 3 Gorenstein ideals in ZZ/2[x,y,z]
-- then computes a basis for S(d_1(g)).

restart;
load "gorensteinTest.m2"
d1 = randomGorenstein(5,8,ZZ/2[x,y,z])
numcols mingens ideal d1 == numcols d1 -- Double check that the generators are minimal.
mingens ideal d1
beList = beMatrix d1
if class beList === List then print("Number of generators of S(d1(g)):"|toString #beList) else print("S(d1(g)) is one-dimensional.")
if class beList === List then scan(beList, i -> print rank i)
if class beList === List then d2 = (beList)#(#beList - 1) else d2 = beList
d1*d2
Pfaff = matrix{ordPfaff(4,d2)}
d1
Pfaff == d1

-----------------------------------------------------------------
-- Examples to try to understand the dimension of the vector space
-- S(d_1(g)) as a function of the degree sequence (d_1,...,d_n).
-----------------------------------------------------------------
-- Question: Does the dimension depend on characteristic?
-- It doesn't seem to depend on the characteristic.
-- Question: When is the dimension 1?
-- Question: Is there a polynomial function in the d_i's which gives
-- dim_k(S(d_1(g)))?

-- Is dim_k(S(d_1(g))) = (# of vars in generic alt. matrix)-(# of equations)?
-- Answer: No, a lot of the equations are dependent.
restart;
load "gorensteinTest.m2"
degList = {2,2,5,5,8}
theta = sub(sum(degList)/2,ZZ)
syzDegMatrix = mutableMatrix(ZZ,5,5)
diagMatrix = mutableMatrix(ZZ,5,5)
scan(4, i -> scan((i+1)..4, j -> syzDegMatrix_(i,j) = theta-degList#i-degList#j))
scan(5, i -> diagMatrix_(i,i) = theta-2*(degList#i))
syzDegMatrix = matrix syzDegMatrix
diagMatrix = matrix diagMatrix
syzDegMatrix = syzDegMatrix+transpose(syzDegMatrix)
syzDegMatrix = syzDegMatrix+diagMatrix
monomialTotal = sum flatten apply(4, i -> apply(toList((i+1)..4), j -> numMonomials(syzDegMatrix_(i,j),3)))
eqnTotal = sum(5, i -> numMonomials(degList#0+syzDegMatrix_(0,i),3))
-- So 92 of the vectors will be independent, so that the kernel
-- is 13-dimensional.
d1 = randomDSGorenstein({2,2,5,5,8},ZZ/101[x,y,z])
beMatrix d1

-- Idea: Try to relate the degree sequence to the dimension of the
-- image.  For example, how does {2,2,5,5,8} relate to 92?
-- General procedure for investigating this:
restart;
load "gorensteinTest.m2"
degList = {2,2,4,4,6}
(numMons,numEqns) = monAndEqns(degList)
DS = dimS(degList,ZZ/101[x,y,z])
numMons
numEqns -- Number of equations imposed by vanishing condition.
numMons-DS -- Number of equations which should be independent.
numEqns-(numMons-DS) -- Number of equations which should be dependent.
--{2,2,5,5,8} - (13,105,176,92?,84)
--{2,3,6,6,9} - (13,129,231,116?,115)
--{2,4,7,7,10} - (13,157,294,144?,150)
--{2,5,8,8,11} - (13,189,365,176?,189)
--{2,6,9,9,12} - (13,225,444,212?,232)
--{2,7,10,10,13} - (13,265,531,252?,279)
-- The ? column is increasing by 20+4k each time.
-- Question: Where does the 20 come from?
data = transpose matrix{{92,2,2,5,5,8},{116,2,3,6,6,9},{144,2,4,7,7,10},{176,2,5,8,8,11},{212,2,6,9,9,12},{252,2,7,10,10,13}}
d1 = symbol d1
d2 = symbol d2
S = QQ[DI,d1,d2,d3,d4,d5]
loadPackage "Points"
eqns = (points(data,S))#2
scan(eqns, i -> (print i; print newline;));

-- todo: Think about the degree function which gives the number
-- of coefficients that we need to solve for.  As we use more and more
-- points, do the equations in the ideal "stabilize"?  How are the degrees
-- related to the degree of the function which gives the number
-- of coefficients?

restart;
load "gorensteinTest.m2"
S = QQ[d1,d2,d3,d4,d5]
degList = {d1,d2,d3,d4,d5}
n = #degList
m = sub((n-1)/2,ZZ)
theta = sum(degList)/m
syzDegMatrix = mutableMatrix(S,n,n)
diagMatrix = mutableMatrix(S,n,n)
scan(n-1, i -> scan((i+1)..(n-1), j -> syzDegMatrix_(i,j) = theta-degList#i-degList#j))
scan(n, i -> diagMatrix_(i,i) = theta-2*(degList#i))
syzDegMatrix = matrix syzDegMatrix
diagMatrix = matrix diagMatrix
syzDegMatrix = syzDegMatrix+transpose(syzDegMatrix)
syzDegMatrix = syzDegMatrix+diagMatrix]
-- todo: Work this out by hand.  What degree does it have in d1,...,d5?
monomialTotal = sum flatten apply(n-1, i -> apply(toList((i+1)..(n-1)), j -> numMonomials(syzDegMatrix_(i,j),3)))
eqnTotal = sum(n, i -> numMonomials(degList#0+syzDegMatrix_(0,i),3))

-- todo: Try doing this for 6 random degree sequences, then using points.

numGens = 5
genLimit = 8
data = matrix mutableMatrix(ZZ,6,0)
while numcols data < 6 do (
     randomDegSeq = sort apply(numGens, i -> random(1,genLimit));
     if admissibleDegSeq(randomDegSeq) then (
     	  (numMons,numEqns) = monAndEqns(randomDegSeq);
     	  DS = dimS(randomDegSeq,ZZ/101[x,y,z]);
	  data=data|(transpose matrix{{numMons-DS}|randomDegSeq});
     );
);
data
d2 = symbol d2
S = QQ[DI,d1,d2,d3,d4,d5]
loadPackage "Points"
eqns = (points(data,S))#2
scan(eqns, i -> (print i; print newline;));


-- check? DI = -(5/2)d1+(7/2)d2+(13/2)d3+(11/2)d4+(23/2)d5-63

restart;
load("gorensteinTest.m2")
n = 5; -- n is the number of generators.
degBound = 8; -- degBound is the bound on the degrees of the generators.
p = 101; -- p is the characteristic of the field.
m = 50; -- m is the number of examples to generate.
Examples = new MutableHashTable;
scan(m, i -> (
     d1 = randomGorenstein(n,degBound,ZZ/p[x,y,z]);
     degList = apply(flatten entries d1, i -> first degree i);
     beList = beMatrix d1;
     if Examples#?degList == false then Examples#degList = {};
     if class beList === List then Examples#degList = append(Examples#degList,#beList) else Examples#degList = append(Examples#degList,1);
))
peek Examples
Examples = new HashTable from Examples
scanPairs(Examples, i -> if first i#0 == 2 and last i#0 == 8 then print i)
scanPairs(Examples, i -> print flatten i#0)
M = matrix mutableMatrix(QQ,0,6)
scanPairs(Examples, i -> M = M||(matrix{apply(flatten i#0, j -> sub(j,QQ))}|(matrix{{sub((toList set flatten i#1)#0,QQ)}})))
M
degData = transpose M -- degData gives the degree lists and corresponding vector space dimension of S(d_1(g)) as column vectors to plug into `points'
degData = sub(degData,ZZ)
d1 = symbol d1
S = ZZ[d1,d2,d3,d4,d5,DS]
loadPackage "Points"
eqns = (points(degData,S))#2
#eqns
scan(eqns, i -> (print i; print newline;))

-- todo: Try to make a minimal list of points where there is a different
-- degree in each component, then look at defining equations.  This will
-- get rid of linear equations involving only one variable.

degData = transpose matrix{{2,2,4,5,7,10},{2,2,4,6,8,14},{2,2,5,5,8,13},{2,3,3,8,8,16}}
degData = transpose matrix{{2,2,4,6,8,14},{3,3,5,5,6,3},{2,3,5,6,8,10},{3,5,6,6,6,1},{3,4,4,6,7,4},{4,4,5,5,6,1}}
degData = transpose matrix{{14,2,2,4,6,8},{10,2,3,5,6,8},{1,3,5,6,6,6},{4,3,4,4,6,7},{1,4,4,5,5,6},{1,8,8,8,8,8}}
loadPackage "Points"
S = QQ[DS,d1,d2,d3,d4,d5]
eqns = (points(degData,S))#2
#eqns
scan(eqns, i -> (print i; print newline;))


-- Observation: It seems that if we fix the lowest degree and shift
-- all other degrees up by 1, the dimension doesn't change.

restart;
load "gorensteinTest.m2"
R = ZZ/101[x,y,z]
-- These examples all have dimension 7.
G = randomDSGorenstein({2,3,5,5,7},R)
apply(flatten entries G, i -> first degree i)
#(beMatrix G)
G = randomDSGorenstein({2,4,6,6,8},R)
apply(flatten entries G, i -> first degree i)
#(beMatrix G)
G = randomDSGorenstein({2,5,7,7,9},R)
apply(flatten entries G, i -> first degree i)
#(beMatrix G)
G = randomDSGorenstein({2,6,8,8,10},R)
apply(flatten entries G, i -> first degree i)
#(beMatrix G)
-- These all have dimension 10.
G = randomDSGorenstein({2,2,4,5,7},R)
apply(flatten entries G, i -> first degree i)
#(beMatrix G)
G = randomDSGorenstein({2,3,5,6,8},R)
apply(flatten entries G, i -> first degree i)
#(beMatrix G)
G = randomDSGorenstein({2,4,6,7,9},R)
apply(flatten entries G, i -> first degree i)
#(beMatrix G)
G = randomDSGorenstein({2,5,7,8,10},R)
apply(flatten entries G, i -> first degree i)
#(beMatrix G)

-- Examples generated in ZZ/5[x,y,z] of the dimension of S(d_1(g)) for
-- various degree sequences of homogeneous 5-generated Gorenstein ideals
-- with degrees bounded above by 8.  This is evidence that dim_k S(d_1(g))
-- is a function of the degree sequence.
Examples = MutableHashTable{{{2}, {2}, {2}, {4}, {4}} => {4}                 }
                      {{2}, {2}, {4}, {4}, {6}} => {7, 7, 7}
                      {{2}, {2}, {4}, {5}, {7}} => {10, 10, 10}
                      {{2}, {2}, {4}, {6}, {8}} => {14, 14}
                      {{2}, {2}, {5}, {5}, {8}} => {13, 13}
                      {{2}, {3}, {3}, {5}, {5}} => {4, 4}
                      {{2}, {3}, {3}, {6}, {6}} => {7, 7}
                      {{2}, {3}, {3}, {8}, {8}} => {16}
                      {{2}, {3}, {4}, {6}, {7}} => {8, 8}
                      {{2}, {3}, {4}, {7}, {8}} => {12}
                      {{2}, {3}, {5}, {5}, {7}} => {7, 7}
                      {{2}, {3}, {5}, {6}, {8}} => {10, 10, 10, 10, 10}
                      {{2}, {4}, {4}, {4}, {4}} => {1}
                      {{2}, {4}, {4}, {5}, {5}} => {2}
                      {{2}, {4}, {4}, {6}, {6}} => {4}
                      {{2}, {4}, {6}, {6}, {8}} => {7}
                      {{2}, {5}, {5}, {7}, {7}} => {4, 4}
                      {{2}, {5}, {5}, {8}, {8}} => {7}
                      {{2}, {5}, {6}, {7}, {8}} => {5, 5}
                      {{2}, {6}, {6}, {7}, {7}} => {2}
                      {{2}, {6}, {6}, {8}, {8}} => {4}
                      {{3}, {3}, {3}, {3}, {4}} => {1}
                      {{3}, {3}, {4}, {6}, {8}} => {8}
                      {{3}, {3}, {4}, {7}, {7}} => {7}
                      {{3}, {3}, {4}, {8}, {8}} => {11}
                      {{3}, {3}, {5}, {5}, {6}} => {3}
                      {{3}, {3}, {5}, {5}, {8}} => {7, 7, 7}
                      {{3}, {3}, {5}, {6}, {7}} => {5}
                      {{3}, {4}, {4}, {6}, {7}} => {4, 4, 4, 4, 4, 4}
                      {{3}, {4}, {4}, {7}, {8}} => {7, 7}
                      {{3}, {4}, {5}, {6}, {6}} => {2}
                      {{3}, {4}, {5}, {6}, {8}} => {5, 5}
                      {{3}, {4}, {5}, {7}, {7}} => {4, 4}
                      {{3}, {4}, {6}, {6}, {7}} => {3}
                      {{3}, {5}, {5}, {6}, {7}} => {2}
                      {{3}, {5}, {5}, {7}, {8}} => {4, 4}
                      {{3}, {5}, {6}, {6}, {6}} => {1, 1}
                      {{3}, {5}, {6}, {7}, {7}} => {2}
                      {{3}, {5}, {6}, {8}, {8}} => {4, 4, 4}
                      {{3}, {6}, {7}, {8}, {8}} => {2}
                      {{3}, {7}, {7}, {7}, {8}} => {1, 1, 1}
                      {{3}, {7}, {8}, {8}, {8}} => {1}
                      {{4}, {4}, {4}, {4}, {6}} => {1}
                      {{4}, {4}, {5}, {5}, {6}} => {1, 1, 1, 1}
                      {{4}, {4}, {5}, {7}, {8}} => {4}
                      {{4}, {4}, {6}, {6}, {6}} => {1}
                      {{4}, {5}, {5}, {6}, {6}} => {1, 1}
                      {{4}, {5}, {5}, {8}, {8}} => {4, 4}
                      {{4}, {6}, {6}, {7}, {7}} => {1}
                      {{4}, {6}, {7}, {7}, {8}} => {1}
                      {{4}, {7}, {7}, {8}, {8}} => {1, 1}
                      {{4}, {8}, {8}, {8}, {8}} => {1}
                      {{5}, {5}, {6}, {6}, {8}} => {1, 1}
                      {{5}, {5}, {6}, {7}, {7}} => {1}
                      {{5}, {5}, {7}, {7}, {8}} => {1}
                      {{5}, {6}, {6}, {7}, {8}} => {1}
                      {{5}, {6}, {7}, {8}, {8}} => {1, 1}
                      {{5}, {7}, {7}, {7}, {8}} => {1}
                      {{6}, {6}, {7}, {7}, {8}} => {1}
                      {{7}, {7}, {8}, {8}, {8}} => {1}




restart;
load("gorensteinTest.m2")
n = 5; -- n is the number of generators.
degBound = 8; -- degBound is the bound on the degrees of the generators.
p = 5; -- p is the characteristic of the field.
m = 100; -- m is the number of examples to generate.
Examples = new MutableHashTable;
scan(m, i -> (
     d1 = randomPureGorenstein(n,degBound,ZZ/p[x,y,z]);
     degList = apply(flatten entries d1, i -> degree i);
     beList = beMatrix d1;
     if Examples#?degList == false then Examples#degList = {};
     if class beList === List then Examples#degList = append(Examples#degList,#beList) else Examples#degList = append(Examples#degList,1);
))
peek Examples
Examples = new HashTable from Examples
M = matrix mutableMatrix(QQ,0,6)
scanPairs(Examples, i -> M = M||(matrix{apply(flatten i#0, j -> sub(j,QQ))}|(matrix{{sub((toList set flatten i#1)#0,QQ)}})))
M
degData = transpose M -- degData gives the degree lists and corresponding vector space dimension of S(d_1(g)) as column vectors to plug into `points'
degData = sub(degData,ZZ)
d1 = symbol d1
S = ZZ[d1,d2,d3,d4,d5,DS]
loadPackage "Points"
eqns = (points(degData,S))#2
#eqns
scan(eqns, i -> (print i; print newline;))

degData17 = sub(degData,ZZ/17)
S17 = ZZ/17[d1,d2,d3,d4,d5,DS]
eqns = (points(degData,S17))#2
#eqns
scan(eqns, i -> (print i; print newline;))
