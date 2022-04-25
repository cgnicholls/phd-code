AttachSpec("../spec");

Krt5<z> := QuadraticField(5);
K<u> := FunctionField(Krt5);
P<k1,k2,k3,k4> := PolynomialRing(K, 4);

Q<x> := PolynomialRing(K);

// We put r = 1 in the equations for G, H. This is possible, since r is an
// arithmetic parameter.
G := 1/2 * (-5*u+1/u)*x^2 + 1/2*(5*u-1/u)*x + 1/4*((z-5)*u + (z+5)/5*1/u);
H := 1/2 * (-5*u-1/u)*x^2 + 1/2*(5*u+1/u)*x + 1/4*((z-5)*u - (z+5)/5*1/u);
assert (G^2 + x^5) eq (H^2 + (x-1)^5);
C := G^2 + x^5;

f0 := Coefficient(C, 0);
f1 := Coefficient(C, 1);
f2 := Coefficient(C, 2);
f3 := Coefficient(C, 3);
f4 := Coefficient(C, 4);
f5 := Coefficient(C, 5);
f6 := Coefficient(C, 6);

kumR := k2^2-4*k1*k3;
kumS := -4*k1^3*f0-2*k1^2*k2*f1-4*k1^2*k3*f2-2*k1*k2*k3*f3
-4*k1*k3^2*f4-2*k2*
k3^2*f5-4*k3^3*f6;
kumT := -4*k1^4*f0*f2+k1^4*f1^2-4*k1^3*k2*f0*f3
-2*k1^3*k3*f1*f3-4*k1^2*k2^2
*f0*f4+4*k1^2*k2*k3*f0*f5-4*k1^2*k2*k3*f1*f4-4*k1^2*k3^2*f0*f6+2*k1^2*k3^
2*f1*f5-4*k1^2*k3^2*f2*f4+k1^2*k3^2*f3^2-4*k1*k2^3*f0*f5+8*k1*k2^2*k3*f0
*f6-4*k1*k2^2*k3*f1*f5+4*k1*k2*k3^2*f1*f6-4*k1*k2*k3^2*f2*f5-2*k1*k3^3*f3*
f5-4*k2^4*f0*f6-4*k2^3*k3*f1*f6-4*k2^2*k3^2*f2*f6-4*k2*k3^3*f3*f6-4*k3^4*
f4*f6+k3^4*f5^2;

kummeqn := kumR*k4^2+kumS*k4+kumT;

// First load in the lli that we already computed. These are the functions
// invariant under both T1 and T2.
load "lli.m";
load "helperfunctions.m";

specialise := function(poly, _u)
    return hom<P->P | hom<K->K | _u>, k1, k2, k3, k4>(poly);
end function;

Pl<l1,l2,l3,l4> := PolynomialRing(K, 4);

specialiseL := function(poly, _u)
    return hom<Pl->Pl | hom<K->K | _u>, l1, l2, l3, l4>(poly);
end function;

computeQuarticForU := function(specu, _lli)
    print "Computing quartic for u = ", specu;
    lispec := [specialise(poly, specu) : poly in _lli];
    print "Computing quartics in specialised lli";
    time quarticsli := degreencombinations(lispec, 4);
    quarticsli := [lispec[4]^2 * (lispec[2]^2 - 4*lispec[1]*lispec[3])];
    quarticsli := quarticsli cat [lispec[4] * cubic : cubic in
    degreencombinations(lispec[1..3], 3)];
    quarticsli := quarticsli cat degreencombinations(lispec[1..3], 4);

    variables := [l4^2 * (l2^2 - 4*l1*l3)];
    variables := variables cat [l4 * cubic : cubic in
    degreencombinations([l1,l2,l3], 3)];
    variables := variables cat degreencombinations([l1,l2,l3], 4);

    print "Reducing quartics";
    time quarticsreduced := reduceall(quarticsli, specialise(kummeqn, specu));
    print "Computing nullspace";
    time nullspace, V, monomials := linearRelations(quarticsreduced);
    assert Dimension(nullspace) eq 1;
    v := Basis(nullspace)[1];
    lleqn := (Matrix(Pl, v) * Transpose(Matrix([variables])))[1][1];
    return lleqn;
end function;

// Either load in the quartics, or compute them again.
load "specificquartics.m";
//print "Computing specific quartics";
//specificquartics := [];
//us := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
//
//for _u in us do
//    print "_u", _u;
//    time specificquartics := Append(eqns, computeQuarticForU(_u, lli));
//end for;

// Suppose a general equation of the form u^2 * l4^2 * (l2^2 - 4*l1*l3) + l4 *
// Phi(l1, l2, l3) + Psi(l1, l2, l3), where Phi is cubic, Psi is quartic, and
// all coefficients of monomials in l1, l2, l3, l4 are regular functions in u.
// That is, there are no denominators in u. We estimate that the degree of the
// functions in u is at most 6, and then use the quartics we have computed for
// specific values of u to interpolate the coefficients in general.

variables := [l4^2 * (l2^2 - 4*l1*l3)];
variables := variables cat [l4 * cubic : cubic in
degreencombinations([l1,l2,l3], 3)];
variables := variables cat degreencombinations([l1,l2,l3], 4);

print "We now try to find degree 8 polynomials in u as coefficients in a general
quartic equation for the li. We take each quartic equation, multiply it by u^4,
and then solve for degree 8 polynomials in u.";
maxdeg := 8;
M := Transpose(Matrix(Krt5, [[uu^i : i in [0..maxdeg]] : uu in us]));
c := Matrix(Krt5, [[MonomialCoefficient(specificquartics[i], var) * us[i]^4 : i in
[1..#specificquartics]] : var in variables[2..#variables]]);
time X := Solution(M, c);

print "The corresponding global quartic is";

coeffs := ChangeRing(X, K) * Transpose(Matrix(K, [[u^i : i in [0..8]]]));
coeffs := [coeffs[i][1] : i in [1..Nrows(coeffs)]];
coeffs := [u^4] cat coeffs;

quarticeqn := (Matrix(Pl, [coeffs]) * Transpose(Matrix(Pl, [variables])))[1][1];
print quarticeqn;

print "Now checking if the equation is correct globally -- it takes about 6
minutes to compute the quartic equation in lli, and then about 20 seconds to
reduce it modulo the original Kummer equation.";
//time quarticeqnsubs := hom<Pl->P | lli[1], lli[2], lli[3], lli[4]>(quarticeqn);
//time reduce(quarticeqnsubs, kummeqn);

print "Uncomment the above to do the check again, but we get 0!!!";

print "Now need to replace l4 by l4 + a1*l1 + a2*l2 + a3*l3 for some a1, a2, a3
so that we kill the l1*l2^2*l4, l2^3*l4 and l2^2*l3*l4 monomials";

Pcoeffs<a1,a2,a3> := PolynomialRing(K, 3);
PL<L1,L2,L3,L4> := PolynomialRing(Pcoeffs, 4);
hextra := hom<Pl->PL | L1,L2,L3,L4+a1*L1+a2*L2+a3*L3>;
eqn1 := MonomialCoefficient(hextra(quarticeqn), L1*L2^2*L4);
eqn2 := MonomialCoefficient(hextra(quarticeqn), L4*L2^3);
eqn3 := MonomialCoefficient(hextra(quarticeqn), L4*L2^2*L3);

// Construct the matrix with these equations, and solve for a1, a2, a3.
Mai := Matrix([[MonomialCoefficient(Pcoeffs!theeqn, ai) : ai in [a1,a2,a3]] :
             theeqn in [eqn1, eqn2, eqn3]]);
vai := -Matrix([[MonomialCoefficient(Pcoeffs!theeqn, 1)] : theeqn in [eqn1,
             eqn2, eqn3]]);
aai := Mai^-1 * vai;
ll4 := lli[4] - aai[1,1] * lli[1] - aai[2,1] * lli[2] - aai[3,1] * lli[3];

print "Now ll1,ll2,ll3,ll4 satisfy the quartic equation:";
quarticeqntilde := hom<Pl->Pl | l1, l2, l3, l4 + aai[1,1]*l1 + aai[2,1]*l2 +
aai[3,1]*l3>(quarticeqn);
// Normalise the quartic equation so that the l4^2 l2^2 term has coefficient 1.
assert Degree(quarticeqn, l4) eq 2;
assert MonomialCoefficient(quarticeqn, l4^2 * l2^2) ne 0;
quarticeqntilde := quarticeqntilde / MonomialCoefficient(quarticeqntilde, l4^2 * l2^2);
assert MonomialCoefficient(quarticeqntilde, l1*l2^2*l4) eq 0;
assert MonomialCoefficient(quarticeqntilde, l2^3*l4) eq 0;
assert MonomialCoefficient(quarticeqntilde, l2^2*l3*l4) eq 0;
assert MonomialCoefficient(quarticeqntilde, l4^2 * l1*l3) eq -4;
print quarticeqntilde;
print "And the three monomials have vanished";

print "Thus we can read off the curve:";

readCurveFromQuartic := function(quarticeqn)
    assert Degree(quarticeqn, l4) eq 2;
    assert MonomialCoefficient(quarticeqn, l4^2 * l2^2) ne 0;
    quarticeqn := quarticeqn / MonomialCoefficient(quarticeqn, l4^2 * l2^2);
    assert MonomialCoefficient(quarticeqn, l4^2 * l1*l3) eq -4;
    llfi := [MonomialCoefficient(quarticeqn, mon * l4) : mon in [l1^3, l1^2*l2,
    l1^2*l3, l1*l2*l3, l1*l3^2, l2*l3^2, l3^3]];
    c := [-4, -2, -4, -2, -4, -2, -4];
    llfi := [llfi[i] / c[i] : i in [1..#llfi]];

    curveeqn := 0;
    for i in [1..7] do
        curveeqn := curveeqn + llfi[i] * x^(i-1);
    end for;
    return curveeqn;
end function;
Ctilde := readCurveFromQuartic(quarticeqntilde);
print "The isogenous curve is", Ctilde;

// Take a curve of the form y^2 = f(x) and output g where v^2 = u^6 f(1/u) =
// g(u).
reverseCurve := function(curveeqn)
    Qu<u> := FieldOfFractions(Q);
    reversedcurve := hom<Q->Qu | 1/u>(curveeqn) * u^6;
    reversedcurve := Q!reversedcurve;
    return reversedcurve;
end function;

print "Now put the curve in degree 5 form, with a rational map, and remove squares from the leading coefficient";
Ctildedeg5 := reverseCurve(hom<Q->Q | x + 1/2>(Ctilde));
Ctildedeg5 := Ctildedeg5 * 16/25;
print "This has degree 5 model", Ctildedeg5;

print "We store the coordinates li in lltilde";
lltilde := lli[1..3] cat [ll4];

print "Check that the lltilde satisfy the quartic. First substitute the lltilde
into the equation.";
//time quarticeqntildesubs := hom<Pl->P | lltilde>(quarticeqntilde);
//print "Now reduce the equation. Should be 0.";
//time reduce(quarticeqntildesubs, kummeqn);
print "Uncomment the above to actually check!";

ourunits := function(n)
    return ((1-z)/2)^n / z;
end function;

specialiseQ := function(poly, _u)
    return hom<Q->Q | hom<K->K | _u>, x>(poly);
end function;

CVictoreqn := 256-640*x+560*x^2-200*x^3+25*x^4+x^5;
CVictor := HyperellipticCurve(CVictoreqn);
CVictor := ChangeRing(CVictor, Rationals());
CtildeVictoreqn := x^5 - 125*x^4 + 5000*x^3 - 175000*x^2 + 1250000*x - 81250000;
CtildeVictor := HyperellipticCurve(CtildeVictoreqn);
CtildeVictor := ChangeRing(CtildeVictor, Rationals());

print "Note that Victor's curve is";
print CVictor;
print "And Victor's Ctilde is";
print CtildeVictor;

uvictor := ((1-z)/2)^-2 / z;
print "We get an arithmetically isomorphic curve for u = uvictor, where uvictor
= ", uvictor;
IsIsomorphic(ChangeRing(HyperellipticCurve(specialiseQ(C, uvictor)),
Rationals()), CVictor);

print "We try to find a twist of C that has a simply expressed rational point. Note that if we put x = 1/2, then we get y^2 = ";
hom<Q->K | 1/2>(C);

print "We want to twist C so that this value is square in Q(rt5), but also so
that it is square in Q for all of our special values of u";
print "To do this, we twist by the conjugate of C(1/2). Note that for our
special values of u, we have u ubar = 1/5 or u ubar = -1/5, so in any case u^2
ubar^2 = 1/25. That is, ubar^2 = 1/(25 u^2).";

twistfactor := 1/64 * (45 + 20*z) / (25*u^2) + 1/320 * (25*u^2) * (9-4*z);

print "Twist C by", twistfactor;

Ctwist := C * twistfactor;

_, alpha := IsSquare(hom<Q->K | 1/2>(Ctwist));
assert alpha^2 eq hom<Q->K | 1/2>(Ctwist);

print "Now note that the point (1/2, alpha) lies on Ctwist, where alpha = ", alpha;

print "Thus Ctwist(1/2) is always a square in Q(rt5), equal to alpha. Moreover, alpha is rational when u is in the special set.";

print "Now trace through (1/2, alpha) + infty under the isogeny.";

computekummeqn := function(_fs)
    while #_fs lt 7 do
        _fs := Append(_fs, 0);
    end while;
    _f0 := _fs[1];
    _f1 := _fs[2];
    _f2 := _fs[3];
    _f3 := _fs[4];
    _f4 := _fs[5];
    _f5 := _fs[6];
    _f6 := _fs[7];

    kumR := k2^2-4*k1*k3;
    kumS := -4*k1^3*_f0-2*k1^2*k2*_f1-4*k1^2*k3*_f2-2*k1*k2*k3*_f3
    -4*k1*k3^2*_f4-2*k2*
    k3^2*_f5-4*k3^3*_f6;
    kumT := -4*k1^4*_f0*_f2+k1^4*_f1^2-4*k1^3*k2*_f0*_f3
    -2*k1^3*k3*_f1*_f3-4*k1^2*k2^2
    *_f0*_f4+4*k1^2*k2*k3*_f0*_f5-4*k1^2*k2*k3*_f1*_f4-4*k1^2*k3^2*_f0*_f6+2*k1^2*k3^
    2*_f1*_f5-4*k1^2*k3^2*_f2*_f4+k1^2*k3^2*_f3^2-4*k1*k2^3*_f0*_f5+8*k1*k2^2*k3*_f0
    *_f6-4*k1*k2^2*k3*_f1*_f5+4*k1*k2*k3^2*_f1*_f6-4*k1*k2*k3^2*_f2*_f5-2*k1*k3^3*_f3*
    _f5-4*k2^4*_f0*_f6-4*k2^3*k3*_f1*_f6-4*k2^2*k3^2*_f2*_f6-4*k2*k3^3*_f3*_f6-4*k3^4*
    _f4*_f6+k3^4*_f5^2;

    return kumR*k4^2+kumS*k4+kumT;
end function;

twistkummcoords := function(_ks, twist)
    return _ks[1..3] cat [_ks[4] * twist];
end function;

// Since the point is of the form (x1,y1) + infty - 2*infty, the Kummer
// coordinates take the form: [0, 1, x1, 2*f6*x1^3+f5*x1^2-2*v2*y1]. Here, f6 =
// 0 and v2 = 0 (since the v-coordinate of infty on a degree 5 curve is zero).
// To see this for the Kummer coordinates just divide all of them through by x1
// + x2, and then substitute x2=1/u2, y2=v2/u2^3, and then set u2 = 0.
kummcoords := [0, 1, 1/2, Coefficient(C, 5)*(1/2)^2];
assert hom<P->K | kummcoords>(kummeqn) eq 0;
print "We take (1/2, alpha) + infty on Jacobian of Ctwist and map it to (1/2, alpha / sqrt(twistfactor)) on Jacobian of C";
print "Then (1/2, alpha / sqrt(twistfactor)) + infty has coordinates", kummcoords, "on the Kummer of C";

print "This point maps to the following point on the Kummer of Ctilde:";

kummcoordstilde := [hom<Pl->K | kummcoords>(poly) : poly in lltilde];
print kummcoordstilde;

// Computes f(x1) + f(x2)
fx1plusfx2 := function(_ks, _fs)
    Qs<x1, x2> := PolynomialRing(K, 2);
    while #_fs lt 7 do
        _fs := Append(_fs, 0);
    end while;
    fx1 := _fs[1] + _fs[2]*x1 + _fs[3]*x1^2 + _fs[4]*x1^3 + _fs[5]*x1^4 +
    _fs[6]*x1^5 + _fs[7]*x1^6;
    fx2 := _fs[1] + _fs[2]*x2 + _fs[3]*x2^2 + _fs[4]*x2^3 + _fs[5]*x2^4 +
    _fs[6]*x2^5 + _fs[7]*x2^6;

    Qssym<s1, s2> := PolynomialRing(K, 2);
    _, sympoly := IsSymmetric(fx1+fx2, Qssym);
    
    return hom<Qssym->K | _ks[2]/_ks[1], _ks[3]/_ks[1]>(sympoly);
end function;

compute_F0_x1_x2 := function(x1, y1, x2, y2, f_eqn)
    _fs := [Coefficient(f_eqn, i) : i in [0..6]];
    return 2 * _fs[1] + _fs[2] * (x1 + x2) + 2 * _fs[3] * (x1*x2) + _fs[4] * \
    (x1*x2) * (x1 + x2) + 2 * _fs[5] * (x1*x2)^2 + _fs[6] * (x1*x2)^2 * (x1 + \
    x2) + 2 * _fs[7] * (x1*x2)^3;
end function;

// Computes k1, k2, k3, k4 for the point (x1,y1) + (x2,y2) - D_infty, where
// D_infty is either 2 * infty (if odd degree curve) or infty+ + infty- (if even
// degree curve). Will fail if x1 = x2.
compute_kumm_coords := function(x1, y1, x2, y2, f_eqn)
    return [1, x1 + x2, x1 * x2, (compute_F0_x1_x2(x1,y1,x2,y2, f_eqn) -
    2*y1*y2) / (x1-x2)^2];
end function;

F0x1x2 := function(_ks, _fs)
    while #_fs lt 7 do
        _fs := Append(_fs, 0);
    end while;
    return 2 * _fs[1] * _ks[1]^3 + 
    _fs[2] * _ks[2] * _ks[1]^2 + 
    2 * _fs[3] * _ks[3] * _ks[1]^2 + 
    _fs[4] * _ks[1] * _ks[2] * _ks[3] + 
    2 * _fs[5] * _ks[3]^2 * _ks[1] +
    _fs[6] * _ks[2] * _ks[3]^2 + 
    2 * _fs[7] * _ks[3]^3;
//    return 2 * _fs[1] + _fs[2] * x1plusx2 + 2 * _fs[3] * x1timesx2 + _fs[4] *
//    x1plusx2 * x1timesx2 + 2 * _fs[5] * x1timesx2^2 + _fs[6] * x1plusx2 *
//    x1timesx2^2 + 2 * _fs[7] * x1timesx2^3;
end function;

discOfY := function(_ks, _fs)
    return fx1plusfx2(_ks, _fs) - F0x1x2(_ks, _fs) + _ks[4] * (_ks[2]^2 -
            4*_ks[3]*_ks[1]);
end function;

compute_affine_a9_squared := function(_ks, _fs)
    // Computes a9^2 / a14^2, assuming a14 != 0. This is equivalent to _ks being
    // the Kummer coordinates for P1 + P2 - 2*infty, where P1, P2 are both
    // affine.
    assert _ks[1] ne 0;
    while #_fs lt 7 do
        _fs := Append(_fs, 0);
    end while;
    _f0 := _fs[1];
    _f1 := _fs[2];
    _f2 := _fs[3];
    _f3 := _fs[4];
    _f4 := _fs[5];
    _f5 := _fs[6];
    _f6 := _fs[7];
    _a15 := (_ks[2]^2 - 4 * _ks[3] * _ks[1]) / _ks[1]^2;
    _a14 := 1;
    _a13 := _ks[2] / _ks[1];
    _a12 := _ks[3] / _ks[1];
    _a10 := _ks[3]^2 / _ks[1]^2;
    _a5 := _ks[4] / _ks[1];
    return _a5*_a14+_f2*_a14^2+_f3*_a14*_a13+_f4*_a13^2+3*_f5*_a13*_a12+_f5*_a13* _a15+_f6*_a14*_a10+6*_f6*_a12*_a15+8*_f6*_a12^2+_f6*_a15^2;
end function;

computea9squared := function(_ks, _fs)
    // This function only works if the first Kummer coordinate is nonzero, i.e.
    // a_14 != 0. This is equivalent to _ks being the Kummer coordinates for P1
    // + P2 - 2*infty, where P1, P2 are both affine.
    assert _ks[1] ne 0;
    while #_fs lt 7 do
        _fs := Append(_fs, 0);
    end while;
    _f0 := _fs[1];
    _f1 := _fs[2];
    _f2 := _fs[3];
    _f3 := _fs[4];
    _f4 := _fs[5];
    _f5 := _fs[6];
    _f6 := _fs[7];
    _a15 := _ks[2]^2 - 4 * _ks[3] * _ks[1];
    _a14 := _ks[1]^2;
    _a13 := _ks[2] * _ks[1];
    _a12 := _ks[3] * _ks[1];
    _a10 := _ks[3]^2;
    // NEED TO FIX THIS SO IT'S HOMOGENEOUS WRT THE FS -- do we?
    _a5 := _ks[4] * _ks[1];
    return _a5*_a14+_f2*_a14^2+_f3*_a14*_a13+_f4*_a13^2+3*_f5*_a13*_a12+_f5*_a13* _a15+_f6*_a14*_a10+6*_f6*_a12*_a15+8*_f6*_a12^2+_f6*_a15^2;
end function;

twoDescentRank := function(curve, uspec)
    gp :=
    TwoSelmerGroup(Jacobian(HyperellipticCurve(ChangeRing(specialiseQ(curve,
                            uspec), Krt5))));
    return gp;
end function;

twoDescentRankOverQ := function(curve, uspec)
    gp :=
    TwoSelmerGroup(Jacobian(HyperellipticCurve(ChangeRing(specialiseQ(curve,
                            uspec), Rationals()))));
    return gp;
end function;

checkTwoDescentRankOverQ := function(curve1, curve2, uspec)
    print "Setting class group bounds!";
    SetClassGroupBounds("GRH");
    gp1 := twoDescentRank(curve1, uspec);
    gp2 := twoDescentRank(curve2, uspec);
    tf := IsIsomorphic(gp1, gp2);
    return tf, gp1, gp2;
end function;

checkTwoDescentRank := function(curve1, curve2, uspec)
    print "Setting class group bounds!";
    SetClassGroupBounds("GRH");
    gp1 := twoDescentRank(curve1, uspec);
    gp2 := twoDescentRank(curve2, uspec);
    tf := IsIsomorphic(gp1, gp2);
    return tf, gp1, gp2;
end function;

kummeqntilde := computekummeqn(Coefficients(Ctilde));
print "Check that kummcoordstilde lie on kummeqntilde";
assert hom<P->K | kummcoordstilde>(kummeqntilde) eq 0;

print "The point corresponding to kummcoordstilde on J(Ctilde) is rational if
and only if a9^2 is square.";
print "We twisted by twistfactor on C to get the point (1/2, alpha) to be
rational, so now we want to twist by twistfactor on Ctilde also.";
print "Assert that a9squared is a square in K.";
assert IsSquare(computea9squared(twistkummcoords(kummcoordstilde, twistfactor), Coefficients(Ctilde*twistfactor)));

checkIsomorphicOverQ := function(curve1, curve2)
    return IsIsomorphic(HyperellipticCurve(ChangeRing(curve1, Rationals())), HyperellipticCurve(ChangeRing(curve2, Rationals())));
end function;

print "Now assert that in Victor's case we get C isomorphic to his C and C' isomorphic to his C'";
assert checkIsomorphicOverQ(specialiseQ(C, ourunits(-2)), CVictoreqn);
assert checkIsomorphicOverQ(specialiseQ(Ctilde, ourunits(-2)), CtildeVictoreqn);
assert checkIsomorphicOverQ(specialiseQ(Ctildedeg5, ourunits(-2)), CtildeVictoreqn);

print "Check writectildeinform.m to see that Ctildedeg5 can be written as lambda1 * G1^2 + (x-s1)^5 = lambda2 * G2^2 + (x-s2)^5";
G1 := x^2 + (1/25*(8*z + 20)*u^2 + 4/125*z)/(u^2 + 1/5*(z + 2));
G2 := x^2 + (1/25*(8*z + 20)*u^2 - 4/125*z)/(u^2 + 1/5*(-z - 2));
lambda1 := -((-10*z + 25)*u^4 + 2*z*u^2 + 1/5*(2*z + 5))/u^2;
lambda2 := -((-10*z + 25)*u^4 - 2*z*u^2 + 1/5*(2*z + 5))/u^2;
s1 := 2/5*z;
s2 := -2/5*z;

assert Ctildedeg5 eq lambda1 * G1^2 - (x-s1)^5;
assert Ctildedeg5 eq lambda2 * G2^2 - (x-s2)^5;
