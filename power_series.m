intrinsic JacobianPowerSeries() -> SeqEnum
    { Computes the power series for the Jacobian of y^2 = f(x), where f is
    a general degree 6 polynomial. }
    K<f0,f1,f2,f3,f4,f5,f6> := PolynomialRing(Rationals(), 7);
    P<x> := PolynomialRing(K);
    f := P!Polynomial(P, [f0,f1,f2,f3,f4,f5,f6]);
    return JacobianPowerSeries(f);
end intrinsic;


intrinsic JacobianPowerSeriesAllCoefficients() -> SeqEnum
    { Computes the power series for the Jacobian of y^2 = f(x). }
    Q<s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,f0,f1,f2,f3,f4,f5,f6>
        := PolynomialRing(Rationals(), 22);

    power_series := [
        s1,
        s2,
        -s10^2*f2*f5^2-s11^2*f0*f5^2+s1^2+8*f0*f6*s4*s11
-s10^2*f3^2*f6-f4*s3^2-f0*s5^2+4*s10^2*f1*f5*f6+4*s10^2*f2*f4*f6-s10*s3*
f3*f5+4*s10*s3*f2*f6+8*f1*f6*s10*s4+f1*f5*s10*s5+4*s11^2*f0*f4*f6-s10*s11*f1*
f5^2+4*s10*s11*f0*f5*f6+4*s10*s11*f1*f4*f6+4*f0*f5*s12*s4+2*s12*s10*f0*f5^2+6
*s12*s10*f1*f3*f6+8*f0*f3*f6*s12*s11+4*s14*s10*f0*f2*f6+2*s14*s10*f0*f3*f5+3*
s14*s10*f1^2*f6+4*f0*f1*f6*s14*s11+2*f0*f1*f5*s14*s12,
        s1*s2+3*s13*s10*f0*f5^2+s13*s10*f1*f3*f6+2*s10^2*f2
*f5*f6+f3*f6*s10*s3+4*f2*f6*s10*s4+s10*s5*f2*f5+5*s10*s5*f1*f6+4*f1*f6*s12*s3+
20*f0*f6*s12*s4+10*f0*f5*f6*s10*s12+2*s12^2*f1*f3*f5+28*s12^2*f0*f3*f6+4*s12
^2*f1*f2*f6+3*f1*f5*s12*s4+2*s12*s10*f1*f4*f6+2*s12*s10*f2*f3*f6+s12*s10*f1*f5
^2-4*f0*f5^2*s12*s11-4*f0*f6*f4*s12*s11+2*f0*f4*s13*s5+8*s10*s13*f0*f4*f6+8*
s13*s12*f0*f2*f6+3*s13*s12*f0*f3*f5-s13*s12*f1^2*f6+9*s14*s3*f0*f5+s14*s3*f1*
f4+f0*f3*s14*s5-2*f1*f6*f2*s14*s10-8*f0*f6*f3*s14*s10-2*f0*f5*f3*s14*s11-4*f0*
f6*f2*s14*s11+10*f1*f6*f0*s14*s12+2*s14*s12*f0*f2*f5+s14*s12*f1^2*f5+2*f1*f6*
s3*s15+4*f0*f6*s4*s15+2*f0*f5*s5*s15+2*f0*f5*f6*s10*s15+4*f0*f3*f6*s12*s15+2*f1
*f6*f0*s14*s15,
        -s14^2*f0*f3^2 - s14^2*f1^2*f4 + s2^2 - f6*s3^2 - f2*s5 ^2 +
8*s13*s4*f0*f6 + 4*f0*f5*s13*s5 + 4*s13*s10*f0*f5*f6 -
4*s13*s10*f1*f4*f6 + 4*f0*f4 *s14*s5 + 4*s10*s14*f0*f4*f6 -
s10*s14*f0*f5^2 + 4*s10*s14*f1*f3*f6 + 8*f1*f6*s12*s4 + 4
*f1*f5*f6*s12*s10 + 4*f1*f6*f4*s12*s11
 - 2*f1*f6*s13*s3 + 4*s14*s13*f0*f1*f6 + 4*s14* s13*f0*f2*f5 -
 s14*s13*f1^2*f5 + 4*s14^2*f0*f2*f4 + f1*f5*s14*s3 - s14*s5*f1*f3 +
 8*s14 *s11*f0*f3*f6 + 16*s14*s12*f0*f2*f6 + 2*s14*s12*f0*f3*f5 +
 4*s14*f0*f2*f6*s15 - s14*f1 ^2*f6*s15,
        -f1*s9*s3+s14*s8*f1^2+4*f1*s8*s4+2*f3*s3*s7+s3*s1-f3*s2*
s10+4*f0*s8*s5+2*f2*s8*s3-2*f0*f5*s10*s9+3*f1*f5*s10*s8+2*f1*f6*s11*s6+12
*f0*f5*s12*s7+12*f0*f6*s12*s6+4*s12*s8*f0*f4+2*s12*s8*f1*f3+2*s12*s7*f1*f4+2*
s12*s6*f1*f5+4*s14*s8*f0*f2+4*f0*f3*s14*s7+4*f0*f4*s14*s6+4*f0*f5*s7*s15+4*f0*
f6*s6*s15,
        2*f0*s9*s5+f1*s8*s5+s2*s3,
        2*f6*s6*s3+f5*s3*s7+s5*s1,
        -f3^2*s14*s7-2*s10*s7*f5^2+4*f6*s7*s3+s2*s5+4*f1*f6*s11*
s9+f3*s9*s4+3*f5*s3*s8+2*f4*s7*s5+4*f0*f5*s13*s9-2*f5*f6*s10*s6+4*s10*s7*
f4*f6+4*f3*f6*s10*s8+4*f2*f6*s10*s9+12*f0*f6*s12*s9-f3*f6*s12*s6+4*s12*s8*f2*f5
+4*s12*s9*f1*f5+4*s12*s7*f2*f6+2*s12*s7*f3*f5-s12*s8*f3*f4-f3*f5*s13*s6+2*f1*f5
*s14*s7-s14*s6*f3*f4-s14*s8*f2*f3+2*s14*s6*f1*f6+4*f0*f6*s9*s15-f3*f6*s6*s15, 
        s3^2,
        f1*s14*s3+f3*s10*s5+f5*s3*s10+2*s4*s3,
        s3*s5,
        f1*s14*s5+f3*s14*s3+f5*s10*s5+2*s5*s4,
        s5^2,
        -(-4*f0*f2*s14^2-4*f0*s14*s5-36*f0*f6*s12^2-4*f3*f5*
s12*s10-4*f1*f6*s13*s10-4*f2*f5*s13*s10-12*f5*f0*s13*s12-2*f1*f3*s14*s12-4*f3*
f0*s14*s13-4*f2*f4*s14*s10-4*f5*s10*s4-f5^2*s10^2-24*f0*f6*s12*s15-4*f2*f6*
s10*s15-4*f1*f6*s11*s15-4*f5*f0*s13*s15-4*f1*f4*s14*s11+f3^2*s14*s10-2*f3*s11*
s5-16*f1*f5*s12^2-2*f1*s13*s5-4*f2*s12*s5-4*f0*f6*s15^2-4*f4*f6*s10^2-4*f6*
s10*s3-4*f4*s10*s5-4*f3*f6*s10*s11-16*f2*f6*s10*s12-8*f1*f6*s11*s12+f1^2*s14^
2-16*f0*f4*s14*s12-4*f1*f5*s12*s15-4*f0*f4*s14*s15)
    ];
    
    return power_series;
end intrinsic;


intrinsic JacobianPowerSeriesUpToDegree(degree::RngIntElt) -> SeqEnum
    { Computes the power series for the Jacobian of y^2 = f(x) in terms of the
    local parameters s1, s2, accurate up to the given degree. That is, we expand
    each power series so that only terms in s1, s2 appear, and such that these
    are computed exactly for each term s1^i1 * s2^i2 with i1 + i2 <= degree. }
    
    Q<s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,f0,f1,f2,f3,f4,f5,f6>
        := PolynomialRing(Rationals(), 22);
    power_series := [Q!JacobianPowerSeriesUpToDegree(i, degree) : i in [1..15]];
    return power_series;
end intrinsic;


intrinsic JacobianPowerSeriesUpToDegreeSpecialised(f::RngUPolElt,
    degree::RngIntElt) -> SeqEnum
    { Computes the power series for the Jacobian of y^2 = f(x) in terms of the
    local parameters s1, s2, accurate up to the given degree. That is, we expand
    each power series so that only terms in s1, s2 appear, and such that these
    are computed exactly for each term s1^i1 * s2^i2 with i1 + i2 <= degree. }
    power_series := JacobianPowerSeriesUpToDegree(degree);
    Q<ss1, ss2, ss3, ss4, ss5, ss6, ss7, ss8, ss9, ss10, ss11, ss12, ss13, ss14,
        ss15, f0, f1, f2, f3, f4, f5, f6> := Universe(power_series);
    K := CoefficientRing(Parent(f));
    P<s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15> :=
        PolynomialRing(K, 15);
    f_coeffs := [Coefficient(f, i) : i in [0..6]];
    spec_hom := hom<Q->P | s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12,
    s13, s14, s15, f_coeffs[1], f_coeffs[2], f_coeffs[3], f_coeffs[4],
    f_coeffs[5], f_coeffs[6], f_coeffs[7]>;
    return [spec_hom(poly) : poly in power_series];
end intrinsic;
    


intrinsic JacobianPowerSeries(f::RngUPolElt) -> SeqEnum
    { Computes the power series for the Jacobian of y^2 = f(x). }
    K := CoefficientRing(Parent(f));
    f0 := Coefficient(f, 0);
    f1 := Coefficient(f, 1);
    f2 := Coefficient(f, 2);
    f3 := Coefficient(f, 3);
    f4 := Coefficient(f, 4);
    f5 := Coefficient(f, 5);
    f6 := Coefficient(f, 6);
    Q<s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15> := PolynomialRing(K,
        15);

    power_series := [
        s1,
        s2,
        -s10^2*f2*f5^2-s11^2*f0*f5^2+s1^2+8*f0*f6*s4*s11
-s10^2*f3^2*f6-f4*s3^2-f0*s5^2+4*s10^2*f1*f5*f6+4*s10^2*f2*f4*f6-s10*s3*
f3*f5+4*s10*s3*f2*f6+8*f1*f6*s10*s4+f1*f5*s10*s5+4*s11^2*f0*f4*f6-s10*s11*f1*
f5^2+4*s10*s11*f0*f5*f6+4*s10*s11*f1*f4*f6+4*f0*f5*s12*s4+2*s12*s10*f0*f5^2+6
*s12*s10*f1*f3*f6+8*f0*f3*f6*s12*s11+4*s14*s10*f0*f2*f6+2*s14*s10*f0*f3*f5+3*
s14*s10*f1^2*f6+4*f0*f1*f6*s14*s11+2*f0*f1*f5*s14*s12,
        s1*s2+3*s13*s10*f0*f5^2+s13*s10*f1*f3*f6+2*s10^2*f2
*f5*f6+f3*f6*s10*s3+4*f2*f6*s10*s4+s10*s5*f2*f5+5*s10*s5*f1*f6+4*f1*f6*s12*s3+
20*f0*f6*s12*s4+10*f0*f5*f6*s10*s12+2*s12^2*f1*f3*f5+28*s12^2*f0*f3*f6+4*s12
^2*f1*f2*f6+3*f1*f5*s12*s4+2*s12*s10*f1*f4*f6+2*s12*s10*f2*f3*f6+s12*s10*f1*f5
^2-4*f0*f5^2*s12*s11-4*f0*f6*f4*s12*s11+2*f0*f4*s13*s5+8*s10*s13*f0*f4*f6+8*
s13*s12*f0*f2*f6+3*s13*s12*f0*f3*f5-s13*s12*f1^2*f6+9*s14*s3*f0*f5+s14*s3*f1*
f4+f0*f3*s14*s5-2*f1*f6*f2*s14*s10-8*f0*f6*f3*s14*s10-2*f0*f5*f3*s14*s11-4*f0*
f6*f2*s14*s11+10*f1*f6*f0*s14*s12+2*s14*s12*f0*f2*f5+s14*s12*f1^2*f5+2*f1*f6*
s3*s15+4*f0*f6*s4*s15+2*f0*f5*s5*s15+2*f0*f5*f6*s10*s15+4*f0*f3*f6*s12*s15+2*f1
*f6*f0*s14*s15,
        -s14^2*f0*f3^2 - s14^2*f1^2*f4 + s2^2 - f6*s3^2 - f2*s5 ^2 +
8*s13*s4*f0*f6 + 4*f0*f5*s13*s5 + 4*s13*s10*f0*f5*f6 -
4*s13*s10*f1*f4*f6 + 4*f0*f4 *s14*s5 + 4*s10*s14*f0*f4*f6 -
s10*s14*f0*f5^2 + 4*s10*s14*f1*f3*f6 + 8*f1*f6*s12*s4 + 4
*f1*f5*f6*s12*s10 + 4*f1*f6*f4*s12*s11
 - 2*f1*f6*s13*s3 + 4*s14*s13*f0*f1*f6 + 4*s14* s13*f0*f2*f5 -
 s14*s13*f1^2*f5 + 4*s14^2*f0*f2*f4 + f1*f5*s14*s3 - s14*s5*f1*f3 +
 8*s14 *s11*f0*f3*f6 + 16*s14*s12*f0*f2*f6 + 2*s14*s12*f0*f3*f5 +
 4*s14*f0*f2*f6*s15 - s14*f1 ^2*f6*s15,
        -f1*s9*s3+s14*s8*f1^2+4*f1*s8*s4+2*f3*s3*s7+s3*s1-f3*s2*
s10+4*f0*s8*s5+2*f2*s8*s3-2*f0*f5*s10*s9+3*f1*f5*s10*s8+2*f1*f6*s11*s6+12
*f0*f5*s12*s7+12*f0*f6*s12*s6+4*s12*s8*f0*f4+2*s12*s8*f1*f3+2*s12*s7*f1*f4+2*
s12*s6*f1*f5+4*s14*s8*f0*f2+4*f0*f3*s14*s7+4*f0*f4*s14*s6+4*f0*f5*s7*s15+4*f0*
f6*s6*s15,
        2*f0*s9*s5+f1*s8*s5+s2*s3,
        2*f6*s6*s3+f5*s3*s7+s5*s1,
        -f3^2*s14*s7-2*s10*s7*f5^2+4*f6*s7*s3+s2*s5+4*f1*f6*s11*
s9+f3*s9*s4+3*f5*s3*s8+2*f4*s7*s5+4*f0*f5*s13*s9-2*f5*f6*s10*s6+4*s10*s7*
f4*f6+4*f3*f6*s10*s8+4*f2*f6*s10*s9+12*f0*f6*s12*s9-f3*f6*s12*s6+4*s12*s8*f2*f5
+4*s12*s9*f1*f5+4*s12*s7*f2*f6+2*s12*s7*f3*f5-s12*s8*f3*f4-f3*f5*s13*s6+2*f1*f5
*s14*s7-s14*s6*f3*f4-s14*s8*f2*f3+2*s14*s6*f1*f6+4*f0*f6*s9*s15-f3*f6*s6*s15, 
        s3^2,
        f1*s14*s3+f3*s10*s5+f5*s3*s10+2*s4*s3,
        s3*s5,
        f1*s14*s5+f3*s14*s3+f5*s10*s5+2*s5*s4,
        s5^2,
        -(-4*f0*f2*s14^2-4*f0*s14*s5-36*f0*f6*s12^2-4*f3*f5*
s12*s10-4*f1*f6*s13*s10-4*f2*f5*s13*s10-12*f5*f0*s13*s12-2*f1*f3*s14*s12-4*f3*
f0*s14*s13-4*f2*f4*s14*s10-4*f5*s10*s4-f5^2*s10^2-24*f0*f6*s12*s15-4*f2*f6*
s10*s15-4*f1*f6*s11*s15-4*f5*f0*s13*s15-4*f1*f4*s14*s11+f3^2*s14*s10-2*f3*s11*
s5-16*f1*f5*s12^2-2*f1*s13*s5-4*f2*s12*s5-4*f0*f6*s15^2-4*f4*f6*s10^2-4*f6*
s10*s3-4*f4*s10*s5-4*f3*f6*s10*s11-16*f2*f6*s10*s12-8*f1*f6*s11*s12+f1^2*s14^
2-16*f0*f4*s14*s12-4*f1*f5*s12*s15-4*f0*f4*s14*s15)
    ];
    return power_series;
end intrinsic;

containsHigherssi := function(poly)
    Q<s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15> :=
        Universe(poly);
    assert Rank(Q) eq 15;
    if Degree(poly, s3) gt 0 then
        return true;
    end if;
    if Degree(poly, s4) gt 0 then
        return true;
    end if;
    if Degree(poly, s5) gt 0 then
        return true;
    end if;
    if Degree(poly, s6) gt 0 then
        return true;
    end if;
    if Degree(poly, s7) gt 0 then
        return true;
    end if;
    if Degree(poly, s8) gt 0 then
        return true;
    end if;
    if Degree(poly, s9) gt 0 then
        return true;
    end if;
    if Degree(poly, s10) gt 0 then
        return true;
    end if;
    if Degree(poly, s11) gt 0 then
        return true;
    end if;
    if Degree(poly, s12) gt 0 then
        return true;
    end if;
    if Degree(poly, s13) gt 0 then
        return true;
    end if;
    if Degree(poly, s14) gt 0 then
        return true;
    end if;
    if Degree(poly, s15) gt 0 then
        return true;
    end if;
    return false;
end function;


weight_of_monomial_fi := function(mon)
    Q<s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,f0,f1,f2,f3,f4,f5,f6>
        := Parent(mon);
    weight_hom := hom<Q->Rationals() | 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2>;
    return ComputeSum([weight_hom(factor[1]) * factor[2] : factor in
        Factorisation(mon)]);
end function;


terms_of_max_weight_fi := function(poly, max_weight)
    monomials := [mon : mon in Monomials(poly) | 
        weight_of_monomial_fi(mon) le max_weight];
    monomial_coeffs := [MonomialCoefficient(poly, mon) : mon in monomials];
    return ComputeSum([monomial_coeffs[i] * monomials[i] : i in
        [1..#monomials]]);
end function;


weight_of_monomial := function(mon)
    Q<s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,f0,f1,f2,f3,f4,f5,f6>
        := Parent(mon);
    weight_hom := hom<Q->Rationals() | -1, -1, -2, -2, -2, -3, -3, -3, -3, -4,
        -4, -4, -4, -4, -4, 2, 2, 2, 2, 2, 2, 2>;
    return ComputeSum([weight_hom(factor[1]) * factor[2] : factor in
        Factorisation(mon)]);
end function;


terms_of_max_weight := function(poly, max_weight)
    monomials := [mon : mon in Monomials(poly) | 
        weight_of_monomial(mon) le max_weight];
    monomial_coeffs := [MonomialCoefficient(poly, mon) : mon in monomials];
    return ComputeSum([monomial_coeffs[i] * monomials[i] : i in
        [1..#monomials]]);
end function;


//weightOfMonomial := function(mon)
//    factors := Factorisation(mon);
//    thehom := hom<Qallss->Integers() |
//    -1,-1,-2,-2,-2,-3,-3,-3,-3,-4,-4,-4,-4,-4,-4,2,2,2,2,2,2,2>;
//    weights := [thehom(factor[1])*factor[2] : factor in factors];
//    totalweight := 0;
//    for weight in weights do
//        totalweight := totalweight + weight;
//    end for;
//    return totalweight;
//end function;
//
//computeWeights := function(poly)
//    monomials := Monomials(poly);
//    weights := [weightOfMonomial(mon) : mon in monomials];
//    return weights, monomials;
//end function;
//
//weightOfMonomialFi := function(mon)
//    K<f0,f1,f2,f3,f4,f5,f6> := Parent(mon);
//    terms := Terms(mon);
//    weight_hom := hom<K->K | 2, 2, 2, 2, 2, 2, 2>;
//    weights := [ComputeSum([weight_hom(factor[1])*factor[2] : factor in
//    Factorisation(term)]) : term in terms];
//    return weights[1];
//end function;
//
//computeWeightsFi := function(poly)
//    monomials := Monomials(poly);
//    weights := [weightOfMonomialFi(MonomialCoefficient(poly, mon)) : mon in
//        monomials];
//    return weights, monomials;
//end function;
//
//removeEndTerms := function(poly, deg)
//    terms := Terms(poly);
//    weights := computeWeights(poly);
//    assert Max(weights) eq Min(weights);
//    wt := Max(weights);
//    lowerpoly := 0;
//    for term in terms do
//        if 2*weightOfMonomialFi(term) le (wt+deg) then
//            lowerpoly := lowerpoly + term;
//        end if;
//    end for;
//    return lowerpoly;
//end function;
//
//expandUpToDegree := function(poly, deg, power_series)
//    // If a monomial s1^i1 * s2^i2 occurs in a monomial of homogeneous weight w,
//    // then we have w = -i1 - i2 + 2 d_f, where d_f is the degree of the
//    // coefficients f_i. Thus if we want all terms with i1 + i2 <= deg, we can
//    // impose that d_f <= (w + deg) / 2.
//    lowerpoly := poly;
//    P := Universe(power_series);
//    K<f0,f1,f2,f3,f4,f5,f6> := CoefficientRing(P);
//    while containsHigherssi(lowerpoly) do
//        lowerpoly := removeEndTerms(lowerpoly, deg);
//        lowerpoly := hom<P->P | power_series[1], power_series[2],
//        power_series[3], power_series[4], power_series[5], power_series[6],
//        power_series[7], power_series[8], power_series[9], power_series[10],
//        power_series[11], power_series[12], power_series[13], power_series[14],
//        power_series[15],ff0,ff1,ff2,ff3,ff4,ff5,ff6>(lowerpoly);
//    end while;
//
//    return lowerpoly;
//end function;
//
//
//intrinsic ExpandPowerSeriesUpToDegree(poly::RngMPolElt, degree::RngIntElt) ->
//    RngMPolElt
//    { Computes the polynomial in the poser series for the Jacobian accurate up
//    to the given degree. That is, all terms of the form s1^i * s2^j with i + j
//    <= degree are expanded. We discard the rest of the terms. }
//    power_series := JacobianPowerSeries();
//    return expandUpToDegree(poly, deg);
//end intrinsic;


intrinsic ExpandPowerSeries(poly::RngMPolElt, power_series::SeqEnum) -> RngElt
    { Given an expression in the power series, substitute in the power series
    again. }
    Q<s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,f0,f1,f2,f3,f4,f5,f6>
        := Universe(power_series);
    return hom<Q->Q | power_series cat [f0,f1,f2,f3,f4,f5,f6]>(poly);
end intrinsic;


intrinsic JacobianPowerSeriesUpToDegree(i::RngIntElt, degree::RngIntElt) ->
    RngMPolElt
    { Returns the ith power series up to degree. }
    power_series := JacobianPowerSeriesAllCoefficients();
    Q<s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,f0,f1,f2,f3,f4,f5,f6>
        := Universe(power_series);

    weighti := [weight_of_monomial(mon) : mon in Monomials(power_series[i])][1];
    max_weight := (degree - weighti) / 2;
    
    si := power_series[i];
    while Max([Degree(si, sj) : sj in [s3, s4, s5, s6, s7, s8, s9, s10, s11,
        s12, s13, s14, s15]]) gt 0 do

        si := terms_of_max_weight_fi(si, max_weight);
        si := ExpandPowerSeries(si, power_series);
        si := terms_of_max_weight_fi(si, max_weight);
    end while;
    return si;
end intrinsic;
    

intrinsic ComputePowerSeriesForKummerFunction(kum_func::RngMPolElt,
    f::RngUPolElt, degree::RngIntElt) -> RngMPolElt
    { Substitutes the power series in to the function in the Kummer coordinates
    k1,k2,k3,k4, accurate up to the given degree. }

    power_series := JacobianPowerSeriesUpToDegreeSpecialised(f, degree);

    P := Universe(power_series);
    k1ps := power_series[14];
    k2ps := power_series[13];
    k3ps := power_series[12];
    k4ps := power_series[5];
    // Victor suggests the following optimisation instead, which gives lower
    // degree terms.
    //f1 := Coefficient(f, 1);
    //f3 := Coefficient(f, 3);
    //f5 := Coefficient(f, 5);
    //k1ps := power_series[5];
    //k2ps := P!f1*power_series[14] + f3*power_series[12] + 2*power_series[4] +
    //    f5*power_series[10];
    //k3ps := power_series[3];
    //k4ps := 1;
    
    Pk<k1,k2,k3,k4> := Parent(kum_func);
    assert Rank(Pk) eq 4;

    return hom<Pk->P | k1ps, k2ps, k3ps, k4ps>(kum_func);
end intrinsic;


intrinsic ComputePowerSeriesForKummerFunction(kum_func::RngMPolElt,
    power_series::SeqEnum) -> RngMPolElt
    { Substitutes the given power series in to the function in the Kummer
    coordinates k1,k2,k3,k4. }

    P := Universe(power_series);
    k1ps := power_series[14];
    k2ps := power_series[13];
    k3ps := power_series[12];
    k4ps := power_series[5];
    // Victor suggests the following optimisation instead, which gives lower
    // degree terms.
    //f1 := Coefficient(f, 1);
    //f3 := Coefficient(f, 3);
    //f5 := Coefficient(f, 5);
    //k1ps := power_series[5];
    //k2ps := P!f1*power_series[14] + f3*power_series[12] + 2*power_series[4] +
    //    f5*power_series[10];
    //k3ps := power_series[3];
    //k4ps := 1;
    
    Pk<k1,k2,k3,k4> := Parent(kum_func);
    assert Rank(Pk) eq 4;

    return hom<Pk->P | k1ps, k2ps, k3ps, k4ps>(kum_func);
end intrinsic;


intrinsic TermsOfMaxDegree(poly::RngMPolElt, max_degree::RngIntElt) ->
    RngMPolElt
    { Returns the sum of the terms in the polynomial whose degrees are at most
    max_degree. }
    return ComputeSum([term : term in Terms(poly) | Degree(term) le
        max_degree]);
end intrinsic;
