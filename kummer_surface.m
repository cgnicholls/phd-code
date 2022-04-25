
// Computes the equation of the Kummer surface for y^2 = f(x), where fs are the
// coefficients of f(x).
intrinsic ComputeKummerEquation(fs::SeqEnum, ks::SeqEnum) -> RngMPolElt
{ Computes the quartic Kummer equation corresponding to the curve y^2 = f(x). Here
f must be a degree 5 or 6 polynomial. }
    f0 := fs[1];
    f1 := fs[2];
    f2 := fs[3];
    f3 := fs[4];
    f4 := fs[5];
    f5 := fs[6];
    if #fs eq 6 then
        f6 := 0;
    else
        f6 := fs[7];
    end if;
    k1 := ks[1];
    k2 := ks[2];
    k3 := ks[3];
    k4 := ks[4];
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

    return kumR*k4^2+kumS*k4+kumT;
end intrinsic;


intrinsic ComputeKummerEquation(f::RngUPolElt) -> RngMPolElt
    { Returns the quartic Kummer equation corresponding to the curve y^2 = f(x).
    Here f must be a degree 5 or 6 polynomial. }
    K := CoefficientRing(f);
    P<k1,k2,k3,k4> := PolynomialRing(K, 4);
    return ComputeKummerEquation([Coefficient(f, i) : i in [0..6]], [k1,k2,k3,k4]);
end intrinsic;


intrinsic ComputeKummerEquation(Kum::SrfKum) -> RngMPolElt
    { Returns the quartic Kummer equation corresponding to the curve y^2 = f(x).
    Here f must be a degree 5 or 6 polynomial. }
    J := Jacobian(Kum);
    f, h := HyperellipticPolynomials(Curve(J));
    assert h eq 0;
    return ComputeKummerEquation(f);
end intrinsic;


intrinsic KummerEquationWithoutBadMonomials(kum_eqn::RngMPolElt) -> RngMPolElt, SeqEnum
    { Removes the monomials k4*k2^2*ki for i = 1, 2, 3 from the Kummer equation.
    Assumes that Kummer equation is a quadratic in k4. Also returns ai such that
    the change of variables was k4 = k4 + a1*k1 + a2*k2 + a3*k3. }
    Pk<k1,k2,k3,k4> := Parent(kum_eqn);
    assert Rank(Pk) eq 4;
    assert Degree(kum_eqn, k4) eq 2;
    kum_eqn := kum_eqn / MonomialCoefficient(kum_eqn, k4^2*k2^2);
    ai := [MonomialCoefficient(kum_eqn, k4*k2^2*ki) : ki in [k1,k2,k3]];

    kum_eqn_transformed := hom<Pk->Pk | k1,k2,k3,k4 - ai[1]*k1/2 - ai[2]*k2/2 -
        ai[3]*k3/2>(kum_eqn);
    coeffs := [MonomialCoefficient(kum_eqn_transformed, k4*k2^2*ki) : ki in
        [k1,k2,k3,k4]];
    assert coeffs eq [0,0,0,1];
    return kum_eqn_transformed, ai;
end intrinsic;


intrinsic RemoveBadMonomialsFromKummerEquation(kum_eqn::RngMPolElt) -> Mtrx, RngMPolElt
{ In a Kummer equation that is a quadratic in k4, we may still have the bad
monomials [k1*k2^2*k4, k2^3*k4, k2^2*k3*k4]. This function returns a1, a2, a3
such that kum_eqn evaluated at k1, k2, k3, k4 + a1*k1 + a2*k2 + a3*k3 removes
the bad monomials. It also returns that Kummer equation. }
    Pk := Parent(kum_eqn);
    k1 := Pk.1;
    k2 := Pk.2;
    k3 := Pk.3;
    k4 := Pk.4;
    
    bad_monomials := [k1*k2^2*k4, k2^3*k4, k2^2*k3*k4];

    // Want k4 = k4 + a1 * k1 + a2 * k2 + a3 * k3, so that we kill these
    // monomials.
    Pa<a1, a2, a3> := PolynomialRing(Pk, 3);
    kum_eqn_ai := hom<Pk->Pa | k1, k2, k3, k4+a1*k1+a2*k2+a3*k3>(kum_eqn);

    // First construct the matrix whose ij entry is the coefficient of ai in
    // bad_monomial_j.
    coeffs := [MonomialCoefficient(kum_eqn_ai, ai) : ai in [a1,a2,a3]];
    M := Matrix([[MonomialCoefficient(coeff, mon) : mon in bad_monomials] : coeff in coeffs]);
    // We also need to know the current coefficients in each bad monomial.
    vec := Matrix([[MonomialCoefficient(kum_eqn, mon) : mon in bad_monomials]]);
    // Now we want to solve for ai to cancel the coefficients of the bad
    // monomials.
    ai_soln := Solution(Transpose(M), -vec);
    ai := [ai_soln[1][i] : i in [1..3]];

    Ma := Matrix(Pk, [[1,0,0,0],[0,1,0,0],[0,0,1,0],[ai[1],ai[2],ai[3],1]]);
    ki_transformed := Ma * Matrix([[k1],[k2],[k3],[k4]]);
    ki_transformed := [ki_transformed[i][1] : i in [1..4]];

    kum_eqn_soln := hom<Pk->Pk | k1, k2, k3, k4+ai[1]*k1+ai[2]*k2+ai[3]*k3>(kum_eqn);
    kum_eqn_soln_test := hom<Pk->Pk | ki_transformed>(kum_eqn);
    assert kum_eqn_soln eq kum_eqn_soln_test;
    assert [MonomialCoefficient(kum_eqn_soln, mon) : mon in bad_monomials] eq [0,0,0];
    
    return Ma, kum_eqn_soln;
end intrinsic;


intrinsic NormaliseQuadraticsForKummer(quadratics::SeqEnum) -> Mtrx, SeqEnum
{ Given quadratics in ki, denoted q, return the linear transformation theta
such that the quadratics theta * q start with k1*k4, k2*k4, k3*k4, k4^2. }
    Pk := Universe(quadratics);
    k1 := Pk.1;
    k2 := Pk.2;
    k3 := Pk.3;
    k4 := Pk.4;
    M := Matrix([[MonomialCoefficient(qi, Pk.j*k4) : j in [1..4]] : qi in
    quadratics]);

    // We require that M is invertible. Later on we should relax this.
    vec := Transpose(Matrix([quadratics]));
    normalised_quadratics := ChangeRing(M^-1, Pk) * vec;
    normalised_quadratics := [normalised_quadratics[i][1] : i in [1..4]];
    return M, normalised_quadratics;
end intrinsic;


intrinsic ReadCurveFromKummer(kum_eqn::RngMPolElt) -> RngUPolElt
{ Compute a curve f(x) such that the quartic Kummer equation kum_eqn is the
Kummer of a twist of y^2 = f(x). }
    Pl := Parent(kum_eqn);
    l1 := Pl.1;
    l2 := Pl.2;
    l3 := Pl.3;
    l4 := Pl.4;
    K := BaseRing(Pl);
    P<x> := PolynomialRing(K);
    assert Degree(kum_eqn, l4) eq 2;
    assert MonomialCoefficient(kum_eqn, l4^2 * l2^2) ne 0;

    // Make sure we only have terms involved in the definition of Phi. Some of
    // the monomials need to be removed.
    bad_monomials := [l1*l2^2*l4, l2^3*l4, l2^2*l3*l4];
    assert #{mon : mon in bad_monomials | MonomialCoefficient(kum_eqn, mon) ne 0} eq 0;
    
    // Normalise the equation.
    kum_eqn := kum_eqn / MonomialCoefficient(kum_eqn, l4^2 * l2^2);
    assert MonomialCoefficient(kum_eqn, l4^2 * l1*l3) eq -4;

    // Read off the curve.
    llfi := [MonomialCoefficient(kum_eqn, mon * l4) : mon in [l1^3, l1^2*l2,
    l1^2*l3, l1*l2*l3, l1*l3^2, l2*l3^2, l3^3]];
    c := [-4, -2, -4, -2, -4, -2, -4];
    llfi := [llfi[i] / c[i] : i in [1..#llfi]];

    // Construct the curve from the coefficients.
    curve_eqn := P!Polynomial(P, llfi);
    return curve_eqn;
end intrinsic;


intrinsic ReadCurveFromKummer(Kum::Srfc) -> RngUPolElt
{ Compute a curve f(x) such that Kum is the Kummer of a twist of y^2 = f(x). }
    return ReadCurveFromKummer(DefiningEquation(Kum));
end intrinsic;


intrinsic ReadCurveFromKummer(Kum::SrfKum) -> RngUPolElt
    { Compute a curve f(x) such that Kum is the Kummer of a twist of y^2 = f(x).
    }
    return ReadCurveFromKummer(DefiningPolynomial(Kum));
end intrinsic;


intrinsic KummerSurfaceScheme(Kum::SrfKum) -> Srfc, Map
    { Takes a SrfKum and returns a surface isomorphic to the original Kummer
    surface together with a map from the SrfKum to the Srfc. }
    eqn := DefiningPolynomial(Kum);
    Pk := Parent(eqn);
    KumSch := Surface(ProjectiveSpace(Pk), eqn);
    themap := func<kum_pt | KumSch!Eltseq(kum_pt)>;
    return KumSch, themap;
end intrinsic;


intrinsic KummerSurface(f::RngUPolElt) -> SrfKum
    { Returns the Kummer surface of y^2 = f(x). }
    J := Jacobian(HyperellipticCurve(f));
    return KummerSurface(J);
end intrinsic;


intrinsic KummerSurface(Kum::Srfc) -> SrfKum
    { First read off the curve from Kum, say y^2 = f(x). Then return the Kummer
    surface of y^2 = f(x) as a SrfKum. This only works if KummerSurface(curve)
    has the same equation as Kum. }
    f := ReadCurveFromKummer(Kum);
    KumSrf := KummerSurface(f);
    expected := DefiningEquation(Kum);
    computed := DefiningPolynomial(KumSrf);
    assert Parent(computed)!expected eq computed;
    return KumSrf;
end intrinsic;


intrinsic KummerSurfaceScheme(f::RngUPolElt) -> SrfKum
    { Returns the Kummer surface of y^2 = f(x) as a scheme. }
    Kum, _ := KummerSurfaceScheme(KummerSurface(f));
    return Kum;
end intrinsic;




intrinsic ComputeMapBetweenKummersOfTwists(f1::RngUPolElt, f2::RngUPolElt) -> RngMPolElt, RngMPolElt, Mtrx
{ If f1 and f2 differ by a constant, so that y^2 = f1 and y^2 = f2 are
twists, then their Kummer surfaces are isomorphic. This returns the linear
on Kummers between Kum1 and Kum2 (as a matrix), as well as their two equations. }

    K1 := BaseRing(f1);
    K2 := BaseRing(f2);
    // We need both curves defined over the same field.
    assert K1 eq K2;
    Pk<k1,k2,k3,k4> := PolynomialRing(K1, 4);
    kum_eqn1 := ComputeKummerEquation([Coefficient(f1, i) : i in [0..6]],
    [k1,k2,k3,k4]);
    kum_eqn2 := ComputeKummerEquation([Coefficient(f2, i) : i in [0..6]],
    [k1,k2,k3,k4]);

    // We now compute the linear map theta such that theta * [k1,k2,k3,k4]^T =
    // [kd1,kd2,kd3,kd4], where ki satisfy kum_eqn1 and kdi satisfy kum_eqn2.
    assert f1 / LeadingCoefficient(f1) eq f2 / LeadingCoefficient(f2);
    twist := LeadingCoefficient(f2) / LeadingCoefficient(f1);
    theta := Matrix([[1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,twist]]);
    return kum_eqn1, kum_eqn2, theta;
end intrinsic;


intrinsic KummerSurfaceTwist(Kum::Srfc, d::RngElt) -> Srfc, Map
    { Let Kum be the Kummer surface of the hyperelliptic curve y^2 = f(x).
    Computes a Kummer surface scheme Kum2 isomorphic to the Kummer surface of
    the hyperelliptic curve y^2 = d * f(x) together with a map from Kum to Kum2. }
    f := ReadCurveFromKummer(Equation(Kum));
    
    kum_eqn_1, kum_eqn_2, _ := ComputeMapBetweenKummersOfTwists(f, f*d);
    Kum2 := Surface(ProjectiveSpace(Parent(kum_eqn_2)), kum_eqn_2);

    themap := func<kum_pt |
        Kum2![kum_pt[1], kum_pt[2], kum_pt[3], d*kum_pt[4]]>;
    return Kum2, themap;
end intrinsic;


intrinsic KummerSurfaceNice(Kum::Srfc) -> Srfc, Map
    { Let Kum be the Kummer surface scheme of a hyperelliptic curve. We
    transform the scheme to a new scheme Kum2 such that the quartic equation of
    Kum2 is of the correct form to read off the equation of the curve. We return
    Kum2 as well as the map Kum -> Kum2. }

    kum_eqn := Equation(Kum);
    f := ReadCurveFromKummer(kum_eqn);
    Kum2 := KummerSurfaceScheme(f);
    themap := func<kum_pt | Kum2!Eltseq(kum_pt)>;
    return Kum2, themap;
end intrinsic;


intrinsic TwoTorsionOnKummer(f::RngUPolElt) -> SetIndx
    { Computes the points on the Kummer surface of y^2 = f(x) corresponding to
    two-torsion points on the Jacobian. }
    quadratics := ComputeQuadraticsDividingF(f);

    if Degree(f) eq 5 then
        quadratics cat:= [factor[1] : factor in Factorisation(f)];
    end if;

    two_torsion := {};
    for quadratic in quadratics do
        two_torsion join:= {TwoTorsionOnKummer(quadratic, f)};
    end for;
    return {@ pt : pt in two_torsion @};
end intrinsic;


intrinsic TwoTorsionOnKummer(Kum::SrfKum) -> SetIndx
{ Computes the points on the Kummer surface corresponding to the 2-torsion points
on the Jacobian. }
    f := HyperellipticCurve(Kum);
    return TwoTorsionOnKummer(f);
end intrinsic;


intrinsic TwoTorsionOnKummer(G::RngUPolElt, f::RngUPolElt) -> SrfKumPt
    { Given a quadratic G dividing a degree 5 or 6 polynomial f, compute the
    corresponding 2-torsion point on the Kummer surface of y^2 = f(x). }
    J := Jacobian(HyperellipticCurve(f));
    Kum := KummerSurface(J);
    points := Points(Kum,
        [Coefficient(G, 2), -Coefficient(G, 1), Coefficient(G, 0)]);
    points := [[pt[i] : i in [1..4]] : pt in points];
    assert #points eq 1;
    return Kum!points[1];
end intrinsic;


intrinsic Double(P::Pt) -> Pt
    { Given a point on a Kummer surface scheme, computes its double, on the same
    Kummer surface scheme. }
    Kum_sch := Parent(P);
    assert Type(Kum_sch) eq Srfc;
    Kum := KummerSurface(Kum_sch);
    return Kum_sch!(Double(Kum!P));
end intrinsic;


intrinsic LiftToJacobian(pt::SrfKumPt) -> SetIndx
    { Lift the point on the Kummer surface of a hyperelliptic curve to the two
    points that lie above it on the Jacobian of the same hyperelliptic curve. }
    Kum := Parent(pt);
    J := Jacobian(Kum);
    return Points(J, pt);
end intrinsic;


intrinsic LiftToJacobianOfTwist(pt::SrfKumPt, twist::RngElt) -> SetIndx
    { Lift the point on the Kummer surface of a hyperelliptic curve y^2 = f(x)
    to the two points that lie above it on the Jacobian of the twisted
    hyperelliptic curve y^2 = twist * f(x). }
    return LiftToJacobian(TwistKummerPoint(pt, twist));
end intrinsic;


intrinsic Computea9Squared(f::RngUPolElt, ks::SeqEnum) -> RngElt
    { Computes a9^2 for the Kummer coordinates. It is an even function on the
    Jacobian, so is expressible in terms of the Kummer coordinates. }
    fs := [Coefficient(f, i) : i in [0..6]];
    f0 := fs[1];
    f1 := fs[2];
    f2 := fs[3];
    f3 := fs[4];
    f4 := fs[5];
    f5 := fs[6];
    f6 := fs[7];
    k1 := ks[1];
    k2 := ks[2];
    k3 := ks[3];
    k4 := ks[4];
    a9squared := k4 * k1^3 + f2 * k1^4 + f3 * k2*k1^3 + f4*k2^2*k1^2 +
    3*f5*k2*k3*k1^2 + f5*k2*(k2^2-4*k3*k1)*k1 + f6*k3^2*k1^2 +
    6*f6*k3*(k2^2-4*k3*k1)*k1 + 8*f6*k3^2*k1^2 + f6*(k2^2-4*k3*k1)^2;
    return a9squared;
end intrinsic;


intrinsic Computea9Squared(kum_pt::SrfKumPt) -> RngElt
    { Computes a9^2 for the Kummer coordinates. It is an even function on the
    Jacobian, so is expressible in terms of the Kummer coordinates. }
    Kum := Parent(kum_pt);
    f := HyperellipticCurve(Kum);
    f0 := Coefficient(f, 0);
    f1 := Coefficient(f, 1);
    f2 := Coefficient(f, 2);
    f3 := Coefficient(f, 3);
    f4 := Coefficient(f, 4);
    f5 := Coefficient(f, 5);
    f6 := Coefficient(f, 6);
    k1 := kum_pt[1];
    k2 := kum_pt[2];
    k3 := kum_pt[3];
    k4 := kum_pt[4];
    a9squared := k4 * k1^3 + f2 * k1^4 + f3 * k2*k1^3 + f4*k2^2*k1^2 +
    3*f5*k2*k3*k1^2 + f5*k2*(k2^2-4*k3*k1)*k1 + f6*k3^2*k1^2 +
    6*f6*k3*(k2^2-4*k3*k1)*k1 + 8*f6*k3^2*k1^2 + f6*(k2^2-4*k3*k1)^2;
    return a9squared;
end intrinsic;


intrinsic HyperellipticCurve(Kum::SrfKum) -> RngUPolElt
{ Computes the hyperelliptic curve for the given Kummer surface. }
    J := Jacobian(Kum);
    f := HyperellipticPolynomials(Curve(J));
    return f;
end intrinsic;


intrinsic TwistKummerPoint(kum_pt::SeqEnum, d::RngElt) -> SeqEnum
    { Twist the Kummer point by d. Returns [k1, k2, k3, d*k4]. }
    return kum_pt[1..3] cat [kum_pt[4] * d];
end intrinsic;


intrinsic TwistKummerPoint(kum_pt::SrfKumPt, d::RngElt) -> SrfKumPt
    { Twist the Kummer point by d. Returns [k1, k2, k3, d*k4] on the Kummer
    surface of y^2 = d * f(x). }
    Kum := Parent(kum_pt);
    f := HyperellipticCurve(Kum);
    J_twisted := Jacobian(HyperellipticCurve(d * f));
    Kum_twisted := KummerSurface(J_twisted);
    coordinates := [kum_pt[i] : i in [1..4]];
    coordinates_twisted := TwistKummerPoint(coordinates, d);
    return Kum_twisted!coordinates_twisted;
end intrinsic;


intrinsic LiftToJacobianOverExtension(kum_point::SrfKumPt, f::RngUPolElt)
    -> SeqEnum
    { Given a point on the Kummer of a genus 2 curve, return the two lifts to
    the Jacobian, possibly over a quadratic extension. }
    return LiftToJacobianOverExtension([kum_point[i] : i in [1..4]], f);
end intrinsic;


intrinsic LiftToJacobianOverExtension(kum_point::Pt, f::RngUPolElt)
    -> SeqEnum
    { Given a point on the Kummer of a genus 2 curve, return the two lifts to
    the Jacobian, possibly over a quadratic extension. }
    return LiftToJacobianOverExtension([kum_point[i] : i in [1..4]], f);
end intrinsic;


intrinsic LiftToJacobianOverExtension(kum_point::SeqEnum, f::RngUPolElt)
    -> SeqEnum
    { Given a point on the Kummer of a genus 2 curve, return the two lifts to
    the Jacobian, possibly over a quadratic extension.
    kum_point should be a list of length 4, denoting [xi0, xi1, xi2, xi3]
    that satisfies the Kummer equation for y^2 = f(x).
    We return the Jacobian J for y^2 = f as well as the two points on it that
    lie above the Kummer point. this is possibly defined over a quadratic
    extension of the Kummer points. }

    K := Universe(kum_point);
    Pk<k1,k2,k3,k4> := PolynomialRing(K, 4);
    kum_eqn := ComputeKummerEquation([Coefficient(f, i) : i in [0..6]], [Pk.i
    : i in [1..4]]);
    assert hom<Pk->Pk | kum_point>(kum_eqn) eq 0;

    // The point on the Kummer lifts to a point on the Jacobian if and only if
    // a9^2 is square. Indeed, once we have a9 being square, and all the Kummer
    // coordinates for the point are K-rational, then all the Jacobian
    // coordinates are K-rational also. This is transparent from the 72
    // quadratic equations defining the Kummer: each a_i / a_14 is linearly
    // defined in terms of the even functions and a_9/a_14.
    a92 := Computea9Squared(f, kum_point);
    if IsSquare(a92) then
        J := BaseChange(Jacobian(HyperellipticCurve(f)), K);
        Kum := KummerSurface(J);
        return Points(J, Kum!kum_point);
    else
        // First have to move to the quadratic extension so that a9^2 is square.
        Kquad := QuadraticExtension(K, a92);
        J := BaseChange(Jacobian(HyperellipticCurve(f)), Kquad);
        Kum := KummerSurface(J);
        return Points(J, Kum!kum_point);
    end if;
end intrinsic;


intrinsic ComputeAdditionByTwoTorsionOnKummer() -> Mtrx
{ Computes the addition by two-torsion matrix on the Kummer surface for the
Kummer surface of the curve y^2 = G * H, where G is a quadratic and H is a
quartic. }
    Kgh<g0,g1,g2, h0,h1,h2,h3,h4> := PolynomialRing(Rationals(), 8);

    return Matrix([
    [g2^2*h0 + g0*g2*h2 - g0^2*h4,
    g0*g2*h3 - g0*g1*h4,
    g1*g2*h3 - g1^2*h4 + 2*g0*g2*h4,
    g2],
    [-g0*g2*h1 - g0*g1*h2 + g0^2*h3,
    g2^2*h0 - g0*g2*h2 + g0^2*h4,
    g2^2*h1 - g1*g2*h2 - g0*g2*h3,
    -g1],
    [-g1^2*h0 + 2*g0*g2*h0 + g0*g1*h1,
    -g1*g2*h0 + g0*g2*h1,
    -g2^2*h0 + g0*g2*h2 + g0^2*h4,
    g0],
    [-g2*(g0^2*h1*h3 - g0*g1*h0*h3 + g0*g1*h1*h2 + 4*g0*g2*h0*h2 - g0*g2*h1^2 -
    g1^2*h0*h2 + g1*g2*h0*h1),
    -2*g0^2*g2*h1*h4 + g0*g1^2*h1*h4 + 4*g0*g1*g2*h0*h4 - g0*g1*g2*h1*h3 -
    2*g0*g2^2*h0*h3 - g1^3*h0*h4 + g1^2*g2*h0*h3,
    -g0*(g0*g1*h3*h4 + 4*g0*g2*h2*h4 - g0*g2*h3^2 - g1^2*h2*h4 - g1*g2*h1*h4 +
    g1*g2*h2*h3 + g2^2*h1*h3),
    -g0^2*h4 - g0*g2*h2 - g2^2*h0]]);
end intrinsic;


intrinsic ComputeAdditionByTwoTorsionOnKummer(G::RngUPolElt, H::RngUPolElt) -> .
    { Computes the addition by two-torsion matrix on the Kummer surface for the
    Kummer surface of the curve y^2 = G * H, where G is a quadratic and H is a
    quartic. }

    // g and h should be the quadratic and quartic such that y^2 = g*h is the
    // curve. It's OK if g * h has degree 5 or 6, but g defines the 2-torsion
    // point we want to add by.
    gcoeffs := [Coefficient(G, i) : i in [0..2]];
    hcoeffs := [Coefficient(H, i) : i in [0..4]];
    K := Universe(gcoeffs);
    M := ComputeAdditionByTwoTorsionOnKummer();
    _Malg := MatrixAlgebra(K, 4);
    Kgh := BaseRing(Parent(M));
    return hom<Parent(M)->_Malg | hom<Kgh->K | gcoeffs cat hcoeffs>>(M);
end intrinsic;


intrinsic ComputeAdditionByTwoTorsionOnKummer(splitting::SeqEnum) -> AlgMatElt,
    AlgMatElt, AlgMatElt
    { Computes the addition by two-torsion matrices for each 2-torsion point in
    the splitting. }
    W1 := ComputeAdditionByTwoTorsionOnKummer(splitting[1], splitting[2]*splitting[3]);
    W2 := ComputeAdditionByTwoTorsionOnKummer(splitting[2], splitting[1]*splitting[3]);
    W3 := ComputeAdditionByTwoTorsionOnKummer(splitting[3], splitting[1]*splitting[2]);
    return W1, W2, W3;
end intrinsic;


intrinsic TestAdditionByTwoTorsion() -> BoolElt
{ Tests if the addition by two torsion is working correctly. }
    P<x> := PolynomialRing(Rationals());
    // Define a quadratic g and quartic h. Twist the quartic so that x = 5 gives
    // a rational point on the curve.
    g := x^2 - 3*x + 2;
    h := (x+1) * (x+2) * (x+3) * (x+4);
    twist := Evaluate(g*h, 5);
    h *:= twist;
    f := g * h;

    _, y5 := IsSquare(Evaluate(f, 5));

    C := HyperellipticCurve(f);
    J := Jacobian(C);
    Kum := KummerSurface(J);
    // Define D = (5, y) + (-1, 0) - infty^+ - infty^-.
    D := elt<J | (x+1) * (x-5), 36288 / 6 * (x+1)>;
    kumD := Kum!D;

    T := elt<J | g, 0>;
    assert 2*T eq J!0;
    kumT := Kum!T;

    kumDpT := Kum!(D+T);

    // We expect to recover the Kummer coordinates of D + T.
    expected := [kumDpT[i] : i in [1..4]];

    // Compute the addition by two torsion matrix in the case of g, h.
    W := ComputeAdditionByTwoTorsionOnKummer(g, h);

    // We actually recover
    M := Transpose(Matrix(Rationals(), [[kumD[i] : i in [1..4]]]));
    computed := Matrix(W) * Matrix(M);

    computed := [computed[i][1] : i in [1..4]];

    // Assert that computed equals expected projectively (we can divide by the
    // first element in both vectors).
    assert [computed[i] / computed[1] : i in [1..4]] eq [expected[i] /
    expected[1] : i in [1..4]];

    return true;
end intrinsic;


intrinsic TranslationByTwoTorsionMap(kum_pt::SrfKumPt) -> Map
{ Let kum_pt be on the Kummer surface Kum that is the image of a 2-torsion point
on the Jacobian. We return the map Kum -> Kum that translates a point pt by kum_pt. }
    Kum := Parent(kum_pt);
    
    // Check that kum_pt is the image on the Jacobian of a 2-torsion point.
    assert Double(kum_pt) eq Kum![0, 0, 0, 1];

    f := HyperellipticCurve(Kum);
    P<x> := Parent(f);
    G := P!Polynomial([kum_pt[3], -kum_pt[2], kum_pt[1]]);
    H := f div G;

    W := ComputeAdditionByTwoTorsionOnKummer(G, H);

    assert TwoTorsionOnKummer(G, f) eq kum_pt;

    translation_image := function(kum_pt2)
        vec2 := Matrix(4, 1, Eltseq(kum_pt2));
        translated_coords := W * vec2;
        return Kum![translated_coords[i][1] : i in [1..4]];
    end function;

    return map<Kum->Kum | x :-> translation_image(x)>;
end intrinsic;


compute_factors_for_kummer := function(G, H)
    // Given G, H such that G corresponds to a 2-torsion point, we compute
    // the translation matrix on the Kummer, as well as the factors for its
    // eigenspaces to have eigenvectors on the Kummer. We also compute a9squared
    // whenever there is an eigenvector on the Kummer.
    f := G * H;
    W := ComputeAdditionByTwoTorsionOnKummer(G, H);

    c := (W^2)[1][1];
    assert IsSquare(c);
    
    eigenspaces := ComputeEigenspaces(W);

    eqn1 := ComputeHomogeneousEquationForLinearCombinationsOnTheKummer(
        eigenspaces[1], f);
    eqn2 := ComputeHomogeneousEquationForLinearCombinationsOnTheKummer(
        eigenspaces[2], f);

    factored_eqn1 := [factor[1] : factor in Factorisation(eqn1)];
    factored_eqn2 := [factor[1] : factor in Factorisation(eqn2)];

    discs1 := [FactorModSquares(
        NumeratorTimesDenominator(HomogeneousDiscriminant(factor))) : factor in
        factored_eqn1];
    discs2 := [FactorModSquares(
        NumeratorTimesDenominator(HomogeneousDiscriminant(factor))) : factor in
        factored_eqn2];

    soln1 := [LinearCombinationOfVectors(factor, eigenspaces[1]) : factor
        in factored_eqn1 | Degree(factor) eq 1];
    soln2 := [LinearCombinationOfVectors(factor, eigenspaces[2]) : factor
        in factored_eqn2 | Degree(factor) eq 1];

    return factored_eqn1, factored_eqn2, discs1, discs2, soln1, soln2;
end function;


intrinsic ComputeConditionsForEigenvectorOnTheKummer(splitting::SeqEnum) ->
    SeqEnum
    { }
    
    _, _, disc11, disc12, _, _ := compute_factors_for_kummer(splitting[1],
        splitting[2] * splitting[3]);
    _, _, disc21, disc22, _, _ := compute_factors_for_kummer(splitting[2],
        splitting[1] * splitting[3]);
    _, _, disc31, disc32, _, _ := compute_factors_for_kummer(splitting[3],
        splitting[1] * splitting[2]);
    conditions1 := disc11 cat disc12;
    conditions2 := disc21 cat disc22;
    conditions3 := disc31 cat disc32;
    return [conditions1, conditions2, conditions3];
end intrinsic;


intrinsic FactorsForEigenvectorsOnTheKummer(a::RngElt, b::RngElt, c::RngElt) ->
    SeqEnum
    { Returns the factors as given in my PhD thesis, evaluated at a, b, c. }
    factors_list := FactorsForEigenvectorsOnTheKummer();
    K := Universe(factors_list[1]);
    Kabc := FieldOfFractions(Universe([a, b, c]));
    spec_hom := hom<K->Kabc | a, b, c>;
    return [[spec_hom(factor) : factor in factors] : factors in factors_list];
end intrinsic;


intrinsic FactorsForEigenvectorsOnTheKummer() -> SeqEnum
    { Returns the factors as given in my PhD thesis. }
    K<a, b, c> := FunctionField(Rationals(), 3);
    return [
        [b, a*c, c, a*b],
        [(1-b) * (a-b), a * (1 - c) * (a - c), (1 - c) * (a - c), a * (1 - b) *
        (a - b)],
        [(a-c) * (a-b), b*c*(1-b) * (1-c), (1-b) * (1-c), b*c*(a-b) * (a-c)]
    ];
end intrinsic;


intrinsic ComputeHomogeneousEquationForLinearCombinationsOnTheKummer(
    xi_i::SeqEnum, f::RngUPolElt) -> SeqEnum
    { }
    K := BaseRing(Universe((xi_i)));
    P<a1, a2> := PolynomialRing(K, 2);
    ai := Matrix(P, [[a1], [a2]]);
    xi_matrix := ChangeRing(Transpose(Matrix(xi_i)), P);
    product := xi_matrix * ai;
    k1 := product[1][1];
    k2 := product[2][1];
    k3 := product[3][1];
    k4 := product[4][1];

    //kum_eqn_test := compute_kummer_equation([Coefficient(f, i) : i in [0..6]], [k1,k2,k3,k4]);
    kum_eqn := ComputeKummerEquation(f);
    Pk := Parent(kum_eqn);
    kum_eqn := hom<Pk->Parent(k1) | k1, k2, k3, k4>(kum_eqn);
    //assert kum_eqn eq kum_eqn_test;

    return kum_eqn;
end intrinsic;


intrinsic ComputePointsOnTheKummerGivenFactors(factor::RngMPolElt, xi_i::SeqEnum, f::RngUPolElt) -> SeqEnum
{ Given 4-dim vectors xi_i and a factor of the Kummer equation (in terms of a1
 and a2), compute the solutions that lie on the Kummer equation. }
    K := BaseRing(Universe(xi_i));
    Pk := Parent(factor);
    Pkt := PolynomialRing(K);
    print factor;
    if Degree(factor) gt 1 then
        K1 := SplittingField(hom<Pk->Pkt | Pkt.1, 1>(factor));
    else
        K1 := K;
    end if;
    P1 := PolynomialRing(K1);
    kum_points := [* *];
    roots1 := [rt[1] : rt in Roots(hom<Pk->P1 | P1.1, 1>(factor))];
    for rt in roots1 do
        lin_comb := ChangeRing(Transpose(Matrix(xi_i)), K1) * Matrix(K1, [[rt], [1]]);
        test := ComputeKummerEquation([Coefficient(f, i) : i in [0..6]], [lin_comb[i][1] : i in [1..4]]);
        assert test eq 0;
        Append(~kum_points, lin_comb);
    end for;
    return kum_points;
end intrinsic;


intrinsic ComputeLinearCombinationsOnTheKummer(xi_i, f) -> []
    { Computes the linear combinations of the vectors xi_i that lie on the
    Kummer surface of y^2 = f. }
    kum_eqn := ComputeHomogeneousEquationForLinearCombinationsOnTheKummer(xi_i,
        f);
    factors := [factor[1] : factor in Factorisation(kum_eqn)];
    kum_points := [* *];
    for factor in factors do
        kum_points cat:= ComputePointsOnTheKummerGivenFactors(factor,
        xi_i, f);
    end for;
    return kum_points;
end intrinsic;


intrinsic LinearCombinationOfVectors(factor, xi_i) -> AlgMatElt
    { Computes the linear combination of the vectors xi_i corresponding to the
    factor. The factor should be of the form a1 * c1 + a2 * c2, where c1, c2 are
    constants in the field. We compute a1 * xi_i[1] + a2 * xi_i[2]. }
    K := BaseRing(Universe(xi_i));
    Pk := Parent(factor);
    Pkt := PolynomialRing(K);
    assert Degree(factor) eq 1;

    c1 := MonomialCoefficient(factor, Pk.1);
    c2 := MonomialCoefficient(factor, Pk.2);

    return -c2 * xi_i[1] + c1 * xi_i[2];
end intrinsic;


intrinsic EigenvectorsOnTheKummer(W::Mtrx, f::RngUPolElt) -> SeqEnum
    { Computes the eigenvectors of the given matrix that lie on the Kummer
    surface of y^2 = f(x). }
    eigenspaces, eigenvectors := ComputeEigenspaces(W);

    kum_pts := [* *];
    for eigenspace in eigenspaces do
        eqn :=
            ComputeHomogeneousEquationForLinearCombinationsOnTheKummer(
                eigenspace, f);
        factors := [factor[1] : factor in Factorisation(eqn)];
        for factor in factors do
            if Degree(factor) eq 1 then
                kum_pt := LinearCombinationOfVectors(factor, eigenspace);
                Append(~kum_pts, kum_pt);
            end if;
        end for;
    end for;
    return kum_pts;
end intrinsic;


intrinsic FourTorsionOnTheKummer(f::RngUPolElt) -> SeqEnum
    { Computes the four torsion points that lie on the Kummer. }
    // First compute the 2-torsion points on the Jacobian and their W_T
    // matrices. Then compute the eigenvectors of these matrices that lie on the
    // Kummer.
    J := Jacobian(HyperellipticCurve(f));
    Kum := KummerSurface(J);
    quadratics := ComputeTwoTorsionPolynomials(f);
    kum_point_list := {};
    for g in quadratics do
        h := f div g;
        assert h * g eq f;
        W := ComputeAdditionByTwoTorsionOnKummer(g, h);
        kum_points := EigenvectorsOnTheKummer(W, f);
        kum_point_list join:= {ColumnVectorToSequence(pt) : pt in kum_points};
    end for;
    return SetToSequence(kum_point_list);
end intrinsic;


intrinsic ReduceModKummerEquation(elts::SeqEnum, kum_eqn::RngMPolElt) -> SeqEnum
    { Reduce all the expressions modulo the Kummer equation. }
    return [ ReduceModKummerEquation(poly, kum_eqn) : poly in elts];
end intrinsic;


intrinsic ReduceModKummerEquation(elt::RngMPolElt, kum_eqn::RngMPolElt) ->
    RngMPolElt
    { Reduce an expression in k1,k2,k3,k4 modulo the Kummer equation. We just
    replace all occurrences of k2^2*k4^2 with the other terms of the Kummer
    equation. }
    _P := Parent(elt);
    _k2 := _P.2;
    _k4 := _P.4;
    quot := _P!(_k2^2*_k4^2);
    q, r := Quotrem(_P!kum_eqn, _P!quot);
    lower := r;
    while true do
        q, r := Quotrem(elt, quot);
        elt := q * (-lower) + r;
        if q eq 0 then
            break;
        end if;
    end while;
    return elt;
end intrinsic;


intrinsic KummerPointToColumnVector(pt::SrfKumPt) -> ModMatFldElt
    { Converts the Kummer point to a 4x1 matrix with the corresponding
    coordinates. }
    return Transpose(Matrix([[pt[i] : i in [1..4]]]));
end intrinsic;


intrinsic KummerPointToSequence(pt::SrfKumPt) -> SeqEnum
    { Converts the Kummer point to a sequence. }
    return [pt[i] : i in [1..4]];
end intrinsic;


intrinsic PointToSequence(pt::Pt) -> SeqEnum
    { Converts the Kummer point to a sequence. }
    return [pt[i] : i in [1..4]];
end intrinsic;


intrinsic PointToSequence(pt::SrfKumPt) -> SeqEnum
    { Converts the Kummer point to a sequence. }
    return KummerPointToSequence(pt);
end intrinsic;



intrinsic EquationOfImageKummerSurface(images::SeqEnum, kum_eqn::RngMPolElt) -> RngMPolElt
{ kum_eqn should be a quartic in a polynomial ring with 4 variables (thought of
as k1, k2, k3, k4), defining the equation for Kum1. images should be a list
of 4 homogeneous forms in the ki, defining a function from Kum1 to Kum2. We
return the equation the images satisfy, i.e. the equation of Kum2. }
    Pk := Parent(kum_eqn);
    k1 := Pk.1;
    k2 := Pk.2;
    k3 := Pk.3;
    k4 := Pk.4;
    
    l1 := images[1];
    l2 := images[2];
    l3 := images[3];
    l4 := images[4];

    // Compute quartics in the li, and reduce them modulo the Kummer equation.
    // Either use the exact monomials required, or just all quartics in ki.
    exact_monomials := [k4^2 * k2^2, k4^2 * k1 * k3];
    exact_monomials cat:= [k4 * mon : mon in DegreeNCombinations([k1,k2,k3], 3)];
    exact_monomials cat:= DegreeNCombinations([k1,k2,k3], 4);

    // Use all quartics in ki.
    exact_monomials := DegreeNCombinations([k1,k2,k3,k4], 4);
    quartics := [hom<Pk->Pk | l1, l2, l3, l4>(mon) : mon in exact_monomials];
    
    //quartics := DegreeNCombinations([l1, l2, l3, l4], 4);
    quartics := ReduceModKummerEquation(quartics, kum_eqn);

    // Now find the linear relations that the quartics satisfy.
    nullspace, V, monomials := LinearRelationsBetweenPolynomials(quartics);

    // Return the equation that the quartics satisfy as a polynomial in ki.
    quartics_ki := exact_monomials;
    basis := Basis(nullspace);
    vec := basis[1];
    
    eqn := ChangeRing(Matrix(vec), Pk) * Transpose(Matrix(Pk, [quartics_ki]));
    return eqn[1][1];
end intrinsic;