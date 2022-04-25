


intrinsic TwoWeilPairing(P::JacHypPt, Q::JacHypPt) -> RngElt
    {Computes the 2-Weil pairing for 2-torsion points P and Q on the Jacobian of
    a curve y^2 = f(x). }
    J := Parent(P);
    // Need both points to be 2-torsion.
    assert 2 * P eq J!0;
    assert 2 * Q eq J!0;

    // The Weil pairing is alternating, so e2(P, P) = 1.
    if P eq Q then
        return 1;
    elif P eq J!0 then
        return 1;
    elif Q eq J!0 then
        return 1;
    end if;

    // The 2-Weil pairing can be computed by looking at the quadratic (or
    // linear) polynomials defining the 2-torsion points. If they are coprime,
    // then e2(P, Q) = 1. Otherwise, e2(P, Q) = -1.
    poly_P := P[1];
    poly_Q := Q[1];

    // Check whether the curve has degree 5 or 6 polynomial.
    f := HyperellipticPolynomials(Curve(J));

    // If degree 5 and both torsion points are of the form A - infty, B - infty,
    // with A, B on the curve and A, B distinct, then they have Weil pairing -1.
    // To see this, if we map to a degree 6 form for the curve, then the inftys
    // would map to an affine Weierstrass point.
    if Degree(f) eq 5 then
        if Degree(poly_P) eq 1 and Degree(poly_Q) eq 1 then
            return -1;
        end if;
    end if;

    if GCD(poly_P, poly_Q) eq 1 then
        return 1;
    end if;
    return -1;
end intrinsic;
