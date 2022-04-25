

intrinsic ComputeRichelotChangeOfBasis(splitting::SeqEnum) -> List
{ This function takes in a quadratic splitting of a genus 2 curve and computes
    the Richelot isogeny on Kummer surfaces. Let Ti denote the 2-torsion point
    corresponding to Gi. Let Wi be the corresponding addition by 2-torsion
    matrix. }

    f := Product(splitting);
    W1, W2, W3 := ComputeAdditionByTwoTorsionOnKummer(splitting);
    K := CoefficientRing(Universe(splitting));

    // We require here that the minimal polynomial of each Wi splits, so that we
    // can diagonalise them.
    min_polys := [MinimalPolynomial(W) : W in [W1, W2, W3]];
    K := SplittingField(min_polys);
    W1 := ChangeRing(W1, K);
    W2 := ChangeRing(W2, K);
    W3 := ChangeRing(W3, K);
    f := ChangeRing(f, K);
    // assert {Max([Degree(factor[1]) : factor in Factorisation(poly)]) : poly in min_polys} eq {1};

    // Simultaneously diagonalise the Wi.
    Dis, theta1 := SimultaneousDiagonalisation([W1, W2, W3]);

    kum_eqn := ComputeKummerEquation(f);
    Pk<k1,k2,k3,k4> := Parent(kum_eqn);

    // If theta1 * W_T * theta1^-1 = L is diagonal, then using l = theta1 * k
    // gives l(D+T) = theta1 * k(D+T) = theta1 * W_T * k(D) / c_T = theta1 * W_T
    // * theta1^-1 l(D) / c_T = L * l(D) / c_T, and so l is invariant under
    // translation by T.
    li := ChangeRing(theta1^-1, Pk) * Matrix(Pk, [[k1], [k2], [k3], [k4]]);

    // Express ki in terms of li. Then the equation li satisfy is just the
    // equation that ki satisfy, with li in place of ki.
    Pl<l1,l2,l3,l4> := PolynomialRing(K, 4);
    ki := ChangeRing(theta1, Pl) * Matrix(Pl, [[l1], [l2], [l3], [l4]]);
    kum_eqn_li := hom<Pk->Pl | [ki[i][1] : i in [1..4]]>(kum_eqn);
    evaluate_kum_eqn_li := hom<Pl->Pk | [li[i][1] : i in [1..4]]>(kum_eqn_li);
    assert ReduceModKummerEquation(evaluate_kum_eqn_li, kum_eqn) eq 0;

    quadratics_li := [li[i][1]^2 : i in [1..4]];
    quadratics_li := [ReduceModKummerEquation(l, kum_eqn) : l in quadratics_li];

    // We now compute the equation that li^2 satisfy in terms of ki.
    print "Computing equation of image";
    time kum_eqn_2_ki := EquationOfImageKummerSurface(quadratics_li, kum_eqn);

    print "Reducing";
    // Check that the li^2 satisfy the Kummer equation.
    time assert ReduceModKummerEquation(hom<Pk->Pk | [li[i][1]^2 : i in
        [1..4]]>(kum_eqn_2_ki), kum_eqn) eq 0;

    // Now translate this equation into a quartic that the li satisfy";
    // First have to normalise the quadratics so that they start with k1*k4,
    // k2*k4, k3*k4, k4*k4, respectively.
    norm_M, norm_quadratics_li := NormaliseQuadraticsForKummer(quadratics_li);
    expected := norm_quadratics_li;
    computed := ChangeRing(norm_M^-1, Universe(quadratics_li)) * Transpose(Matrix([quadratics_li]));
    computed := [computed[i][1] : i in [1..4]];
    assert expected eq computed;

    transformed_inv := ChangeRing(norm_M, Pk) * Matrix(Pk, [[k1], [k2], [k3], [k4]]);
    kum_eqn_test := hom<Pk->Pk | [transformed_inv[i][1] : i in [1..4]]>(kum_eqn_2_ki);
    Ma, kum_eqn_soln := RemoveBadMonomialsFromKummerEquation(kum_eqn_test);
    kum_eqn_soln := hom<Parent(kum_eqn_soln)->Pk | k1,k2,k3,k4>(kum_eqn_soln);

    // The curve of our Kummer equation is:
    curve_from_quartic := ReadCurveFromKummer(kum_eqn_soln);
    curve_from_quartic := ChangeRing(curve_from_quartic, K);

    // We now have a Kummer equation for a twist of curved.
    // We also compute the splitting of the isogenous curve.
    delta := ComputeRichelotDelta(splitting);
    Ls := ComputeRichelotLs(splitting);
    curved := delta * Ls[1] * Ls[2] * Ls[3];
    curved := ChangeRing(curved, K);
    assert curved / LeadingCoefficient(curved) eq curve_from_quartic / LeadingCoefficient(curve_from_quartic);

    // We can compute the Kummer equation of the correct twist:
    kum_curved, kum_curve_from_quartic, theta_d_quartic := ComputeMapBetweenKummersOfTwists(curved, curve_from_quartic);
    kum_curved := hom<Parent(kum_curved)->Pk | k1,k2,k3,k4>(kum_curved);
    kum_curve_from_quartic := hom<Parent(kum_curve_from_quartic)->Pk |
        k1,k2,k3,k4>(kum_curve_from_quartic);

    // Check that the Kummer equations are equal.
    assert NormalisePolynomial(kum_curve_from_quartic) eq
        NormalisePolynomial(kum_eqn_soln);

    kum_eqns := [* kum_eqn, kum_eqn_li, kum_eqn_2_ki, kum_curved *];

    theta2 := norm_M * Ma * theta_d_quartic;
    computed := ChangeRing(theta2^-1, Universe(quadratics_li)) * Transpose(Matrix([quadratics_li]));
    computed := [computed[i][1] : i in [1..4]];
    time eqn_of_image := EquationOfImageKummerSurface(computed, kum_eqn);
    assert IsDivisibleBy(eqn_of_image, kum_curved);

    assert ReduceModKummerEquation(hom<Pk->Pk | computed>(kum_curved), kum_eqn) eq 0;

    richelot_data := [* splitting, theta1, theta2, kum_eqns, f, curved, Ls *];
    return richelot_data;
end intrinsic;