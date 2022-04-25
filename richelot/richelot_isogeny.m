
import "four_four/richelotisogenyonkummer.m": compute_richelot_on_kummers,
    richelot_img, lift_to_jacobian, richelot_preimages, richelot_img_general,
    compute_quadratic_splittings;
import "four_four/kummerfunctions.m": equation_of_image, reduce,
    normalise_quadratics, remove_bad_monomials, read_curve_from_quartic,
    compute_map_between_kummers_of_twists;


intrinsic ComputeRichelotOnKummers(Gs::[ ]) -> SrfKum, SrfKum, .
    { Computes the Richelot isogeny associated to y^2 = G1 * G2 * G3 on the
    Kummer of the curve. Returns the Kummer surface of the original curve and
    the Kummer surface of the isogenous curve.}
    richelot_data := compute_richelot_on_kummers(Gs[1], Gs[2], Gs[3]);
    f := richelot_data[5];
    fd := richelot_data[6];
    C := HyperellipticCurve(f);
    Cd := HyperellipticCurve(fd);
    J := Jacobian(C);
    Jd := Jacobian(Cd);
    Kum := KummerSurface(J);
    Kumd := KummerSurface(Jd);
    return Kum, Kumd, richelot_data;
end intrinsic;


intrinsic CreateRichelotIsogenyOnKummers(Gs::[ ]) -> UserProgram
    { Returns a map from the Kummer of y^2 = Gs[1] * Gs[2] * Gs[3] to the Kummer
    of y^2 = delta * Ls[1] * Ls[2] * Ls[3]. }
    Kum1, Kum2, richelot_data := ComputeRichelotOnKummers(Gs);
    return map<Kum1->Kum2 | y:->Kum2!richelot_img(richelot_data, Eltseq(y))>;
end intrinsic;


intrinsic CreateRichelotIsogenyOnKummersGeneral(Gs::[ ]) -> Srfc, Srfc, Map
    { Returns the Kummer surface of y^2 = Gs[1] * Gs[2] * Gs[3], the Kummer
    surface of y^2 = delta * Ls[1] * Ls[2] * Ls[3] and the map between them
    corresponding to the Richelot isogeny. }
    Kum1, Kum2, richelot_data := ComputeRichelotOnKummers(Gs);
    kum_eqn_1 := DefiningPolynomial(Kum1);
    kum_eqn_2 := DefiningPolynomial(Kum2);
    Pk := Parent(kum_eqn_1);
    KumSch1 := Surface(ProjectiveSpace(Pk), kum_eqn_1);
    KumSch2 := Surface(ProjectiveSpace(Pk), kum_eqn_2);

    general_map := richelot_img_general(richelot_data);

    themap := map<KumSch1->KumSch2 | ChangeUniverse(general_map, Pk)>;

    return KumSch1, KumSch2, themap;
end intrinsic;


intrinsic ComputeRichelotOnKummersLocalGeneral(richelot_isogeny::Map,
    Qp::FldPad) -> Map
    { Given a Richelot isogeny computed from
    CreateRichelotIsogenyOnKummersGeneral, we base change to a p-adic field, Qp.
    }
    Kum1 := Domain(richelot_isogeny);
    Kum2 := Codomain(richelot_isogeny);

    assert Type(Kum1) eq Srfc;
    assert Type(Kum2) eq Srfc;

    Kum1_kum := KummerSurface(Kum1);
    Kum2_kum := KummerSurface(Kum2);

    Kum1_p := BaseChange(Kum1_kum, Qp);
    Kum2_p := BaseChange(Kum2_kum, Qp);

    Pk<k1,k2,k3,k4> := PolynomialRing(Qp, 4);
    map_polys := [* Pk!ChangeRing(poly, Qp) : poly in
        DefiningPolynomials(richelot_isogeny) *];

    themap := func<kum_pt | Kum2_p![Evaluate(map_poly, Eltseq(kum_pt)) : map_poly in map_polys]>;
    return Kum1_p, Kum2_p, themap;
end intrinsic;


twist_kummer_point := function(kum_pt, twist)
    return [kum_pt[i] : i in [1..3]] cat [kum_pt[4] * twist];
end function;


intrinsic CreateDualRichelotIsogenyOnKummersGeneral(Gs::[ ]) -> Map
    { Returns a map from the Kummer of y^2 = delta * Ls[1] * Ls[2] * Ls[3] to
    the Kummer of y^2 = Gs[1] * Gs[2] * Gs[3]. }
    Ls := ComputeRichelotLs(Gs);
    delta := ComputeRichelotDelta(Gs);
    deltad := ComputeRichelotDelta(Ls);
    fd := delta * Product(Ls);
    f := Product(Gs);

    Kum2, Kum1, dual_richelot_isogeny :=
        CreateRichelotIsogenyOnKummersGeneral(Ls);

    Kumd := KummerSurfaceScheme(fd);
    Kum := KummerSurfaceScheme(f);

    // We now have to get the twists right. We currently have a map from Kum2:
    // y^2 = Ls[1] * Ls[2] * Ls[3] to Kum1: y^2 = deltad * Hs[1] * Hs[2] *
    // Hs[3], where Hs are the Richelot Ls for Ls and deltad is the delta for
    // Ls.
    // By explicitly computing deltad and Ls generally, we find that deltad =
    // -2*delta^2 and Hs[i] = -2*delta * Gs[i] for each i.
    // We first need to map from Kumd: y^2 = delta * Ls[1] * Ls[2] * Ls[3] to
    // Kum2, then use the isogeny Kum2 -> Kum1, then map from Kum1 to Kum: y^2 =
    // Gs[1] * Gs[2] * Gs[3].
    // The first is just a twist by 1/delta and the last is a twist by
    // 1/(-2*delta^2) * 1/(-2*delta^2)^3 = 1/(16*delta^6).
    // TODO: Work out why we separately need to twist by delta in the last map.

    polys := DefiningPolynomials(dual_richelot_isogeny);
    Pk := Universe(polys);
    twist_polys := [Evaluate(poly, Pk.4, 1/delta * Pk.4) : poly in polys];
    twist_polys[4] := delta / (16 * delta^6) * twist_polys[4];

    themap := map<Kumd->Kum | twist_polys>;

    return Kumd, Kum, themap;
end intrinsic;


intrinsic CreateDualRichelotIsogenyOnKummers(Gs::[ ]) -> Map
    { Returns a map from the Kummer of y^2 = delta * Ls[1] * Ls[2] * Ls[3] to
    the Kummer of y^2 = Gs[1] * Gs[2] * Gs[3]. }
    Ls := ComputeRichelotLs(Gs);
    delta := ComputeRichelotDelta(Gs);
    deltad := ComputeRichelotDelta(Ls);
    fd := delta * Ls[1] * Ls[2] * Ls[3];
    f := Gs[1] * Gs[2] * Gs[3];

    dual_richelot_isogeny := CreateRichelotIsogenyOnKummers(Ls);
    Kum2 := Domain(dual_richelot_isogeny);
    Kum1 := Codomain(dual_richelot_isogeny);

    Kumd := KummerSurface(fd);
    Kum := KummerSurface(f);

    // We now have to get the twists right. We currently have a map from Kum2:
    // y^2 = Ls[1] * Ls[2] * Ls[3] to Kum1: y^2 = deltad * Hs[1] * Hs[2] *
    // Hs[3], where Hs are the Richelot Ls for Ls and deltad is the delta for
    // Ls.
    // By explicitly computing deltad and Ls generally, we find that deltad =
    // -2*delta^2 and Hs[i] = -2*delta * Gs[i] for each i.
    // We first need to map from Kumd: y^2 = delta * Ls[1] * Ls[2] * Ls[3] to
    // Kum2, then use the isogeny Kum2 -> Kum1, then map from Kum1 to Kum: y^2 =
    // Gs[1] * Gs[2] * Gs[3].
    // The first is just a twist by 1/delta and the last is a twist by
    // 1/(-2*delta^2) * 1/(-2*delta^2)^3 = 1/(16*delta^6).
    // TODO: Work out why we separately need to twist by delta in the last map.

    themap := map<Kumd->Kum |
        y:->Kum!twist_kummer_point(Eltseq(dual_richelot_isogeny(
            twist_kummer_point(y, 1/delta))), delta/(16 * delta^6))>;
    return themap;
end intrinsic;


intrinsic ComputeImageOfKummerPointUnderRichelotIsogeny(richelot_data::.,
    kum_pt::[ ]) -> [ ]
    { Given richelot_data, computed from ComputeRichelotOnKummers, and a point
    on the Kummer of the original curve, we compute the image of kum_pt under
    the Richelot isogeny. This image lies on the Kummer of the isogenous curve.
    }
    return richelot_img(richelot_data, kum_pt);
end intrinsic;


intrinsic ComputeImageOfJacobianPointUnderRichelotIsogeny(richelot_data::.,
    jac_pt::JacHypPt) -> { }
    { Given richelot_data, computed from ComputeRichelotOnKummers, and a point
    on the Jacobian of the original curve, we compute the image of jac_pt under
    the Richelot isogeny. This image lies on the Jacobian of the isogenous
    curve. However, we only compute this point up to sign, so we actually return
    a point together with its inverse. }
    f := richelot_data[5];
    fd := richelot_data[6];
    J := Jacobian(HyperellipticCurve(f));
    Kum := KummerSurface(J);
    assert jac_pt in J;
    kum_pt := Eltseq(Kum!jac_pt);
    kum_img := richelot_img(richelot_data, kum_pt);
    return lift_to_jacobian(kum_img, fd);
end intrinsic;


intrinsic ComputePreimagesUnderRichelot(richelot_data::., jac_pt::JacHypPt) 
    -> { }
    { Computes the preimages of the point on the Jacobian under the Richelot
    isogeny defined by richelot_data. Since we actually only compute this on the
    Kummer, we return the preimages up to sign. }
    J := Parent(jac_pt);
    Kum := KummerSurface(J);
    kum_pt := Eltseq(Kum!jac_pt);
    preimages := richelot_preimages(richelot_data, kum_pt);
    preimages := [pt : pt in Set(preimages)];
    f := richelot_data[5];
    jac_preimages := Union({lift_to_jacobian(Eltseq(pt), f) : pt in preimages});
    return {@ pt : pt in jac_preimages @};
end intrinsic;


intrinsic TwistRichelotIsogenyOnKummers(richelot::Map, twist::RngElt) -> Map
    { Given a map, created by RichelotIsogenyOnKummersGeneral, twist this map by
    'twist'. If the original map is between y^2 = Product(Gs) and y^2 = delta *
    Product(Ls), then the returned map is between y^2 = twist * Product(Gs) and
    y^2 = twist * delta * Product(Ls). }
    // TODO: Implement.
    
    error "Not implemented yet";
    return richelot;
end intrinsic;


intrinsic ComputeQuadraticSplittings(f::RngUPolElt) -> [ ]
    { Computes all quadratic splittings for a degree 5 or 6 polynomial. That is,
    computes all unordered monic triples q1, q2, q3 such that q1*q2*q3 = d * f
    for some constant d, and such that Degree(qi) <= 2 for each i. }
    
    splittings := compute_quadratic_splittings(f);
    // Return the splittings, converted to a list.
    return [[poly : poly in splitting] : splitting in splittings];
end intrinsic;


intrinsic ComputeRichelotChangeOfBasis(splitting::SeqEnum) -> .
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
    assert {Max([Degree(factor[1]) : factor in Factorisation(poly)]) : poly in
        min_polys} eq {1};

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
    time kum_eqn_2_ki := equation_of_image(quadratics_li, kum_eqn);

    print "Reducing";
    // Check that the li^2 satisfy the Kummer equation.
    time assert ReduceModKummerEquation(hom<Pk->Pk | [li[i][1]^2 : i in
        [1..4]]>(kum_eqn_2_ki), kum_eqn) eq 0;

    // Now translate this equation into a quartic that the li satisfy";
    // First have to normalise the quadratics so that they start with k1*k4,
    // k2*k4, k3*k4, k4*k4, respectively.
    norm_M, norm_quadratics_li := normalise_quadratics(quadratics_li);
    expected := norm_quadratics_li;
    computed := ChangeRing(norm_M^-1, Universe(quadratics_li)) * Transpose(Matrix([quadratics_li]));
    computed := [computed[i][1] : i in [1..4]];
    assert expected eq computed;

    transformed_inv := ChangeRing(norm_M, Pk) * Matrix(Pk,
        [[k1], [k2], [k3], [k4]]);
    kum_eqn_test := hom<Pk->Pk | [transformed_inv[i][1] : i in
        [1..4]]>(kum_eqn_2_ki);
    Ma, kum_eqn_soln := remove_bad_monomials(kum_eqn_test);
    kum_eqn_soln := hom<Parent(kum_eqn_soln)->Pk | k1,k2,k3,k4>(kum_eqn_soln);

    // The curve of our Kummer equation is:
    curve_from_quartic := read_curve_from_quartic(kum_eqn_soln);
    curve_from_quartic := ChangeRing(curve_from_quartic, K);

    // We now have a Kummer equation for a twist of curved.
    // We also compute the splitting of the isogenous curve.
    delta := ComputeRichelotDelta(splitting);
    Ls := ComputeRichelotLs(splitting);
    curved := delta * Ls[1] * Ls[2] * Ls[3];
    curved := ChangeRing(curved, K);
    assert curved / LeadingCoefficient(curved) eq curve_from_quartic / LeadingCoefficient(curve_from_quartic);

    // We can compute the Kummer equation of the correct twist:
    kum_curved, kum_curve_from_quartic, theta_d_quartic :=
        compute_map_between_kummers_of_twists(curved, curve_from_quartic);
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
    time eqn_of_image := equation_of_image(computed, kum_eqn);
    assert IsDivisibleBy(eqn_of_image, kum_curved);

    assert ReduceModKummerEquation(hom<Pk->Pk | computed>(kum_curved), kum_eqn)
        eq 0;

    richelot_data := [* splitting, theta1, theta2, kum_eqns, f, curved, Ls *];
    return richelot_data;
end intrinsic;

