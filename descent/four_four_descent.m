import "four_four/four_four_family.m": four_four_family_t,
    four_four_family_spec;


intrinsic FourFourFamilyNormalised(a::RngElt, b::RngElt, c::RngElt) -> SeqEnum
    { Returns a curve y^2 = f(x) with f(x) monic that admits a Richelot isogeny
    to the curve y^2 = x * (x-1) * (x-a) * (x-b) * (x-c). }

    K := FieldOfFractions(Universe([a, b, c]));
    P<x> := PolynomialRing(K);

    splitting1d := [x, (x-1) * (x-a), (x-b) * (x-c)];
    splitting1, _ := ComputeRichelotIsogenousCurveNoDelta(splitting1d);
    splitting1 := [Normalise(poly) : poly in splitting1];

    splitting1d, f2 := ComputeRichelotIsogenousCurveNoDelta(splitting1);
    return splitting1;
end intrinsic;


intrinsic ComputeImageInGroupUsingShifts(the_map::Map, point::Any, other_points::SeqEnum) -> GrpAbElt
{ Tries to compute the_map on point. If this is not possible, then we compute
the_map(point + other_point) - the_map(other_point). We assume that the_map is
a homomorphism of abelian groups, so that we can add and subtract points in the
domain and codomain, and use the homomorphism property. }
    try
        return the_map(point);
    catch e
        print "Couldn't immediately compute the map on", point;
    end try;

    error_points := [];

    for other_point in other_points do
        try
            return the_map(point + other_point) - the_map(other_point);
        catch e
            Append(~error_points, other_point);
        end try;
    end for;
    print "Couldn't compute the map on shifts of", point;
    assert false;
end intrinsic;


intrinsic FourFourFamilyRationalKernel(l::RngElt) -> SeqEnum, SeqEnum
{ Computes the subfamily of the four four family whose curve contains the point (v, 0), where
v is defined as in the function. }
    t := 2;
    s := (-2 * t^3 + 2 * t) * l / (l^2 + t^2 - 1);
    v := t * (l^2 + 1 - t^2) / (l^2 + t^2 - 1);
    splitting1, splitting1d := FourFourFamilyRationalKernel(s, t, v);
    return splitting1, splitting1d;
end intrinsic;


intrinsic FourFourFamilyRationalKernel(s::RngElt, t::RngElt, v::RngElt) ->
    SeqEnum, SeqEnum
    { Computes the family currently written in the thesis. }
    splitting1, splitting1d := FourFourFamilyRationalKernel();
    P := Universe(splitting1);
    K := CoefficientRing(P);
    Kstv := FieldOfFractions(Universe([s, t, v]));
    Pstv<x> := PolynomialRing(Kstv);
    spec_hom := hom<P->Pstv | hom<K->Kstv | s, t, v>, Pstv.1>;
    splitting1_spec := [spec_hom(poly) : poly in splitting1];
    splitting1d_spec := [spec_hom(poly) : poly in splitting1d];
    f1_spec := Product(splitting1_spec);
    assert Discriminant(f1_spec) ne 0;
    return splitting1_spec, splitting1d_spec;
end intrinsic;


intrinsic FourFourFamilyRationalKernel(s::FldRatElt, t::FldRatElt, v::FldRatElt) ->
    SeqEnum, SeqEnum
    { Computes the family currently written in the thesis. }
    splitting1, splitting1d := FourFourFamilyRationalKernel();
    P := Universe(splitting1);
    K := CoefficientRing(P);
    PQ<x> := PolynomialRing(Rationals());
    spec_hom := hom<P->PQ | hom<K->Rationals() | s, t, v>, PQ.1>;
    splitting1_spec := [spec_hom(poly) : poly in splitting1];
    splitting1d_spec := [spec_hom(poly) : poly in splitting1d];
    f1_spec := Product(splitting1_spec);
    assert Discriminant(f1_spec) ne 0;
    return splitting1_spec, splitting1d_spec;
end intrinsic;


intrinsic FourFourFamilyRationalKernel() -> SeqEnum, SeqEnum
    { Computes the family currently written in the thesis. }
    Kstv<s, t, v> := FunctionField(Rationals(), 3);
    P<x> := PolynomialRing(Kstv);
    u := (-s^2 * (s^2 - t^4 + t^2)*v^2 - 2*(s^2 - t^4 + t^2)*v - 1) /
        (-s^2 * t * (s^2 - t^4 + t^2)*v^2 + t);
    a := (s^2 - t^4 + t^2) / (1 - t^2);
    b := (s^2 - t^4 + t^2) / (s^2 * u^2 + 1 - t^2);
    c := t^2;

    twist := (s^2 - t^4 + t^2) * (s^2*u^2 + t^4 - 2*t^2 + 1) * (s^4*u^2 -
        s^2*t^2*u^2 + s^2*u^2 - t^6 + 3*t^4 - 3*t^2 + 1);

    // Need to twist the curve by twist so that the 4-torsion divisors are
    // rational.
    splitting1 := FourFourFamilyNormalised(a, b, c);
    splitting1[1] := twist * splitting1[1];

    splitting1d, f2 := ComputeRichelotIsogenousCurveNoDelta(splitting1);

    return splitting1, splitting1d;
end intrinsic;


intrinsic FourFourFamily(a1, a2, a3, a4, a5) -> SeqEnum
    { Returns [G1, G2, G3] such that y^2 = G1 * G2 * G3 admits a (4, 4)-isogeny.
    The family has 3 parameters. It is the image under the Richelot isogeny of
    y^2 = (x-a1) (x-a2) (x-a3) (x-a4) (x-a5) given by [x-a1, (x-a2)(x-a3), (x-a4)(x-a5)].}

    K := FieldOfFractions(Universe([a1, a2, a3, a4, a5]));
    P<x> := PolynomialRing(K);
    splitting := [x-a1, (x-a2) * (x-a3), (x-a4) * (x-a5)];
    splittingd := ComputeRichelotIsogenousCurveNoDelta(splitting);

    return splittingd;
end intrinsic;


intrinsic FourFourFamily() -> SeqEnum
    { Returns [G1, G2, G3] such that y^2 = G1 * G2 * G3 admits a (4, 4)-isogeny.
    The family has 3 parameters. It is the image under the Richelot isogeny of
    y^2 = x (x-1) (x-a) (x-b) (x-c) given by [x, (x-1)(x-a), (x-b)(x-c)].}

    K<a, b, c> := FunctionField(Rationals(), 3);
    P<x> := PolynomialRing(K);
    splitting := [x, (x-1) * (x-a), (x-b) * (x-c)];
    splittingd := ComputeRichelotIsogenousCurveNoDelta(splitting);

    return splittingd;
end intrinsic;


intrinsic FourFourFamily(abc::SeqEnum) -> SeqEnum
    { Returns [G1, G2, G3] such that y^2 = G1 * G2 * G3 admits a (4, 4)-isogeny.
    The family has 3 parameters. It is the image under the Richelot isogeny of
    y^2 = x (x-1) (x-a) (x-b) (x-c) given by [x, (x-1)(x-a), (x-b)(x-c)].}

    return FourFourFamily(abc[1], abc[2], abc[3]);
end intrinsic;


intrinsic FourFourFamily(a::RngElt, b::RngElt, c::RngElt) -> SeqEnum
    { Returns [G1, G2, G3] such that y^2 = G1 * G2 * G3 admits a (4, 4)-isogeny.
    The family has 3 parameters. It is the image under the Richelot isogeny of
    y^2 = x (x-1) (x-a) (x-b) (x-c) given by [x, (x-1)(x-a), (x-b)(x-c)].}

    P<x> := PolynomialRing(Rationals());
    splitting := [x, (x-1) * (x-a), (x-b) * (x-c)];
    splittingd := ComputeRichelotIsogenousCurveNoDelta(splitting);

    return splittingd;
end intrinsic;


intrinsic FourFourFamilyBothSplitGeneral() -> RngUPolElt
    { The subfamily where both curves are split. }
    return four_four_family_t();
end intrinsic;


intrinsic FourFourFamilyBothSplit(s::RngElt, t::RngElt) -> RngUPolElt
    { The subfamily where both curves are split, for a particular s and t. }
    return four_four_family_spec(s, t);
end intrinsic;


intrinsic GenerateFourFourFromRichelot(richelot2::Map, gens2mod1::[ ], gens3mod2::[ ]) -> SetIndx
    { Given generators Di for J3 / phi2(J2) and generators Ej for J2 / phi1(J1),
    we compute generators for J3 / phi2(phi1(J1)) as Di together with phi2(Ej).
    The generators gens2mod1 and gens3mod2 should be elements of the Jacobians
    J2 and J3, respectively.}

    images := [pt : pt in gens3mod2];
    for gen in gens2mod1 do
        Kum2 := Domain(richelot2);
        image_kum := richelot2(Kum2!gen);
        images_jac := LiftToJacobian(image_kum);

        // The Kummer point lifts to two points on the Jacobian, P and Pbar, the
        // image under the hyperelliptic involution. We only need one of these
        // as a generator.
        Append(~images, images_jac[1]);
    end for;
    return images;
end intrinsic;


intrinsic GenerateFourFourLocalPoints(splitting1::SeqEnum, splitting2::SeqEnum,
    p::RngIntElt :
    global_points1 := [], global_points2 := [], global_points3 := []) -> SeqEnum, SeqEnum
{ Generate the local points for J / psid Jd and Jd / psi J, where psi is the
(4, 4)-isogeny psi = phi2 phi1.
splitting1 is the Richelot splitting for the first Richelot and splitting2
is the Richelot splitting for the second Richelot.

The difference with GenerateFourFourLocalTriples is that here we localise the global
points first. The issue is that sometimes Magma cannot localise global points. }
    // Let the Jacobians be J, J2, J3, where the Richelot isogenies are phi1: J
    // -> J2, phi2: J2 -> J3 and their duals are phi2d: J3 -> J2, phi1d: J2 ->
    // J. Let psi = phi2 phi1, psid = phi1d phi2d be the (4, 4)-isogeny.
    // We generate local points for J3 / psi J by taking generators for J3 /
    // phi2 J2 together with the images of generators for J2 / phi1 J under
    // phi2.

    // Localises all the points first.
    

    splitting1d := ComputeRichelotIsogenousCurveNoDelta(splitting1);
    splitting2d := ComputeRichelotIsogenousCurveNoDelta(splitting2);

    richelot2 := RichelotOnKummerMap(splitting2);
    richelot1d := RichelotOnKummerMap(splitting1d);
    
    // Compute the local triples (ignore global triples). The local points are the first element in the triple.
    local_triples_1mod2, global_triples_1mod2, _, local_triples_2mod1, global_triples_2mod1, _ :=
        GenerateLocalPointsRichelot(splitting1, p :
            global_points := global_points1, global_pointsd := global_points2);
    local_triples_2mod3, global_triples_2mod3, _, local_triples_3mod2, global_triples_3mod2, _ :=
        GenerateLocalPointsRichelot(splitting2, p :
            global_points := global_points2, global_pointsd := global_points3);

    // Compute the local generators
    local_gens_1mod2 := [trip[1] : trip in local_triples_1mod2];
    local_gens_2mod1 := [trip[1] : trip in local_triples_2mod1];
    local_gens_2mod3 := [trip[1] : trip in local_triples_2mod3];
    local_gens_3mod2 := [trip[1] : trip in local_triples_3mod2];

    richelot2_p := LocalRichelotOnKummerMap(splitting2, p);
    local_gens_3mod1 := GenerateFourFourFromRichelot(richelot2_p, local_gens_2mod1, local_gens_3mod2);

    richelot1d_p := LocalRichelotOnKummerMap(splitting1d, p);
    local_gens_1mod3 := GenerateFourFourFromRichelot(richelot1d_p, local_gens_2mod3, local_gens_1mod2);

    // Compute the global generators
    global_gens_1mod2 := [trip[1] : trip in global_triples_1mod2];
    global_gens_2mod1 := [trip[1] : trip in global_triples_2mod1];
    global_gens_2mod3 := [trip[1] : trip in global_triples_2mod3];
    global_gens_3mod2 := [trip[1] : trip in global_triples_3mod2];

    richelot2 := RichelotOnKummerMap(splitting2);
    global_gens_3mod1 := GenerateFourFourFromRichelot(richelot2, global_gens_2mod1, global_gens_3mod2);

    richelot1d := RichelotOnKummerMap(splitting1d);
    global_gens_1mod3 := GenerateFourFourFromRichelot(richelot1d, global_gens_2mod3, global_gens_1mod2);

    return local_gens_1mod3, global_gens_1mod3, local_gens_3mod1, global_gens_3mod1;
end intrinsic;


intrinsic GenerateFourFourLocalTriples(splitting1::SeqEnum, splitting2::SeqEnum,
    p::RngIntElt :
    global_points1 := [], global_points2 := [], global_points3 := []) -> SeqEnum, SeqEnum
    { Generate the local points for J / psid Jd and Jd / psi J, where psi is the
    (4, 4)-isogeny psi = phi2 phi1.
    splitting1 is the Richelot splitting for the first Richelot and splitting2
    is the Richelot splitting for the second Richelot. }
    // Let the Jacobians be J, J2, J3, where the Richelot isogenies are phi1: J
    // -> J2, phi2: J2 -> J3 and their duals are phi2d: J3 -> J2, phi1d: J2 ->
    // J. Let psi = phi2 phi1, psid = phi1d phi2d be the (4, 4)-isogeny.
    // We generate local points for J3 / psi J by taking generators for J3 /
    // phi2 J2 together with the images of generators for J2 / phi1 J under
    // phi2.

    splitting1d := ComputeRichelotIsogenousCurveNoDelta(splitting1);
    splitting2d := ComputeRichelotIsogenousCurveNoDelta(splitting2);

    richelot2 := RichelotOnKummerMap(splitting2);
    richelot1d := RichelotOnKummerMap(splitting1d);
    
    // Compute the local triples (ignore global triples). The local points are the first element in the triple.
    local_triples_1mod2, global_triples_1mod2, _, local_triples_2mod1, global_triples_2mod1, _ :=
        GenerateLocalPointsRichelot(splitting1, p :
            global_points := global_points1, global_pointsd := global_points2);
    local_triples_2mod3, global_triples_2mod3, _, local_triples_3mod2, global_triples_3mod2, _ :=
        GenerateLocalPointsRichelot(splitting2, p :
            global_points := global_points2, global_pointsd := global_points3);

    // Compute the local generators
    local_gens_1mod2 := [trip[1] : trip in local_triples_1mod2];
    local_gens_2mod1 := [trip[1] : trip in local_triples_2mod1];
    local_gens_2mod3 := [trip[1] : trip in local_triples_2mod3];
    local_gens_3mod2 := [trip[1] : trip in local_triples_3mod2];

    richelot2_p := LocalRichelotOnKummerMap(splitting2, p);
    local_gens_3mod1 := GenerateFourFourFromRichelot(richelot2_p, local_gens_2mod1, local_gens_3mod2);

    richelot1d_p := LocalRichelotOnKummerMap(splitting1d, p);
    local_gens_1mod3 := GenerateFourFourFromRichelot(richelot1d_p, local_gens_2mod3, local_gens_1mod2);

    // Compute the global generators
    global_gens_1mod2 := [trip[1] : trip in global_triples_1mod2];
    global_gens_2mod1 := [trip[1] : trip in global_triples_2mod1];
    global_gens_2mod3 := [trip[1] : trip in global_triples_2mod3];
    global_gens_3mod2 := [trip[1] : trip in global_triples_3mod2];

    richelot2 := RichelotOnKummerMap(splitting2);
    global_gens_3mod1 := GenerateFourFourFromRichelot(richelot2, global_gens_2mod1, global_gens_3mod2);

    richelot1d := RichelotOnKummerMap(splitting1d);
    global_gens_1mod3 := GenerateFourFourFromRichelot(richelot1d, global_gens_2mod3, global_gens_1mod2);

    return local_gens_1mod3, global_gens_1mod3, local_gens_3mod1, global_gens_3mod1;
end intrinsic;


intrinsic LiftToJacobianOverExtension(kum_points::SeqEnum) -> SeqEnum, Fld
{ Returns the lifts of the Kummer points to the Jacobian over the minimum extension possible,
as well as the field required. }
    if #kum_points eq 0 then
        return [], RationalsAsNumberField();
    end if;
    Kum := Universe(kum_points);
    f := HyperellipticCurve(Kum);
    big_field := BaseRing(f);
    if Type(big_field) eq FldRat then
        big_field := RationalsAsNumberField();
    end if;
    J := Jacobian(Kum);
    lifts := [];
    for kum_point in kum_points do
        jac_point := LiftToJacobianOverExtension(kum_point, f)[1];
        field := FieldOfDefinition(jac_point);
        if Type(field) eq FldRat then
            field := RationalsAsNumberField();
        end if;

        big_field := Compositum(big_field, field);
        J := BaseChange(J, big_field);
        lifts := [ChangeRing(pt, J) : pt in lifts];
        Append(~lifts, ChangeRing(jac_point, J));
    end for;
    return lifts, big_field;
end intrinsic;


intrinsic GenerateFourFourRealPoints(splitting1::SeqEnum, splitting2::SeqEnum)
-> SeqEnum, SeqEnum, SeqEnum
{Generate the local points for J / psid Jd and Jd / psi J, where psi is the
(4, 4)-isogeny psi = phi2 phi1. \\

Parameters - splitting1 is the Richelot splitting for the first Richelot \\
- splitting2 is the Richelot splitting for the second Richelot. \\

We return points on the Jacobian over the smallest field containing all the points. }
    triples_1mod2, triples_2mod1 := GenerateLocalPointsRichelotAtInfinity(splitting1);
    triples_2mod3, triples_3mod2 := GenerateLocalPointsRichelotAtInfinity(splitting2);

    richelot1d := DualRichelotOnKummerMap(splitting1);
    richelot2 := RichelotOnKummerMap(splitting2);

    gens_1mod3 := [trip[1] : trip in triples_1mod2] cat [richelot1d(trip[1]) : trip in triples_2mod3];
    gens_3mod1 := [trip[1] : trip in triples_3mod2] cat [richelot2(trip[1]) : trip in triples_2mod1];

    lifts_1mod3, field_1mod3 := LiftToJacobianOverExtension(gens_1mod3);
    lifts_3mod1, field_3mod1 := LiftToJacobianOverExtension(gens_3mod1);
    return lifts_1mod3, lifts_3mod1, field_1mod3, field_3mod1;
end intrinsic;


intrinsic ComputeQuadraticsDividingF(f::RngUPolElt) -> { }
    { Returns all monic quadratics that divide f over the base field. }
    factors := Factorisation(f);

    // First add all the degree 2 factors to quadratics
    quadratics := [factor[1] : factor in factors | Degree(factor[1]) eq 2];

    // Now add all products of linear factors
    linear_factors := [factor[1] : factor in factors | Degree(factor[1]) eq 1];
    for i in [1..#linear_factors] do
        for j in [i+1..#linear_factors] do
            Append(~quadratics, linear_factors[i] * linear_factors[j]);
        end for;
    end for;
    
    // Normalise the quadratics.
    quadratics := [quadratic / LeadingCoefficient(quadratic) : quadratic in
        quadratics];
    return quadratics;
end intrinsic;


intrinsic ComputeFullFourTorsion(f::RngUPolElt) -> { }
    { Let J be the Jacobian of the hyperelliptic curve y^2 = f(x). This function
    computes the four torsion subgroup J[4] over the algebraic closure of the
    base field. This function assumes that f admits a Richelot isogeny. }

    // First get all the quadratics dividing f. These are the q such that <q, 0,
    // 2> is a 2-torsion point on the Jacobian.
    two_torsion_x_polys := ComputeQuadraticsDividingF(f);
    // If deg f = 5, then <l, 0, 1> is also a 2-torsion point, where l is
    // linear.
    if Degree(f) eq 5 then
        two_torsion_x_polys cat:= [factor[1] : factor in Factorisation(f)];
    end if;

    four_torsion := [* *];
    for x_poly in two_torsion_x_polys do
        four_torsion cat:= [* ComputeFourTorsionAboveTwoTorsion(f, x_poly)[1] *];
    end for;

    return four_torsion;
end intrinsic;


intrinsic SubgroupGeneratedBy(Ds::SeqEnum, m::RngIntElt) -> SeqEnum, SeqEnum
    { Computes the subgroup generated by Ds. Assumes that m is the exponent of
    the subgroup, i.e. m * D = 0 for all D in Ds. Returns subgroup, gens. }
    gens := [];
    J := Universe(Ds);
    generated := {J!0};
    for D in Ds do
        if not D in generated then
            Append(~gens, D);
            generated := {i * D + E : i in [0..m-1], E in generated};
        end if;
    end for;
    return [D : D in generated], gens;
end intrinsic;


intrinsic ComputeFullFourTorsionOneField(f::RngUPolElt) -> Set
    { Computes the full four torsion subgroup of the Jacobian of y^2 = f(x) over
    the field of definition of all 4-torsion points. }

    J := Jacobian(HyperellipticCurve(f));
    four_torsion_divisors := ComputeFullFourTorsion(f);
    big_field := RationalsAsNumberField();
    four_torsion := [];

    // Order by increasing degree of field of definition.
    four_torsion_divisors := SortBy(four_torsion_divisors,
        [Degree(FieldOfDefinition(D)) : D in four_torsion_divisors]);

    for D in four_torsion_divisors do
        field := FieldOfDefinition(D);
        big_field := Compositum(big_field, field);
        Jfield := BaseChange(J, big_field);

        // Update the four torsion divisors so far.
        four_torsion := [ChangeRing(E, Jfield) : E in four_torsion];
        Append(~four_torsion, ChangeRing(D, Jfield));
        subgp, gens := SubgroupGeneratedBy(four_torsion, 4);
        if #subgp eq 256 then
            return subgp, gens;
        end if;
    end for;
    assert #subgp eq 256;
    return subgp, gens;
end intrinsic;


intrinsic ComputeFourTorsionAboveTwoTorsion(f::RngUPolElt, q::RngUPolElt)
    -> JacHypPt
    { Given a quadratic or linear polynomial q defining the 2-torsion point T = <q,
    0, deg q> on the Jacobian of y^2 = f(x), returns a 4-torsion point D such
    that 2 D = T. }

    K := BaseRing(f);
    C := HyperellipticCurve(f);
    J := Jacobian(C);
    T := elt<J | q, 0>;
    assert 2 * T eq J!0;

    test, h := IsDivisibleBy(f, q);
    assert test;
    WT := ComputeAdditionByTwoTorsionOnKummer(q, h);

    cT := (WT^2)[1][1];
    KcT := QuadraticExtension(K, cT);

    eigenspaces, eigenvalues := ComputeEigenspaces(ChangeRing(WT, KcT));

    kum_points := [* *];
    kum_points cat:= ComputeLinearCombinationsOnTheKummer(eigenspaces[1], f);
    kum_points cat:= ComputeLinearCombinationsOnTheKummer(eigenspaces[2], f);

    // Now lift the Kummer points to the Jacobian.
    jac_points := [* *];
    for kum_point in kum_points do
        jac_point_set :=
            LiftToJacobianOverExtension([kum_point[i][1] : i in [1..4]], f);
        jac_points cat:= [* pt : pt in jac_point_set *];
    end for;

    return jac_points;
end intrinsic;


intrinsic ComputeFourTorsionFunction(D::JacHypPt) -> RngUPolElt, RngUPolElt,
    RngElt
    { Compute the function F such that div F = 4D, where D is a 4-torsion
    divisor. D should be a point on the Jacobian of a curve. Returns: H, t,
    lambda such that F = (y - H)^2 / t satisfies div(F) = 4D. Here <t, 0> is the
    2-torsion point 2 * D. In particular, H^2 - f = lambda * a^2 * t, where D is
    the divisor <a, b>. }

    J := Parent(D);
    C := Curve(J);
    K := BaseRing(C);
    f := HyperellipticPolynomials(C);

    a := D[1];
    b := D[2];
    t := (2*D)[1];
    assert (2*D)[2] eq 0;
    assert 4*D eq J!0;

    if Degree(a) eq 1 then
        return ComputeFourTorsionFunctionDegreeOne(D);
    end if;
    assert Degree(a) eq 2;

    // First compute the multiplicative inverse of b modulo a.
    b_inv := InverseMod(b, a^2);
    H := (b + b_inv * f) / 2 mod a^2;
    check, quo := IsDivisibleBy(H^2 - f, a^2);
    assert check;
    assert quo / LeadingCoefficient(quo) eq t / LeadingCoefficient(t);
    
    // Check the original method agrees:
    c := (b_inv / 2) * ((f - b^2) div a);
    c := c mod a;
    assert IsDivisibleBy(H - (b + c * a), a^2);
    check, quo2 := IsDivisibleBy((b+c*a)^2 - f, a^2);

    divisor := elt<J | quo, H>;

    s := (H^2 - f) div a^2;
    assert NormalisePolynomial(s) eq NormalisePolynomial(t);
    check, lambda := IsDivisibleBy(s, t);
    assert Degree(lambda) eq 0;

    assert H^2 - f eq lambda * a^2 * t;

    return H, t, lambda;
end intrinsic;


intrinsic ComputeFourTorsionFunctionDegreeOne(D::JacHypPt) -> RngMPolElt,
    RngMPolElt, RngUPolElt, RngUPolElt
    { Computes the functions H and t such that (y-H)^2 / t has divisor 4 * D. }

    J := Parent(D);
    C := Curve(J);
    K := BaseRing(C);
    f := HyperellipticPolynomials(C);
    P<x> := Parent(f);

    a := D[1];
    b := D[2];
    t := (2*D)[1];
    assert (2*D)[2] eq 0;
    assert 4*D eq J!0;

    assert Degree(a) eq 1;

    // Change variables to a degree 5 curve. Hopefully this can be done.
    assert #Roots(f) gt 0;
    alpha := Roots(f)[1][1];

    f1 := Evaluate(f, x + alpha);
    f2 := HyperellipticFlipMap(f1, 6);
    assert Degree(f2) eq 5;
    
    a2 := HyperellipticFlipMap(Evaluate(a, x + alpha), 2);
    b2 := HyperellipticFlipMap(Evaluate(b, x + alpha), 3);

    J2 := Jacobian(HyperellipticCurve(f2));
    D2 := elt<J2 | a2, b2>;
    assert 4*D2 eq J2!0;

    H2, t2, lambda := ComputeFourTorsionFunction(D2);

    H := Evaluate(HyperellipticFlipMap(H2, 3), x - alpha);
    t := Evaluate(HyperellipticFlipMap(t2, 2), x - alpha);
    t := NormalisePolynomial(t);

    _, lambda := IsDivisibleBy(H^2 - f, a^2 * t);
    assert Degree(lambda) eq 0;
    assert (H^2 - f - lambda * a^2 * t) eq 0;
    return H, t, lambda;
end intrinsic;


intrinsic FourFourKernels(splitting::SeqEnum) -> SeqEnum, SeqEnum, SeqEnum
    { Computes the Kummer points of all (4, 4)-kernels on the Jacobian of y^2 =
    f(x) where f(x) = G1 * G2 * G3, where splitting = [G1, G2, G3]. Also returns
    the indices of the 4-torsion points generating the kernels and the sequence
    of 4-torsion points. }
    
    f := Product(splitting);
    four_torsion := FourTorsionOnTheKummer(f);
    return FourFourKernels(splitting, four_torsion);
end intrinsic;


intrinsic FourFourKernels(splitting::SeqEnum, four_torsion::SeqEnum) -> SeqEnum,
    SeqEnum
    { Computes the Kummer points of all (4, 4)-kernels on the Jacobian of y^2 =
    f(x), where f(x) = G1 * G2 * G3, where splitting = [G1, G2, G3]. This takes
    in the already computed 4-torsion, which should be a sequence with elements
    length 4 sequences, representing Kummer coordinates on y^2 = f(x).
    Returns a sequence of pairs of Kummer points such that the points on the
    Jacobian lying above them generate a (4, 4)-kernel. Also returns the
    sequence of pairs of indices, such that if [i, j] is an element then the
    corresponding kernel is [four_torsion[i], four_torsion[j]], where P are the
    Kummer 4-torsion points. }

    f := Product(splitting);
    Kum1 := KummerSurface(f);

    T1 := TwoTorsionOnKummer(splitting[1], f);
    T2 := TwoTorsionOnKummer(splitting[2], f);

    richelot_map := RichelotOnKummerMap(splitting);

    imgs := [LiftToJacobian(richelot_map(pt))[1] : pt in four_torsion];

    possible_ij := [[i, j] : i, j in [1..#four_torsion] | i ne j and imgs[i] ne
        imgs[j] and TwoWeilPairing(imgs[i], imgs[j]) eq 1];
    possible_ij := [ij : ij in possible_ij | Double(Kum1!four_torsion[i]) eq T1
        and Double(Kum1!four_torsion[j]) eq T2 where i is ij[1] where j is ij[2]];
    kernels := [[Kum1!four_torsion[ij[1]], Kum1!four_torsion[ij[2]]] : ij in
        possible_ij];

    return kernels, possible_ij, four_torsion;
end intrinsic;


intrinsic FourFourKernelsRational(splitting::SeqEnum) -> SeqEnum
    { Computes the (4, 4)-kernels on the Kummer such that the points lift to the
    Jacobian. }

    kernels, possible_ij, four_torsion := FourFourKernels(splitting);
    return [kernel : kernel in kernels | #LiftToJacobian(kernel[1]) gt 0 and
        #LiftToJacobian(kernel[2]) gt 0];
end intrinsic;


intrinsic FourFourCasselsMapComponent(D::JacHypPt) -> Map
    { Let D be a 4-torsion divisor on the Jacobian J. This function computes a
    map from J to K, where K is the field of definition of D. }

    J := Parent(D);
    K := CoefficientRing(J);
    assert K eq Rationals();
    f := HyperellipticPolynomials(Curve(J));

    H, t, _ := ComputeFourTorsionFunction(D);

    // Computes the image of infinity+ + infinity-.
    ftilde := HyperellipticFlipMap(f, 6);
    Htilde := HyperellipticFlipMap(H, 3);
    ttilde := HyperellipticFlipMap(t, 2);
    image_at_infinity := Evaluate((ftilde - Htilde^2)^2, 0) / Evaluate(ttilde^2, 0);
    assert image_at_infinity ne 0;
    
    cassels_image := function(jac_point)
        assert jac_point in J;
        a := jac_point[1];
        b := jac_point[2];

        if jac_point eq J!0 then
            return 1;
        end if;

        // TODO: Deal with more general points.
        assert Degree(a) eq 2;

        num := EvaluatePolynomialAtRootsOfOtherPolynomial((b - H)^2, a);
        denom := EvaluatePolynomialAtRootsOfOtherPolynomial(t, a);
        result := num / denom / image_at_infinity;
        assert result ne 0;
        return result;
    end function;

    cassels := map<J->K | x :-> cassels_image(x)>;
    return cassels;
end intrinsic;


intrinsic FourFourCasselsMap(D1::JacHypPt, D2::JacHypPt) -> Map
{ Computes the Cassels map for the (4, 4)-isogeny by D1, D2, where D1, D2 are
points on the Jacobian generating the (4, 4)-kernel. }

    J := Parent(D1);
    assert Parent(D2) eq J;
    K := CoefficientRing(J);

    pair := car<K, K>;
    cassels1 := FourFourCasselsMapComponent(D1);
    cassels2 := FourFourCasselsMapComponent(D2);

    cassels_image := function(jac_pt)
        return pair!<cassels1(jac_pt), cassels2(jac_pt)>;
    end function;

    cassels := map<J->pair | x :-> cassels_image(x)>;

    return cassels;
end intrinsic;


intrinsic LocalFourFourCasselsMapComponent(D::JacHypPt, p::RngIntElt : precision := 100) -> Map
{ Let D be a 4-torsion divisor on the Jacobian J (over Q). This function computes
a map from J_p (over Qp) to Qp. }

    J := Parent(D);
    K := CoefficientRing(J);
    assert K eq Rationals();
    f := HyperellipticPolynomials(Curve(J));

    H, t, _ := ComputeFourTorsionFunction(D);

    Qp := pAdicField(p, precision);

    J_p := BaseChange(J, Qp);

    H_p := ChangeRing(H, Qp);
    t_p := ChangeRing(t, Qp);
    f_p := ChangeRing(f, Qp);

    // Computes the image of infinity+ + infinity-.
    ftilde := HyperellipticFlipMap(f_p, 6);
    Htilde := HyperellipticFlipMap(H_p, 3);
    ttilde := HyperellipticFlipMap(t_p, 2);
    image_at_infinity := Evaluate((ftilde - Htilde^2)^2, 0) / Evaluate(ttilde^2, 0);
    assert image_at_infinity ne 0;
    
    cassels_image := function(jac_point)
        a := jac_point[1];
        b := jac_point[2];

        if jac_point eq J_p!0 then
            return 1;
        end if;

        // TODO: Deal with more general points.
        assert Degree(a) eq 2;

        num := EvaluatePolynomialAtRootsOfOtherPolynomial((b - H)^2, a);
        denom := EvaluatePolynomialAtRootsOfOtherPolynomial(t, a);
        return num / denom / image_at_infinity;
    end function;

    cassels := map<J_p->Qp | x :-> cassels_image(x)>;
    return cassels;
end intrinsic;


intrinsic LocalFourFourCasselsMap(D1::JacHypPt, D2::JacHypPt, p::RngIntElt : precision := 100) -> Map
{ Computes the Cassels map for the (4, 4)-isogeny with kernel generated by D1, D2. Currently
require D1, D2 to be defined over Q. We first localise them and return a map from the
Jacobian over Qp to the correct local fields. }

    J := Parent(D1);
    assert Parent(D2) eq J;
    assert CoefficientRing(J) eq Rationals();

    precision := 100;
    Qp := pAdicField(p, precision);

    J_p := BaseChange(J, Qp);

    pair := car<Qp, Qp>;

    cassels1 := LocalFourFourCasselsMapComponent(D1, p : precision := precision);
    cassels2 := LocalFourFourCasselsMapComponent(D2, p : precision := precision);
    cassels_image := function(jac_pt)
        return pair!<cassels1(jac_pt), cassels2(jac_pt)>;
    end function;

    cassels := map<J_p->pair | x :-> cassels_image(x)>;
    return cassels;
end intrinsic;


intrinsic FourFourCasselsMapComponentAtInfinity(D::JacHypPt, field::FldNum) -> Map
{ Let D be a 4-torsion divisor on the Jacobian J. This function computes a
map from Kum to <-1> x <-1> contained in RR^* / RR^*4, where Kum is the Kummer
surface of J. We assume all points that we evaluate the map on are defined over field.}

    J := Parent(D);
    K := CoefficientRing(J);
    assert K eq Rationals();
    f := HyperellipticPolynomials(Curve(J));

    H, t, _ := ComputeFourTorsionFunction(D);

    // Computes the image of infinity+ + infinity-.
    ftilde := HyperellipticFlipMap(f, 6);
    Htilde := HyperellipticFlipMap(H, 3);
    ttilde := HyperellipticFlipMap(t, 2);
    image_at_infinity := Evaluate((ftilde - Htilde^2)^2, 0) / Evaluate(ttilde^2, 0);
    assert image_at_infinity ne 0;

    assert IsTotallyReal(field);
    Jfield := BaseChange(J, field);
    
    cassels_image := function(jac_point)
        assert jac_point in Jfield;
        jac_points := ChangeRing(jac_point, Jfield);
        a := jac_point[1];
        b := jac_point[2];

        if jac_point eq Jfield!0 then
            return 1;
        end if;

        // TODO: Deal with more general points.
        assert Degree(a) eq 2;

        num := EvaluatePolynomialAtRootsOfOtherPolynomial((b - H)^2, a);
        denom := EvaluatePolynomialAtRootsOfOtherPolynomial(t, a);
        result := num / denom / image_at_infinity;
        assert result ne 0;

        // Choose an embedding into RR.
        places := RealPlaces(field);

        signs := [Sign(Evaluate(result, place)) : place in places];

        // TODO: Do this more consistently -- currently just hope all signs are the same if we have a choice of places.
        assert #Set(signs) eq 1;
        return signs[1];
    end function;

    cassels := map<Jfield->Rationals() | x :-> cassels_image(x)>;
    return cassels;
end intrinsic;


intrinsic FourFourCasselsMapAtInfinity(D1::JacHypPt, D2::JacHypPt, field::FldNum) -> Map
{ Computes the (4, 4)-Cassels map for the real place. We assume that all points we want
to evaluate the map on are defined over field. }
    J := Parent(D1);
    assert Parent(D2) eq J;
    K := CoefficientRing(J);

    Kum := KummerSurface(J);

    pair := car<Rationals(), Rationals()>;

    cassels1 := FourFourCasselsMapComponentAtInfinity(D1, field);
    cassels2 := FourFourCasselsMapComponentAtInfinity(D2, field);

    cassels_image := function(kum_pt)
        return pair!<cassels1(kum_pt), cassels2(kum_pt)>;
    end function;

    Jfield := BaseChange(J, field);

    cassels := map<Jfield->pair | x :-> cassels_image(x)>;

    return cassels;
end intrinsic;


intrinsic IsKummerPointReal(kum_pt::SrfKumPt) -> BoolElt
{ Returns whether or not the Kummer point lifts to a point on the Jacobian over the real numbers. }
    a92 := Computea9Squared(kum_pt);
    if a92 lt 0 then
        return false;
    elif a92 gt 0 then
        return true;
    end if;
    // If a92 equals zero then we lift the Kummer point to the Jacobian over a quadratic extension and
    // check if the quadratic extension is real.
    f := HyperellipticCurve(Parent(kum_pt));
    lift := LiftToJacobianOverExtension(kum_pt, f)[1];
    return IsTotallyReal(BaseRing(Parent(lift)));
end intrinsic;


intrinsic RichelotCasselsMapAtInfinity(splitting : ReplaceComponents := false) -> Map
{ Let Kum be the Kummer surface of y^2 = f(x), where splitting is a Richelot splitting of f(x).

Returns a map from Kum to the Cartesian product K x K. Only well-defined for points on Kum that
lift to real points on the Jacobian. }
    richelot_cassels := RichelotCasselsMapKummers(splitting : ReplaceComponents := ReplaceComponents);

    f := Product(splitting);
    J := Jacobian(HyperellipticCurve(f));
    Kum := KummerSurface(J);

    K := BaseRing(Parent(f));

    if ReplaceComponents then
        codomain := car<K, K>;
    else
        codomain := car<K, K, K>;
    end if;

    richelot_image := function(kum_pt)
        assert kum_pt in Kum;
        // Check the point lifts to the Jacobian over the real numbers
        assert IsKummerPointReal(kum_pt);

        image := richelot_cassels(kum_pt);
        if ReplaceComponents then
            return codomain!<Sign(K!image[1]), Sign(K!image[2])>;
        end if;
        return codomain!<Sign(K!image[1]), Sign(K!image[2]), Sign(K!image[3])>;
    end function;

    return map<Kum->codomain | x :-> richelot_image(x)>;
end intrinsic;


intrinsic BadPrimesFourFour(splitting1::SeqEnum, splitting2::SeqEnum) -> SeqEnum
{ Computes the bad primes for the four four isogeny. }
    bad_primes1 := BadPrimesRichelot(splitting1);
    bad_primes2 := BadPrimesRichelot(splitting2);
    return Sort(SetToSequence(Set(bad_primes1) join Set(bad_primes2)));
end intrinsic;


intrinsic FactorisationRationals(x::FldRatElt) -> SeqEnum
{ Returns the factorisation of the rational number, with possibly negative exponents. }
    num := Numerator(x);
    den := Denominator(x);
    factors := Factorisation(num);
    factors cat:= [<factor[1], -factor[2]> : factor in Factorisation(den)];
    compare := function(factor1, factor2)
        if factor1[1] eq factor2[1] then
            return 0;
        end if;
        return factor1[1] lt factor2[1] select -1 else 1;
    end function;
    Sort(~factors, compare);
    return factors;
end intrinsic;


intrinsic MultiplyTuples(tup1::Tup, tup2::Tup) -> Tup
{ Multiply the two tuples elementwise. }
    par := Parent(tup1);
    assert Parent(tup2) eq par;
    return par!<tup1[i] * tup2[i] : i in [1..#tup1]>;
end intrinsic;


intrinsic FourFourFamilyRationalKernelBadPrimes(abc::SeqEnum) -> SeqEnum
{ Returns the bad primes for the curve in our family corresponding to a, b, c. }
    splitting1 := FourFourFamilyRationalKernel(abc[1], abc[2], abc[3]);
    four_four_kernel := FourFourKernelsRational(splitting1)[1];
    splitting2 := FourFourSecondRichelot(four_four_kernel[1], four_four_kernel[2]);

    return BadPrimesFourFour(splitting1, splitting2);
end intrinsic;


intrinsic FourFourFamilyBadPrimes(abc::SeqEnum) -> SeqEnum
{ Returns the bad primes for the curve in our family corresponding to a, b, c. }
    splitting1 := FourFourFamily(abc[1], abc[2], abc[3]);
    four_four_kernel := FourFourKernelsRational(splitting1)[1];
    splitting2 := FourFourSecondRichelot(four_four_kernel[1], four_four_kernel[2]);

    return BadPrimesFourFour(splitting1, splitting2);
end intrinsic;


intrinsic FourFourDescent(four_four_kernel::Tup) -> GrpAb, GrpAb, GrpAb
{ Runs the (4, 4)-descent. Returns the top Selmer group, image of top Selmer group in bottom Selmer group
and the bottom Selmer group. We look for when the last two groups differ. }

    // First construct splitting1 and splitting2 from the four four kernel.
    Kum1 := Parent(four_four_kernel[1]);
    J1 := Jacobian(Kum1);
    f1 := HyperellipticPolynomials(Curve(J1));
    T1 := LiftToJacobian(Double(four_four_kernel[1]))[1];
    T2 := LiftToJacobian(Double(four_four_kernel[2]))[1];
    T3 := T1 + T2;
    splitting1 := [Ti[1] : Ti in [T1, T2, T3]];
    splitting1[1] *:= LeadingCoefficient(f1);
    assert Product(splitting1) eq f1;

    splitting2 := FourFourSecondRichelot(four_four_kernel[1], four_four_kernel[2]);

    splitting2d, _ := ComputeRichelotIsogenousCurveNoDelta(splitting2);

    f1 := Product(splitting1);
    f2 := Product(splitting2);
    f3 := Product(splitting2d);

    // Check that C1 has a rational point. This means that the map Div^0 C1(K) -> J1(K) / phi1d phi2d J3(K)
    // is surjective.
    assert #Roots(f1) gt 0 or #PointsOnIntegralModelOfCurve(f1, 1000) gt 0;

    d1 := Product(FactorModSquares(Computea9Squared(four_four_kernel[1])));
    d2 := Product(FactorModSquares(Computea9Squared(four_four_kernel[2])));

    // For the rational four four kernel, we expect d1, d2 to be 1.
    assert d1 eq 1;
    assert d2 eq 1;

    K1 := QuadraticField(d1);
    K2 := QuadraticField(d2);
    Ks := car<K1, K2>;

    D1 := LiftToJacobian(four_four_kernel[1])[1];
    D2 := LiftToJacobian(four_four_kernel[2])[1];

    assert D1 in J1;
    assert D2 in J1;
    assert 2 * D1 eq elt<J1 | splitting1[1], 0, 2>;
    assert 2 * D2 eq elt<J1 | splitting1[2], 0, 2>;

    bad_primes := BadPrimesFourFour(splitting1, splitting2);
    bad_primes := Sort(bad_primes);
    print "Bad primes", bad_primes;

    // Global points
    // TODO: Use the global points to start the local point search.
    global_points1 := IndexedSetToSequence(SearchPointsOnJacobianGlobal(f1 : Bound := 10));
    global_points2 := IndexedSetToSequence(SearchPointsOnJacobianGlobal(f2 : Bound := 10));
    global_points3 := IndexedSetToSequence(SearchPointsOnJacobianGlobal(f3 : Bound := 10));

    print "Global points 1:", global_points1;
    print "Global points 2:", global_points2;
    print "Global points 3:", global_points3;

    four_cassels := FourFourCasselsMap(D1, D2);
    richelot_cassels := RichelotCasselsMap(splitting1 : ReplaceComponents := true);

    // Restrict to the global points we can compute the four four cassels map on.
    // _, global_points1 := TryToCompute(four_cassels, global_points1);
    // richelot1d := DualRichelotOnKummerMap(splitting1);
    // Kum2 := Domain(richelot1d);
    // _, global_points2 := TryToCompute(func<jac_pt | four_cassels(LiftToJacobian(richelot1d(Kum2!jac_pt))[1])>, global_points2);

    // Top global Selmer data
    four_selmer_global, four_selmer_global_map, four_As :=
        ComputeMSelmerGroupGlobal(bad_primes, 4, Ks);

    // Bottom global Selmer data
    two_selmer_global, two_selmer_global_map, two_As :=
        ComputeMSelmerGroupGlobal(bad_primes, 2, Ks);

    // Four Selmer to two Selmer map
    four_selmer_to_two_selmer_global_map := hom<four_selmer_global->two_selmer_global |
        x :-> two_selmer_global_map(x @@ four_selmer_global_map)>;

    // Check that the four four Cassels map and Richelot Cassels map are equal modulo squares.
    assert { ComputeImageInGroupUsingShifts(four_cassels * two_selmer_global_map, pt, global_points1) eq
        two_selmer_global_map(richelot_cassels(pt)) : pt in global_points1 } eq { true };

    top_selmer := four_selmer_global;
    bottom_selmer := two_selmer_global;

    for i in [1..#bad_primes] do
        p := bad_primes[i];
        print "p", p;
        print "Generating local points";
        time local_gens1mod3, global_gens1mod3, _, _ :=
            GenerateFourFourLocalPoints(splitting1, splitting2, p :
                global_points1 := global_points1, global_points2 := global_points2, global_points3 := global_points3);

        Qp := pAdicField(p, 100);
        J1_p := BaseChange(J1, Qp);
        local_points := local_gens1mod3 cat [J1_p!pt : pt in global_gens1mod3];

        // ------------- Top Selmer ------------------

        // Compute the local 4-Selmer group.
        four_selmer_local, four_selmer_local_map, _ := ComputeMSelmerGroupLocal(p, 4, four_As);

        // Compute the local Cassels map for the divisors D1, D2.
        four_four_cassels_local := LocalFourFourCasselsMap(D1, D2, p);

        // four_four_cassels_images := [four_four_cassels_local(pt) : pt in local_points];
        // local_selmer_images := [four_selmer_local_map(img) : img in four_four_cassels_images];

        local_selmer_images := [ComputeImageInGroupUsingShifts(four_four_cassels_local * four_selmer_local_map, 
            pt, local_points) : pt in local_points];

        selmer_preimage := IntersectLocalInformation(
            four_selmer_global_map, four_selmer_local_map, local_selmer_images);
        top_selmer meet:= selmer_preimage;

        print "Current top Selmer group", top_selmer;

        // ------------- Bottom Selmer ----------------

        // Compute the local 2-Selmer group.
        two_selmer_local, two_selmer_local_map, _ := ComputeMSelmerGroupLocal(p, 2, two_As);

        richelot_cassels_local :=
            LocalRichelotCasselsMap(splitting1, p : ReplaceComponents := true);

        cassels_images := [richelot_cassels_local(pt) : pt in local_points];
        local_selmer_images := [two_selmer_local_map(img) : img in cassels_images];

        // Check the image of the Richelot Cassels and four four Cassels maps are equal modulo squares.
        assert {two_selmer_local_map(richelot_cassels_local(pt)) eq
            ComputeImageInGroupUsingShifts(four_four_cassels_local * two_selmer_local_map, pt, local_points)
            : pt in local_points} eq {true};

        selmer_preimage := IntersectLocalInformation(
            two_selmer_global_map, two_selmer_local_map, local_selmer_images);
        bottom_selmer meet:= selmer_preimage;

        print "Current bottom Selmer group", bottom_selmer;

        // ------------- Top Selmer image in bottom Selmer -----------
        top_selmer_image := four_selmer_to_two_selmer_global_map(top_selmer);
        print "Image of top Selmer group in bottom Selmer group", top_selmer_image;

        // We always need to have top Selmer image contained in bottom Selmer.
        assert top_selmer_image subset bottom_selmer;
    end for;

    // TODO: Also intersect at infinity.
    real_points_1mod3, real_points_3mod1, field_1mod3 := GenerateFourFourRealPoints(splitting1, splitting2);

    four_four_cassels_infinity := FourFourCasselsMapAtInfinity(D1, D2, field_1mod3);
    richelot_cassels_infinity := RichelotCasselsMapKummers(splitting1 : ReplaceComponents := true);

    real_selmer, real_selmer_map := MSelmerGroupAtInfinity(Ks, 2);

    four_four_real_selmer_images := [ComputeImageInGroupUsingShifts(four_four_cassels_infinity * real_selmer_map,
        pt, real_points_1mod3) : pt in real_points_1mod3];
    Kum1_field := KummerSurface(Universe(real_points_1mod3));
    kummer_real_points_1mod3 := [Kum1!(Kum1_field!pt) : pt in real_points_1mod3];
    richelot_real_selmer_images := [(richelot_cassels_infinity * real_selmer_map)(pt) : pt in kummer_real_points_1mod3];

    // Intersection
    selmer_preimage := IntersectLocalInformation(
        four_selmer_global_map, real_selmer_map, four_four_real_selmer_images);
    top_selmer meet:= selmer_preimage;

    selmer_preimage := IntersectLocalInformation(
        two_selmer_global_map, real_selmer_map, richelot_real_selmer_images);
    bottom_selmer meet:= selmer_preimage;

    print "Top Selmer group";
    print top_selmer;

    print "Bottom Selmer group";
    print bottom_selmer;

    // We always have image of top Selmer group modulo squares contained in the
    // bottom Selmer group, but it can be smaller.
    top_selmer_image := four_selmer_to_two_selmer_global_map(top_selmer);
    print "Top Selmer group image";
    print top_selmer_image;

    print "Difference: ", #Generators(bottom_selmer) - #Generators(top_selmer_image);

    return top_selmer, top_selmer_image, bottom_selmer;
end intrinsic;


intrinsic FourFourDescentForRationalKernelFamily(s::RngElt, t::RngElt, v::RngElt) -> RngIntElt, GrpAb, GrpAb
{ Runs the (4, 4)-descent on the curve in the family corresponding to s, t, v. }
        
    splitting1, splitting1d := FourFourFamilyRationalKernel(s, t, v);

    four_four_kernel := FourFourKernelsRational(splitting1)[1];

    return FourFourDescent(<four_four_kernel[1], four_four_kernel[2]>);
end intrinsic;


intrinsic FourFourDescentForFamily(abc::SeqEnum) -> RngIntElt, GrpAb, GrpAb
{ Runs the (4, 4)-descent on the curve in the family corresponding to a, b, c. }
    a := abc[1];
    b := abc[2];
    c := abc[3];
    splitting1 := FourFourFamily(a, b, c);

    four_four_kernel := FourFourKernelsRational(splitting1)[1];

    return FourFourDescent(<four_four_kernel[1], four_four_kernel[2]>);
end intrinsic;


intrinsic SearchForGoodABCFourFour(bound::RngIntElt) -> SeqEnum
{ Searches for a, b, c that satisfy: c is square, (1 - c) * (a - c) is square,
and b * c * (a - b) * (a - c) is square. We then also want that the curve in the
(4, 4) family corresponding to a, b, c admits a rational kernel, i.e. that the
Kummer points lift to points on the Jacobian that generate a (4, 4)-kernel. }
    abcs := [[a, b, c^2] : a, b, c in RationalsUpToHeight(bound) |
        IsSquare((1-c^2) * (a - c^2)) and IsSquare(b * c^2 * (a - b) * (a - c^2))];

    splittings := [FourFourFamily(abc[1], abc[2], abc[3]) : abc in abcs];

    // First restrict to the abcs such that the discriminant of the curve is nonzero.
    good_indices := [i : i in [1..#abcs] |
        Product(splittings[i]) ne 0 and Discriminant(Product(splittings[i])) ne 0];

    // Now restrict to those abcs that admit a rational four four kernel.
    good_abcs := [i : i in good_indices | #FourFourKernelsRational(splittings[i]) gt 0];

    return abcs[good_abcs];
end intrinsic;
