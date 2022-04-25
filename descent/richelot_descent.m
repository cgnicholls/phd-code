intrinsic GenerateLocalPointsRichelot(splitting::SeqEnum, p::RngIntElt :
    global_points := [], global_pointsd := []) -> SeqEnum, SeqEnum, List, SeqEnum, SeqEnum, List
{ Computes the local Selmer groups and the images of J(Qp) / phid Jd(Qp) and
Jd(Qp) / phi J(Qp) under the Cassels maps, for the prime p. \\

Returns: local_triples, global_triples, local_selmer_map \\
local_triplesd, global_triplesd, local_selmer_mapd. \\

The triples are elements of the Cartesian product <J, Aps, m_selmer> and the triplesd are elements of <Jd, Adps, m_selmerd>.
 }

    // Computes the local Selmer groups and the images of J(Qp) / phid Jd(Qp)
    // and Jd(Qp) / phi J(Qp) under the Cassels maps.
    precision := 100;

    // Compute the equation of the curve and the isogenous curve.
    f := Product(splitting);
    splittingd, fd := ComputeRichelotIsogenousCurveNoDelta(splitting);

    // Make sure everything is defined over the rationals.
    f := ChangeRing(f, Rationals());
    fd := ChangeRing(fd, Rationals());
    C := ChangeRing(HyperellipticCurve(f), Rationals());
    J := Jacobian(HyperellipticCurve(f));
    Jd := Jacobian(HyperellipticCurve(fd));

    // Set up the fields
    As := car<FieldToAlgebra(Rationals()), FieldToAlgebra(Rationals())>;
    Ads := car<FieldToAlgebra(Rationals()), FieldToAlgebra(Rationals())>;

    // Set up the Cassels maps
    cassels_map := RichelotCasselsMap(splitting : ReplaceComponents := true);
    cassels_mapd := RichelotCasselsMap(splittingd : ReplaceComponents := true);

    As := Codomain(cassels_map);
    Ads := Codomain(cassels_mapd);

    // Compute the images of the global points under the Cassels map
    pair := car<J, As>;
    paird := car<Jd, Ads>;
    _, global_points := TryToCompute(cassels_map, global_points);
    _, global_pointsd := TryToCompute(cassels_mapd, global_pointsd);
    global_pairs := [pair!<pt, cassels_map(pt)> : pt in global_points];
    global_pairsd := [paird!<pt, cassels_mapd(pt)> : pt in global_pointsd];

    // Set up the local Cassels map
    local_cassels_map := LocalRichelotCasselsMap(splitting, p : ReplaceComponents := true);
    local_cassels_mapd := LocalRichelotCasselsMap(splittingd, p : ReplaceComponents := true);

    // Compute the expected size of the product #J(Qp)/phid Jd(Qp) * #Jd(Qp)
    // / phi J(Qp).
    expected_size := ExpectedRichelotProductSize(p);
    bound := 200;
    local_gens, local_gensd, local_selmer_map, local_selmer_mapd,
        local_triples, local_triplesd,
        global_triples, global_triplesd := ComputeLocalPoints(
            [* f, fd, 2, p, As, Ads,
                local_cassels_map, local_cassels_mapd,
                expected_size, global_pairs, global_pairsd *] :
                precision:=precision, bound:=bound
    );

    // Return the images and Selmer datas for each isogeny.
    return local_triples, global_triples, local_selmer_map,
           local_triplesd, global_triplesd, local_selmer_mapd;
end intrinsic;


intrinsic GenerateLocalPointsRichelotAtInfinity(splitting::SeqEnum : max_bound := 100) -> SeqEnum, SeqEnum
{ Generates the local points for Jd(R) / phi J(R) and J(R) / phid Jd(R). We
assume that splitting is defined over Q -- otherwise this might fail.
The product of the sizes of the resulting subgroups generated should be 4.}
    splittingd, fd := ComputeRichelotIsogenousCurveNoDelta(splitting);
    f := Product(splitting);

    Kum := KummerSurface(Jacobian(HyperellipticCurve(f)));
    Kumd := KummerSurface(Jacobian(HyperellipticCurve(fd)));

    // Now compute their images. These lie in R^* / R^*2 x R^* / R^*2, assuming
    // that splitting is defined over Q.
    P<x> := Universe(splitting);
    cassels_map := RichelotCasselsMapKummers(splitting : ReplaceComponents := true);
    cassels_mapd := RichelotCasselsMapKummers(splittingd : ReplaceComponents := true);
    As := Codomain(cassels_map);
    Ads := Codomain(cassels_mapd);

    // The Selmer groups are R*^ / R^*2 x R^* / R^*2, which is just <-1> x <-1>.
    fields := car<Rationals(), Rationals()>;
    fieldsd := car<Rationals(), Rationals()>;
    real_selmer, real_selmer_map := MSelmerGroupAtInfinity(fields, 2);
    real_selmerd, real_selmer_mapd := MSelmerGroupAtInfinity(fieldsd, 2);

    real_triple := car<Kum, As, real_selmer>;
    real_tripled := car<Kumd, Ads, real_selmerd>;

    // Search for points until we find enough.
    current_bound := 10;
    subgp := sub<real_selmer | 0>;
    subgpd := sub<real_selmerd | 0>;
    while #subgp * #subgpd lt 4 and current_bound le max_bound do
        // We now find points on the Kummer whose a9^2 is non-negative, so that
        // they lift to the Jacobian over R.
        print "Searching with bound", current_bound;
        kum_points := SearchLocalPointsOnJacobianReals(f : Bound := current_bound);
        kum_pointsd := SearchLocalPointsOnJacobianReals(fd : Bound := current_bound);

        // Compute their images in the Selmer groups.
        selmer_imgs, good_points := TryToCompute(cassels_map * real_selmer_map, [pt : pt in kum_points]);
        selmer_imgsd, good_pointsd := TryToCompute(cassels_mapd * real_selmer_mapd, [pt : pt in kum_pointsd]);

        used_indices := IndicesGeneratingSubgroup(selmer_imgs, real_selmer);
        used_indicesd := IndicesGeneratingSubgroup(selmer_imgsd, real_selmerd);

        real_triples := [<pt, cassels_map(pt), real_selmer_map(cassels_map(pt)) where pt is good_points[i]> : i in used_indices];
        real_triplesd := [<pt, cassels_mapd(pt), real_selmer_mapd(cassels_mapd(pt)) where pt is good_pointsd[i]> : i in used_indicesd];

        subgp := sub<real_selmer | [trip[3] : trip in real_triples]>;
        subgpd := sub<real_selmerd | [trip[3] : trip in real_triplesd]>;

        // Increase the bound.
        current_bound *:= 2;
        print "Currently have #subgp, #subgpd = ", #subgp, #subgpd;
    end while;

    // We expect the product of the sizes to be 4.
    if #subgp * #subgpd ne 4 then
        print "Expecting #subgp * #subgpd = 4, but we have #subgp, #subgpd = ", #subgp, #subgpd;
        assert false;
    end if;

    return real_triples, real_triplesd, real_selmer_map, real_selmer_mapd;
end intrinsic;


replace_components_richelot_cassels := function(components)
    // Compute the Richelot map for L1, L2, L3. Return only the Richelot map
    // for L1, L2, but first replace any zero entries by the product of the
    // other two entries. The product of all three entries is square, so this
    // gives the same result modulo squares. That is, we assume we are on the
    // curve y^2 = L1 * L2 * L3, and are given [L1(pt), L2(pt), L3(pt)]. Since
    // the product of these components is a square, we replace the zero
    // component with the product of the other two.
    if components[1] eq 0 then
        components[1] := components[2] * components[3];
    end if;
    if components[2] eq 0 then
        components[2] := components[1] * components[3];
    end if;
    assert components[1] ne 0;
    assert components[2] ne 0;
    return <components[1], components[2]>;
end function;


replace_components_local_richelot_cassels := function(components)
    // Compute the Richelot map for L1, L2, L3. Return only the Richelot map
    // for L1, L2, but first replace any zero entries by the product of the
    // other two entries. The product of all three entries is square, so this
    // gives the same result modulo squares. That is, we assume we are on the
    // curve y^2 = L1 * L2 * L3, and are given [L1(pt), L2(pt), L3(pt)]. Since
    // the product of these components is a square, we replace the zero
    // component with the product of the other two.
    if (components[1] eq 0) or (Precision(components[1]) eq 0) then
        components[1] := components[2] * components[3];
    end if;
    if (components[2] eq 0) or (Precision(components[2]) eq 0) then
        components[2] := components[1] * components[3];
    end if;
    assert (components[1] ne 0) and (Precision(components[1]) ne 0);
    assert (components[2] ne 0) and (Precision(components[2]) ne 0);
    return <components[1], components[2]>;
end function;


intrinsic TryToCompute(the_map::UserProgram, elements::SeqEnum : verbose := false) -> SeqEnum, SeqEnum, SeqEnum
{ Tries to compute the map on the elements. Returns the result and the elements
for which it worked and the elements for which it did not work. That is, returns
results, good_elements, bad_elements. }
    results := [];
    good_elements := [];
    error_elements := [];
    for elt in elements do
        try
            Append(~results, the_map(elt));
            Append(~good_elements, elt);
        catch e
            if verbose then
                print e;
            end if;
            Append(~error_elements, elt);
        end try;
    end for;
    return results, good_elements, error_elements;
end intrinsic;


intrinsic TryToCompute(the_map::Map, elements::SeqEnum : verbose := false) -> SeqEnum, SeqEnum, SeqEnum
{ Tries to compute the map on the elements. Returns the result and the elements
for which it worked and the elements for which it did not work. That is, returns
results, good_elements, bad_elements. }
    results := [];
    good_elements := [];
    error_elements := [];
    for elt in elements do
        try
            Append(~results, the_map(elt));
            Append(~good_elements, elt);
        catch e
            if verbose then
                print e;
            end if;
            Append(~error_elements, elt);
        end try;
    end for;
    return results, good_elements, error_elements;
end intrinsic;


intrinsic RichelotCasselsMap(splitting::SeqEnum : ReplaceComponents := false) -> Map
{ Let splitting be a splitting of the Jacobian J, and let phi: J -> Jd be the
corresponding Richelot isogeny. This function computes a map from J / phid Jd
to K x K x K, where K is the ground field of the polynomials in splitting. }
    K := BaseRing(Universe(splitting));
    A := FieldToAlgebra(K);
    J := Jacobian(HyperellipticCurve(Product(splitting)));
    Kum := KummerSurface(J);

    if ReplaceComponents then
        codomain := car<A, A>;
        cassels_map := map<J->codomain | x :-> replace_components_richelot_cassels(RichelotCasselsMapKummers(splitting, Kum!x))>;
    else
        codomain := car<A, A, A>;
        cassels_map := map<J->codomain | x :-> RichelotCasselsMapKummers(splitting, Kum!x)>;
    end if;

    return cassels_map;
end intrinsic;


intrinsic LocalRichelotCasselsMap(splitting::SeqEnum, p::RngIntElt :
    ReplaceComponents := false, precision := 100) -> Map
{ Let splitting be a splitting of the Jacobian J, and let phi: J -> Jd be the
corresponding Richelot isogeny. This function computes a map from J / phid Jd
to K x K x K, where K is the ground field of the polynomials in splitting. }

    Qp := pAdicField(p, precision);
    splitting := [ChangeRing(poly, Qp) : poly in splitting];
    f := Product(splitting);
    J_p := Jacobian(HyperellipticCurve(f));
    Kum_p := KummerSurface(J_p);

    Ap := FieldToAlgebra(Qp);
    codomain := ReplaceComponents select car<Ap, Ap> else car<Ap, Ap, Ap>;

    cassels_image := function(jac_pt)
        image := RichelotCasselsMapKummers(splitting, Kum_p!jac_pt);
        if ReplaceComponents then
            return replace_components_local_richelot_cassels(image);
        else
            return codomain!<image[i] : i in [1..3]>;
        end if;
    end function;

    cassels_map := map<J_p->codomain | x :-> cassels_image(x)>;

    return cassels_map;
end intrinsic;


intrinsic RichelotCasselsMapKummers(splitting::SeqEnum : ReplaceComponents := false) -> Map
{ }
    K := BaseRing(Universe(splitting));
    A := FieldToAlgebra(K);
    Kum := KummerSurface(Product(splitting));

    if ReplaceComponents then
        codomain := car<A, A>;
        cassels_map := map<Kum->codomain | x :-> replace_components_richelot_cassels(RichelotCasselsMapKummers(splitting, x))>;
    else
        codomain := car<A, A, A>;
        cassels_map := map<Kum->codomain | x :-> RichelotCasselsMapKummers(splitting, x)>;
    end if;
    return cassels_map;
end intrinsic;


intrinsic LocalRichelotCasselsMapKummers(splitting::SeqEnum, p::RngIntElt :
    ReplaceComponents := false, precision := 100) -> Map
{ The polynomials in splitting should be defined over the rationals. }
    Qp := pAdicField(p, precision);
    splitting := [ChangeRing(poly, Qp) : poly in splitting];
    f := Product(splitting);
    Kum_p := KummerSurface(Jacobian(HyperellipticCurve(f)));

    if ReplaceComponents then
        codomain := car<Qp, Qp>;
        cassels_map := map<Kum_p->codomain | x :->
            replace_components_richelot_cassels(RichelotCasselsMapKummers(splitting, x))>;
    else
        codomain := car<Qp, Qp, Qp>;
        cassels_map := map<Kum_p->codomain | x :-> RichelotCasselsMapKummers(splitting, x)>;
    end if;
    return cassels_map;
end intrinsic;


replace_components_triple := function(triple)
    // Finds the first zero component in a triple and replaces it with the product of the other two.
    if triple[1] eq 0 then
        return [triple[2] * triple[3], triple[2], triple[3]];
    elif triple[2] eq 0 then
        return [triple[1], triple[1] * triple[3], triple[3]];
    elif triple[3] eq 0 then
        return [triple[1], triple[2], triple[1] * triple[2]];
    else
        return triple;
    end if;
end function;


intrinsic RichelotCasselsSpecialCase(splitting::SeqEnum, roots_poly::RngUPolElt) -> Tup
{ The special case when the roots_poly has roots in common with two polynomials in splitting. }
    roots := [rt[1] : rt in Roots(roots_poly)];
    trip1 := [Evaluate(poly, roots[1]) : poly in splitting];
    trip1 := replace_components_triple(trip1);
    trip2 := [Evaluate(poly, roots[2]) : poly in splitting];
    trip2 := replace_components_triple(trip2);
    return [trip1[i] * trip2[i] : i in [1..3]];
end intrinsic;


intrinsic RichelotCasselsMapKummers(splitting::SeqEnum, kum_pt::SrfKumPt) -> Tup
{ Let splitting be a splitting of the Jacobian J, and let phi: J -> Jd be the
corresponding Richelot isogeny. This function computes the map from J / phid Jd
to K x K x K, where K is the ground field of the polynomials in splitting.
But the map takes in points on the Kummer surface. }

    Kum := Parent(kum_pt);
    K := BaseRing(Kum);
    codomain := car<K, K, K>;
    P<x> := PolynomialRing(K);
    roots_poly := kum_pt[1] * x^2 - kum_pt[2] * x + kum_pt[3];

    // The roots poly is zero when the Kummer point is the image of the identity on
    // the Jacobian. In this case the image should be 1 in all components.
    if roots_poly eq 0 then
        return codomain!< 1, 1, 1>;
    end if;
    // The roots poly is 1 for infty^+ - infty^- or infty^- - infty^+. This is because
    // it implies all points in the support of P + Q - infty^+ - infty^- are in the infinite
    // chart. So the point is either the identity or one of the two above. In this case,
    // the point is linearly equivalent to 2 * infty^+ - P - Pbar for some affine point P,
    // which implies the Cassels map evaluates to the trivial point.
    if roots_poly eq 1 then
        return codomain!<1, 1, 1>;
    end if;

    // We do something special if the Kummer point is 2-torsion. In this case, possibly two of 
    // the components evaluate to zero. This only happens if the roots poly splits, since then it
    // can have roots in common with two of the splittings.
    // TODO: Implement.
    if #[poly : poly in splitting | Degree(GCD(poly, roots_poly)) gt 0] ge 2 then
        result := RichelotCasselsSpecialCase(splitting, roots_poly);
        assert result[1] ne 0 and result[2] ne 0 and result[3] ne 0;
    else
        result := [EvaluatePolynomialAtRootsOfOtherPolynomial(poly, roots_poly) : poly in splitting];
    end if;


    // We also have to deal with points at infinity. This only occurs if the point
    // is P - infty, where the curve has odd degree. See my thesis for the explanation.
    if Degree(roots_poly) eq 1 then
        result := codomain!<result[i] * Coefficient(splitting[i], 2) : i in [1..3]>;
    end if;
    if Type(K) eq FldPad then
        return result;
    else
        return codomain!<Product(FactorModSquares(elt)) : elt in result>;
    end if;
end intrinsic;


intrinsic ExpectedRichelotProductSize(p::RngIntElt) -> RngIntElt
    { Computes the size of J(Qp) / phid Jd(Qp) * Jd(Qp) / phi J(Qp), where p is
    prime and Qp denotes the p-Adic field. Assumes that J admits a Richelot
    isogeny with kernel defined over Qp, and that Jd is the image under this
    Richelot isogeny. This is the case precisely when J is the Jacobian of y^2 =
    f(x) and f(x) is a product of three quadratics (with possibly one being
    linear). We let p = 0 denote the infinite place. }
    // Returns the size of J(Qp) / phi' J'(Qp) * J'(Qp) / phi J(Qp). It is
    // computed as J(Qp)[phi] * J'(Qp)[phi'] * |p|_2^-2, where |p|_2 is the
    // 2-adic absolute value of p. Assumes that the Richelot kernel is defined
    // over Qp (that is, that the quadratic factors defining the Richelot are
    // defined over Qp). This definitely holds if the quadratic factors are
    // defined over Q.

    if p eq 0 then
        return 4;
    end if;

    // Compute #Jd(Qp)[phid]. This has size 4, so long as the Richelot torsion
    // points are Qp-rational.
    num_JdQpphid := 4;

    // Compute #J(Qp)[phi]. This has size 4, so long as the Richelot torsion
    // points are Qp-rational.
    num_JQpphi := 4;
    
    // Compute |p|_2^-2. It's 1 unless p = 2.
    two_factor := 1;
    if p eq 2 then
        two_factor := 2^2;
    end if;

    // Multiply all the factors.
    return num_JQpphi * num_JdQpphid * two_factor;
end intrinsic;


intrinsic CheckCasselsMapIsHomomorphism(pts::SetIndx, cassels_map::Map)
    -> BoolElt
    { Checks for the given points whether the given Cassels map is a
    homomorphism. }
    return CheckCasselsMapIsHomomorphism([pt : pt in pts], cassels_map);
end intrinsic;


intrinsic CheckCasselsMapIsHomomorphism(pts::SeqEnum, cassels_map::Map)
    -> BoolElt
    { Checks for the given points whether the given Cassels map is a
    homomorphism. }
    for pt1, pt2 in pts do
        try
            img1 := cassels_map(pt1);
            img2 := cassels_map(pt2);
            img12 := cassels_map(pt1 + pt2);
            assert Min([Precision(img) : img in [img1, img2, img12]]) gt 20;
            thediff := [img1[i] * img2[i] * img12[i] : i in [1..2]];
            if false in [IsSquare(elt) : elt in thediff] then
                print "Issue with", img1, img2, img12;
                return false;
            end if;
        catch e
            print e;
        end try;
    end for;
    return true;
end intrinsic;


intrinsic BadPrimesRichelot(splitting::SeqEnum) -> SeqEnum
{ Computes the bad primes for the Richelot isogeny. }
    f := Product(splitting);
    delta := ComputeRichelotDelta(splitting);
    disc := Discriminant(f);
    result := 2 * NumeratorTimesDenominator(delta) * NumeratorTimesDenominator(disc);
    return [p[1] : p in Factorisation(result)];
end intrinsic;


intrinsic RichelotDescentLowerBound(splitting::SeqEnum) -> RngIntElt
{ Returns a lower bound for the Jacobian of y^2 = f(x), where f is the product of the polynomials in splitting.
This uses the Richelot descent. }
    f := Product(splitting);
    splittingd, fd := ComputeRichelotIsogenousCurveNoDelta(splitting);

    // Search for global points.
    global_points := SetToSequence(SearchPointsOnJacobianGlobal(f));
    global_pointsd := SetToSequence(SearchPointsOnJacobianGlobal(fd));

    bad_primes := BadPrimesRichelot(splitting);

    fields := car<Rationals(), Rationals()>;
    fieldsd := car<Rationals(), Rationals()>;

    global_selmer, global_selmer_map, As := ComputeMSelmerGroupGlobal(bad_primes, 2, fields);
    global_selmerd, global_selmer_mapd, Ads := ComputeMSelmerGroupGlobal(bad_primes, 2, fieldsd);

    // Compute the image of the found global points. And thus obtain a lower bound on #J'(K) / 2 J'(K) using
    // #J'(K) / 2J'(K) = #J'(K) / phi J(K) * #J(K) / phi' J'(K) * #J'[2](K) / (#J[phi](K) * #J'[phi'](K)).
    richelot_cassels := RichelotCasselsMap(splitting : ReplaceComponents := true);
    richelot_casselsd := RichelotCasselsMap(splittingd : ReplaceComponents := true);
    global_images := [ComputeImageInGroupUsingShifts(richelot_cassels * global_selmer_map, pt, global_points)
        : pt in global_points];
    global_imagesd := [ComputeImageInGroupUsingShifts(richelot_casselsd * global_selmer_mapd, pt, global_pointsd)
        : pt in global_pointsd];
    global_subgroup := sub<global_selmer | global_images>;
    global_subgroupd := sub<global_selmerd | global_imagesd>;

    torsion_subgroup := TorsionSubgroup(fd);
    twice_torsion_subgroup := 2 * torsion_subgroup;
    torsion_bound := #(torsion_subgroup / twice_torsion_subgroup);

    // Size of J[phi](K) and J[phid](K) are both 4.
    // Compute size of J[2](K).
    Jd := Jacobian(HyperellipticCurve(fd));
    assert BaseRing(Jd) eq Rationals();

    two_torsion_size := #TwoTorsionSubgroup(Jd);

    size_lower_bound := (#global_subgroup * #global_subgroupd * two_torsion_size) div (4 * 4);

    rank_lower_bound := ComputeRankBoundFromSelmer(2, size_lower_bound, torsion_bound);

    return rank_lower_bound;
end intrinsic;


intrinsic RichelotDescent(splitting::SeqEnum) -> RngIntElt, GrpAb, GrpAb
{ Returns rank_bound, selmer, selmerd, where r is the rank bound, selmer is the Selmer group
and selmerd is the Selmer group for phid, computed by the Richelot descent. }

    f := Product(splitting);
    splittingd, fd := ComputeRichelotIsogenousCurveNoDelta(splitting);

    // Search for global points.
    global_points := SetToSequence(SearchPointsOnJacobianGlobal(f));
    global_pointsd := SetToSequence(SearchPointsOnJacobianGlobal(fd));

    bad_primes := BadPrimesRichelot(splitting);

    fields := car<Rationals(), Rationals()>;
    fieldsd := car<Rationals(), Rationals()>;

    global_selmer, global_selmer_map, As := ComputeMSelmerGroupGlobal(bad_primes, 2, fields);
    global_selmerd, global_selmer_mapd, Ads := ComputeMSelmerGroupGlobal(bad_primes, 2, fieldsd);

    selmer := global_selmer;
    selmerd := global_selmerd;

    // Intersect at all the bad primes.
    for p in bad_primes do
        local_triples, global_triples, local_selmer_map,
            local_triplesd, global_triplesd, local_selmer_mapd :=
                GenerateLocalPointsRichelot(splitting, p :
                    global_points := global_points, global_pointsd := global_pointsd);
        local_selmer_images := [trip[3] : trip in local_triples] cat [trip[3] : trip in global_triples];
        local_selmer_imagesd := [trip[3] : trip in local_triplesd] cat [trip[3] : trip in global_triplesd];
        selmer_preimage := IntersectLocalInformation(global_selmer_map, local_selmer_map, local_selmer_images);
        selmer meet:= selmer_preimage;
        selmer_preimaged := IntersectLocalInformation(global_selmer_mapd, local_selmer_mapd, local_selmer_imagesd);
        selmerd meet:= selmer_preimaged;
    end for;

    // Also intersect at infinity.
    print "p = infinity";
    real_triples, real_triplesd, real_selmer_map, real_selmer_mapd := GenerateLocalPointsRichelotAtInfinity(splitting);
    selmer meet:= IntersectLocalInformation(global_selmer_map, real_selmer_map, [trip[3] : trip in real_triples]);
    selmerd meet:= IntersectLocalInformation(global_selmer_mapd, real_selmer_mapd, [trip[3] : trip in real_triplesd]);

    torsion_subgroup := TorsionSubgroup(fd);
    twice_torsion_subgroup := 2 * torsion_subgroup;
    torsion_bound := #(torsion_subgroup / twice_torsion_subgroup);

    // Size of J[phi](K) and J[phid](K) are both 4.
    // Compute size of J[2](K).
    Jd := Jacobian(HyperellipticCurve(fd));
    assert BaseRing(Jd) eq Rationals();

    // Use the bound #J'(K) / 2J'(K) <= #selmer * #selmerd * #J'[2](K) /
    // (#J[phi](K) * #J'[phi'](K)).
    two_torsion_size := #TwoTorsionSubgroup(Jd);
    size_upper_bound := (#selmer * #selmerd * two_torsion_size) div (4 * 4);

    // Now we have 2^r <= size_upper_bound / torsion_bound.
    rank_upper_bound := ComputeRankBoundFromSelmer(2, size_upper_bound, torsion_bound);

    // Also compute a lower bound
    rank_lower_bound := RichelotDescentLowerBound(splitting);

    return rank_lower_bound, rank_upper_bound, selmer, selmerd;
end intrinsic;


intrinsic ComputeLocalTwoTorsion(f::RngUPolElt, Qp::FldPad) -> Set
{ Computes J(Qp)[2], where J is the Jacobian of the hyperelliptic curve y^2 = f(x).
We know the 2-torsion is of the form <q(x), 0, 2> where q(x) is a quadratic factor
of f(x). }
    assert Degree(f) in [5,6];
    
    p := Prime(Qp);
    fp := ChangeRing(f, Qp);
    Jp := Jacobian(HyperellipticCurve(fp));
    factors := [factor[1] : factor in Factorisation(fp)];
    all_products := ComputeAllProducts(factors);
    points := {Jp!0};
    if Degree(f) eq 5 then
        valid_degrees := [1, 2];
    else
        valid_degrees := [2];
    end if;

    // Consider the 2-torsion points corresponding to factors of fp. We need the
    // degree of the factor to be 1 or 2, if deg f = 5, and to be 2, if deg f =
    // 6.
    for product in [product : product in all_products | Degree(product) in
        valid_degrees] do
        points_product := Points(Jp, product, Degree(product));
        points join:= {thing : thing in points_product};
    end for;
    return points;
end intrinsic;


intrinsic ComputeAllProducts(elements::SeqEnum) -> SeqEnum
{ Returns a sequence of all products of subsets of elements in elements. }
    products := {Universe(elements) | 1};
    subsets := Subsets(Set(elements));
    for subs in subsets do
        if #subs ne 0 then
            products join:= {Product([elt : elt in subs])};
        end if;
    end for;
    return [product : product in products];
end intrinsic;