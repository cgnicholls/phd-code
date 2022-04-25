// import "four_four/richelotisogenyonkummer.m": compute_four_four_splittings;


intrinsic ComputeFourFourSplittings(splitting1::[ ]) -> ., { }
{ Let C be the hyperelliptic curve y^2 = G1 * G2 * G3, where splitting = [G1, G2, G3].
We compute the Richelot-isogenous curve C2 under the Richelot isogeny phi corresponding
to G1, G2, G3. We check if C2 admits a further Richelot isogeny phi2 such that ker phi2
intersect phi1(J[2]) = \{0\}.  We return all quadratic splittings of C2 such that the
composition phi2 phi1 is a (4, 4)-isogeny. \\

Returns: Richelot data for the first Richelot, as well as all cyclic splittings of C2
such that the composition of the two Richelots is (4, 4).  }

    // Compute all monic quadratic splittings of f2.
    f := Product(splitting1);
    _, Ls, f2 := ComputeRichelotIsogenousCurve(splitting1);
    splittings := ComputeQuadraticSplittings(f2);
    for splitting in splittings do
        for poly in splitting do
            assert IsMonic(poly);
        end for;
    end for;

    monic_Ls := [Li / LeadingCoefficient(Li) : Li in Ls];

    cyclic_splittings := [];
    for splitting2 in splittings do
        if #(Set(splitting2) meet Set(monic_Ls)) eq 0 then
            test, twist := IsDivisibleBy(f2, Product(splitting2));
            assert test;
            assert Degree(twist) eq 0;
            R := CoefficientRing(f2);
            twist := R!twist;
            twisted_splitting2 := [poly : poly in splitting2];
            twisted_splitting2[1] *:= twist;
            assert Product(twisted_splitting2) eq f2;

            Append(~cyclic_splittings, twisted_splitting2);
        end if;
    end for;
    return cyclic_splittings;
end intrinsic;


// intrinsic ComputeFourFourSplittingsOld(splitting1::[ ]) -> ., { }
//     { Let C be the hyperelliptic curve y^2 = G1 * G2 * G3, where splitting =
//     [G1, G2, G3]. We compute the Richelot-isogenous curve C2 under the Richelot
//     isogeny phi corresponding to G1, G2, G3. We check if C2 admits a further
//     Richelot isogeny phi2 such that ker phi2 intersect phi1(J[2]) = \{0\}.  We
//     return all quadratic splittings of C2 such that the composition phi2 phi1 is
//     a (4, 4)-isogeny.  Returns: Richelot data for the first Richelot, as well as
//     all cyclic splittings of C2 such that the composition of the two Richelots
//     is (4, 4).  }
//     _, cyclic_splittings :=
//         compute_four_four_splittings(splitting1[1], splitting1[2],
//                                      splitting1[3]);
//     twisted_cyclic_splittings := [];

//     _, _, f2 := ComputeRichelotIsogenousCurve(splitting1);

//     for splitting2 in cyclic_splittings do
//         // We have to twist one of the polys in splitting2 so that
//         // Product(splitting2) == f2.
//         test, twist := IsDivisibleBy(f2, Product(splitting2));
//         assert test;
//         assert Degree(twist) eq 0;
//         R := CoefficientRing(f2);
//         twist := R!twist;
//         twisted_splitting2 := [poly : poly in splitting2];
//         twisted_splitting2[1] *:= twist;
//         assert Product(twisted_splitting2) eq f2;

//         Append(~twisted_cyclic_splittings, twisted_splitting2);
//     end for;

//     return twisted_cyclic_splittings;
// end intrinsic;


intrinsic FourFourSecondRichelot(pt1::SrfKumPt, pt2::SrfKumPt) -> SeqEnum
    { Let pt1, pt2 be points on the same Kummer surface Kum1 that are the image
    of the 4-torsion divisors that generate the (4, 4)-kernel. This function
    returns the splitting of f2(x) corresponding to the Richelot isogeny J2 ->
    J3. }
    Kum := Parent(pt1);
    f := HyperellipticCurve(Kum);
    T1_kum := Double(pt1);
    T2_kum := Double(pt2);
    T1 := LiftToJacobian(T1_kum)[1];
    T2 := LiftToJacobian(T2_kum)[1];
    P<x> := Parent(f);
    splitting := [P!T1[1], P!T2[1]];
    Append(~splitting, f div (splitting[1] * splitting[2]));
    assert Product(splitting) eq f;
    
    _, f2 := ComputeRichelotIsogenousCurveNoDelta(splitting);
    assert Kum eq Parent(pt2);

    richelot_map := RichelotOnKummerMap(splitting);
    imgs_lifted := [LiftToJacobian(richelot_map(pt)) : pt in [pt1, pt2]];
    splitting2 := [P!imgs_lifted[1][1][1], P!imgs_lifted[2][1][1]];
    
    Append(~splitting2, f2 div (splitting2[1] * splitting2[2]));
    assert Product(splitting2) eq f2;
    return splitting2;
end intrinsic;
