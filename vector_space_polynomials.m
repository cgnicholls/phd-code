// This file contains functions for computing with polynomials as a vector
// space.

intrinsic VectorSpaceForPolynomials(polys::SeqEnum) -> ModTupFld, SeqEnum
    { Computes a vector space over the same field as the polynomials are defined
    with vectors for the monomials occurring in the polynomials. }
    P := Universe(polys);
    K := CoefficientRing(P);
    monomials := {};
    for poly in polys do
        monomials := monomials join Set(Monomials(poly));
    end for;
    monomials := SetToSequence(monomials);
    V := VectorSpace(K, #monomials);
    return V, monomials;
end intrinsic;


intrinsic PolynomialToVector(poly::RngElt, V::ModTupFld, monomials::SeqEnum)
    -> ModTupFldElt
    { Computes the vector corresponding to the polynomial with the given vector
    space. }
    vector := [];
    for monomial in monomials do
        vector := Append(vector, MonomialCoefficient(poly, monomial));
    end for;
    return V!vector;
end intrinsic;


intrinsic VectorToPolynomial(vector::ModTupFldElt, monomials::SeqEnum) -> RngElt
    { Computes the polynomial corresponding to the vector. }
    poly := 0;
    for i in [1..#monomials] do
        poly := poly + vector[i] * monomials[i];
    end for;
    return poly;
end intrinsic;


intrinsic LinearRelationsBetweenPolynomials(polys::SeqEnum) -> ModTupFld,
    ModTupFld, SeqEnum
    { Computes the linear relations between the given polynomials. }
    V, monomials := VectorSpaceForPolynomials(polys);
    M := Matrix([PolynomialToVector(poly, V, monomials) : poly in polys]);
    nullspace := Nullspace(M);
    return nullspace, V, monomials;
end intrinsic;


intrinsic SubspaceOfPolynomials(polys::SeqEnum, monomials::SeqEnum) ->
    ModTupFld, ModTupFld
    { Computes the subspace of the already computed vector space for the
    polynomials corresponding to the given polys. We also take in the monomials
    for the big vector space. }
    P := Universe(polys);
    K := BaseRing(P);
    V := VectorSpace(K, #monomials);
    vectors := [[MonomialCoefficient(poly, mon) : mon in monomials] : poly in polys];
    return sub<V | vectors>, V;
end intrinsic;


intrinsic DimensionOfPolynomials(polys::SeqEnum) -> RngIntElt
{ Returns the dimension of the polynomials over the vector space with basis the monomials occurring
in the polynomials. }
    V, m := VectorSpaceForPolynomials(polys);
    return Dimension(sub<V | [PolynomialToVector(poly, V, m) : poly in polys]>);
end intrinsic;


intrinsic DegreeNCombinations(polys::SeqEnum, n::RngIntElt) -> SeqEnum
    { Computes the degree n combinations of the polynomials. }
    R := Universe(polys);
    P := PolynomialRing(R, #polys);
    monomials_n := MonomialsOfDegree(P, n);
    h := hom<P->R | polys>;
    return [h(mon) : mon in monomials_n];
end intrinsic;


intrinsic MonomialsOfMaxDegree(P::RngMPol, max_degree::RngIntElt) -> SeqEnum
{ Returns the monomials in P of degree up to max_degree. }
    monomials := [];
    for d in [0..max_degree] do
        monomials cat:= SetToSequence(MonomialsOfDegree(P, d));
    end for;
    return monomials;
end intrinsic;