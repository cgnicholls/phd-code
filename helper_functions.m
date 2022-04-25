intrinsic Product(list::[ ]) -> .
    { Computes the product of the elements in the list. }
    if #list eq 0 then
        return 1;
    end if;
    product := Universe(list)!1;
    for elt in list do
        product *:= elt;
    end for;
    return product;
end intrinsic;


intrinsic Product(elts::SetEnum) -> .
    { Computes the product of the elements in the set. }
    return Product([elt : elt in elts]);
end intrinsic;


intrinsic Product(elts::SetIndx) -> .
    { Computes the product of the elements in the set. }
    return Product([elt : elt in elts]);
end intrinsic;


intrinsic ComputeSum(elts::SeqEnum) -> .
    { Takes the sum of the elements in the sequence. }
    if #elts eq 0 then
        return 0;
    end if;
    result := Universe(elts)!0;
    for elt in elts do
        result +:= elt;
    end for;
    return result;
end intrinsic;


intrinsic Union(sets::SetIndx) -> SetIndx
    { Computes the union of a set of sets }
    the_union := {};
    for set in sets do
        the_union join:= Set(set);
    end for;
    return {@ elt: elt in the_union @};
end intrinsic;


intrinsic Union(sets::SetEnum) -> SetEnum
    { Computes the union of a set of sets }
    the_union := {};
    for set in sets do
        the_union join:= Set(set);
    end for;
    return the_union;
end intrinsic;


intrinsic Intersection(sets::SeqEnum) -> SetEnum
    { Computes the intersection of a sequence of sets }
    the_intersection := sets[1];
    for set in sets do
        the_intersection meet:= Set(set);
    end for;
    return the_intersection;
end intrinsic;


intrinsic Concatenate(seqs::SeqEnum) -> SeqEnum
    { Given a sequence 'seqs' of sequences, concatenate all the sequences. }
    if #seqs eq 0 then
        return [];
    end if;
    big_seq := [];
    for seq in seqs do
        big_seq cat:= seq;
    end for;
    return big_seq;
end intrinsic;


intrinsic ComputeTorsionPointsOnJacobian(f::RngUPolElt) -> SeqEnum
{ Computes the torsion points on the Jacobian of the curve y^2 = f(x).
f(x) can have non-integral coefficients, as we map through IntegralModel. }

    lcm := LCM([Denominator(coeff) : coeff in Coefficients(f)]);

    curve := HyperellipticCurve(f * lcm^2);

    tt, mtt := TorsionSubgroup(Jacobian(curve));
    
    points := [mtt(pt) : pt in tt];

    J := Jacobian(HyperellipticCurve(f));
    points := [elt<J | pt[1], pt[2] / lcm, pt[3]> : pt in points];
    return points;
end intrinsic;


intrinsic ComputeTorsionSubgroupOfJacobian(f::RngUPolElt) -> SeqEnum
{ Computes the torsion subgroup of the Jacobian of the curve y^2 = f(x).
f(x) can have non-integral coefficients, as we map through IntegralModel. }

    lcm := LCM([Denominator(coeff) : coeff in Coefficients(f)]);

    curve := HyperellipticCurve(f * lcm^2);

    tt, mtt := TorsionSubgroup(Jacobian(curve));
    return tt, mtt;
end intrinsic;


intrinsic IndicesGeneratingSubgroup(elts::SeqEnum, gp::GrpAb : start_with := []) -> SeqEnum
{ Given some elements of a group that generate a subgroup subgp of gp, we
return the indices required to generate that group. }
    subgp := sub<gp | start_with cat elts>;
    used_indices := [];
    for i in [1..#elts] do
        elt := elts[i];
        if not elt in sub<gp | start_with cat elts[used_indices]> then
            Append(~used_indices, i);
        end if;
        if sub<gp | start_with cat elts[used_indices]> eq subgp then
            break;
        end if;
    end for;
    return used_indices;
end intrinsic;


intrinsic ImageInSubgroup(the_map::UserProgram, elts::SetIndx, gp::GrpAb :
    start_with := []) ->
SeqEnum, SeqEnum, SeqEnum
{ Computes the image of elts under the_map in gp. Returns just the elements
we needed to use to generate the subgroup. Note that if the order of the
group is composite, then our generating set need not be minimal. \\

Parameter start_with should be a sequence of elements in gp.
We start with these elements if they are given. \\

Returns - used_elts: the elements in elts that are used to generate the image. \\

- used_imgs: the images of the used elements in the group. \\

- bad_elts: the elements the_map failed on. }
    imgs := [];
    bad_elts := [];
    good_elts := [];
    for elt in elts do
        try
            img := the_map(elt);
            Append(~imgs, img);
            Append(~good_elts, elt);
        catch e
            Append(~bad_elts, elt);
        end try;
    end for;

    used_indices := IndicesGeneratingSubgroup(imgs, gp : start_with := start_with);
    return good_elts[used_indices], imgs[used_indices], bad_elts;
end intrinsic;


intrinsic SimultaneousImagesInSubgroups(data1::., data2::.,
    max_product_size::RngIntElt) -> [ ], [ ], [ ], [ ]
    { Computes the image of elts1 under map1 in gp1 and images of elts2 under
    map2 in gp2. Returns the elements in elts that are used to generate the
    image. The number of returned elements is thus the number of generators of
    the subgroup of the image. If the size of the group is composite, we
    may return more elements. Each data consists of a map (UserProgram),
    elts (SetIndx) and a group that the map maps the elts into.
    }
    map1 := data1[1];
    elts1 := data1[2];
    gp1 := data1[3];
    map2 := data2[1];
    elts2 := data2[2];
    gp2 := data2[3];
    used_elts1 := [];
    used_imgs1 := [];
    used_elts2 := [];
    used_imgs2 := [];
    num_errors := 0;
    // Each iteration we try adding an elt1 and an elt2 and see if it increases
    // the product size.
    subgp1 := sub<gp1 | used_imgs1>;
    subgp2 := sub<gp2 | used_imgs2>;
    for i in [1..Max(#elts1, #elts2)] do
        if i le #elts1 then
            try
                elt1 := elts1[i];
                img1 := map1(elt1);
                if not img1 in sub<gp1 | used_imgs1> then
                    Append(~used_elts1, elt1);
                    Append(~used_imgs1, img1);
                end if;
            catch e
                print e;
                num_errors +:= 1;
            end try;
        end if;
        if i le #elts2 then
            try
                elt2 := elts2[i];
                img2 := map2(elt2);
                if not img2 in sub<gp2 | used_imgs2> then
                    Append(~used_elts2, elt2);
                    Append(~used_imgs2, img2);
                end if;
            catch e
                num_errors +:= 1;
            end try;
        end if;
        if #subgp1 * #subgp2 eq max_product_size then
            break;
        end if;
    end for;
    print "Num errors: ", num_errors;
    return used_elts1, used_imgs1, used_elts2, used_imgs2;
end intrinsic;


intrinsic EvaluatePolynomialAtRootsOfOtherPolynomial(
    poly::RngUPolElt, roots_poly::RngUPolElt) -> RngElt
    { Let a1, .., an be the roots of roots_poly. This function computes poly(a1)
    * .. * poly(an). }
    resultant := Resultant(roots_poly, poly);
    // resultant(roots_poly, poly) = lead_coeff(roots_poly)^degree(poly) *
    // poly(a1) * .. * poly(an).
    // Note that Magma uses the convention that Resultant(x-a, x-b) = a - b.
    return resultant / LeadingCoefficient(roots_poly)^Degree(poly);
end intrinsic;


intrinsic EvaluateSumOfPolynomialAtRootsOfOtherPolynomial(
    poly::RngUPolElt, roots_poly::RngUPolElt) -> RngElt
    { Let a1, .., an be the roots of roots_poly. This function computes poly(a1)
    + .. + poly(an). }
    P := Parent(poly);
    K := CoefficientRing(P);
    // We need as many symmetric variables as we have roots for roots_poly.
    n := Degree(roots_poly);
    Q := PolynomialRing(K, n);
    sym_poly := ComputeSum([hom<P->Q | Q.i>(poly) : i in [1..n]]);

    check, sym_poly_Q := IsSymmetric(sym_poly);
    assert check;

    si := [(-1)^i * Coefficient(roots_poly, n - i) / Coefficient(roots_poly, n)
        : i in [1..n]];
    return hom<Q->K | si>(sym_poly_Q);
end intrinsic;


intrinsic Precision(pt::JacHypPt) -> RngElt
    { Given a local point on a Jacobian of a curve, compute its precision. }
    if pt[1] ne 0 then
        precision_a := Min([Precision(elt) : elt in
                            Coefficients(pt[1])]);
    else
        precision_a := 0;
    end if;
    if pt[2] ne 0 then
        precision_b := Min([Precision(elt) : elt in
                            Coefficients(pt[2])]);
    else
        precision_b := 0;
    end if;
    return Min(precision_a, precision_b);
end intrinsic;


intrinsic Precision(elts::SeqEnum) -> RngElt
    { Returns the minimum precision of all elements in the sequence. Assumes all
    elements are from a p-adic field. }
    precision := Min([Precision(elt) : elt in elts]);
    return precision;
end intrinsic;


intrinsic Precision(pt::PtHyp) -> RngElt
    { Given a local point on a hyperelliptic curve, compute its precision. }
    precision := Precision([pt[i] : i in [1..3]]);
    return precision;
end intrinsic;


intrinsic Precision(pt::SrfKumPt) -> RngElt
    { Compute the precision of a local point on a Kummer surface. }
    precision := Precision([pt[i] : i in [1..4]]);
    return precision;
end intrinsic;


intrinsic Precision(elts::Tup) -> RngIntElt
{ Returns the minimum precision of all elements in the tuple. Assumes all elements are
from a p-adic field. }
    return Precision([e : e in elts]);
end intrinsic;


intrinsic ComputeVectorsModM(len::RngElt, m::RngElt) -> SeqEnum
    { Computes all vectors of length len modulo m. }
    vectors := [[c] : c in [0..m-1]];
    for l in [1..len-1] do
        new_vectors := [];
        for v in vectors do
            for c in [0..m-1] do
                Append(~new_vectors, v cat [c]);
            end for;
        end for;
        vectors := new_vectors;
    end for;
    return vectors;
end intrinsic;


intrinsic ComputeRelationsForVectorsModuloSquares(vecs::SeqEnum) -> SeqEnum
    { Given a sequence of vectors, computes the products of the vectors
    (computed elementwise) that are squares. For example, given [[1, 2], [4, 2]]
    returns [[0,0], [1,1]]. }
    dim := #vecs[1];
    relations := Set(ComputeVectorsModM(#vecs, 2));
    for i in [1..dim] do
        relations_i := ComputeRelationsModuloSquares([vec[i] : vec in vecs]);
        relations meet:= Set(relations_i);
    end for;
    return [relation : relation in relations];
end intrinsic;


intrinsic ComputeRelationsModuloSquares(elts::SeqEnum) -> SeqEnum
    { Given a sequence of field elements, computes the products that are
    squares. For example, given [1, 2, 3, 6] returns [[0,0,0,0], [1,0,0,0],
    [0,1,1,1], [1,1,1,1]].}
    exponents := ComputeVectorsModM(#elts, 2);
    relations := [];
    for e in exponents do
        product := Universe(elts)!1;
        for i in [1..#e] do
            product *:= elts[i]^e[i];
        end for;
        if IsSquare(product) then
            Append(~relations, e);
        end if;
    end for;
    return relations;
end intrinsic;


intrinsic BadPrimesIntegralModel(f::RngUPolElt) -> Set
    { Computes the bad primes of y^2 = f(x). We first take the integral model, though. }
    return BadPrimes(IntegralModel(HyperellipticCurve(f)));
end intrinsic;


intrinsic RandomOrder(elts::SetIndx) -> SetIndx
    { Returns the set index in a random order. }
    list := [elt : elt in elts];
    return {@ elt : elt in RandomOrder(list) @};
end intrinsic;


intrinsic Shuffle(seq::SeqEnum) -> SeqEnum
    { Returns a randomly chosen permutation of the sequence. }
    n := #seq;
    for i in [1..n] do
        // Choose a random index in [i..n]. Swap seq[i] and seq[index]. We build
        // up the sequence from the left. At iteration i, seq[1..i-1] is
        // a random subsequence.
        index := Random(i, n);

        // Swap seq[i] and seq[index].
        tmp := seq[i];
        seq[i] := seq[index];
        seq[index] := tmp;
    end for;
    return seq;
end intrinsic;


intrinsic QuadraticExtension(K::Fld, d::RngElt) -> Fld
    { Given a field, and element d of the field, return an extension of K such
    that d is square. }
    P<x> := PolynomialRing(K);
    if IsIrreducible(x^2 - d) then
        return ext<K | x^2 - d>;
    else
        return K;
    end if;
end intrinsic;


// Computes the available eigenvectors of M.
intrinsic ComputeEigenspace(M::AlgMatElt, lambda::RngElt) -> SeqEnum
    { Computes a basis for the eigenspace of M with eigenvalue lambda. Each
    element is an nx1 matrix corresponding to a column eigenvector. }

    _K := BaseRing(M);
    assert Nrows(M) eq Ncols(M);
    n := Nrows(M);
    id_n := IdentityMatrix(_K, n);

    nullspace := Nullspace(Transpose(M - lambda * id_n));
    basis := Basis(nullspace);
    eigenspace := [];
    for vec in basis do
        Append(~eigenspace, Matrix(_K, [[vec[i]] : i in [1..n]]));
    end for;
    return eigenspace;
end intrinsic;


intrinsic ComputeEigenspaces(M::AlgMatElt) -> List, SeqEnum
    { Computes the eigenvectors of M for all available eigenvalues. Returns a
    list where each element is a sequence for the basis of the eigenspace. Also
    returns the eigenvalues. }
    // First compute the eigenvalues.
    eigenvalues := Roots(CharacteristicPolynomial(M));
    eigenvalues := [rt[1] : rt in eigenvalues];

    eigenspaces := [];
    for lambda in eigenvalues do
        eigenspace := ComputeEigenspace(M, lambda);
        Append(~eigenspaces, eigenspace);
    end for;
    return eigenspaces, eigenvalues;
end intrinsic;


intrinsic ComputeDiagonalisation(M::AlgMatElt) -> AlgMatElt, AlgMatElt
    { Computes matrices U, D such that D = U^-1 * M * U is diagonal. }

    eigenspaces, eigenvectors := ComputeEigenspaces(M);
    K := CoefficientRing(M);
    n := Nrows(M);
    U := ZeroMatrix(K, n, n);
    j := 1;
    for espace in eigenspaces do
        for k in [1..#espace] do
            for i in [1..n] do
                U[i][j] := espace[k][i][1];
            end for;
            j +:= 1;
        end for;
    end for;
    return U^-1 * M * U, U;
end intrinsic;


intrinsic SimultaneousDiagonalisation(Ms::SeqEnum) -> SeqEnum, AlgMatElt
    { Simultaneously diagonalise the matrices (assuming they are diagonalisable
    with eigenvalues defined over the base field. Returns the sequence of
    diagonal matrices, together with a matrix U such that U^-1 * M_i * U = D_i
    for each i. }

    K := CoefficientRing(Ms[1]);
    n := Nrows(Ms[1]);
    Ufull := IdentityMatrix(K, n);

    for i in [1..#Ms] do
        M := Ufull^-1 * Ms[i] * Ufull;
        D, U := ComputeDiagonalisation(M);
        Ufull *:= U;
    end for;
    return [Ufull^-1 * M * Ufull : M in Ms], Ufull;
end intrinsic;


intrinsic PointsDefinedOverBaseField(J::JacHyp, points::List) -> SetIndx
    { Returns just those points that are defined on J. }
    rational_points := {};
    for pt in points do
        try
            J_pt := J!pt;
            rational_points join:= {J_pt};
        catch e
            errors := 1;
        end try;
    end for;
    return {@ pt : pt in rational_points @};
end intrinsic;


intrinsic FieldOfDefinition(elt::RngUPolElt) -> Fld
    { Computes the minimal field of definition of the elements in the list. }
    min_polys := [MinimalPolynomial(coeff) : coeff in Coefficients(elt)];
    field := SplittingField(min_polys);
    return field;
end intrinsic;


intrinsic FieldOfDefinition(elts::.) -> Fld
    { Computes the minimal field of definition of the elements in the list. }
    min_polys := [MinimalPolynomial(elt) : elt in elts];
    field := SplittingField(min_polys);
    return field;
end intrinsic;


intrinsic FieldOfDefinition(pt::JacHypPt) -> Fld
    { Computes the minimal field of definition of the elements in the list. }
    min_polys := [MinimalPolynomial(coeff) : coeff in Coefficients(pt[1])] cat
        [MinimalPolynomial(coeff) : coeff in Coefficients(pt[2])];
    field := SplittingField(min_polys);
    return field;
end intrinsic;


intrinsic ChangeRing(D::JacHypPt, J2::JacHyp) -> JacHypPt
    { Given a divisor D on a Jacobian J/K and a Jacobian J2/K2, where K2 is a
    field extension of K, return D on J2. }
    a := D[1];
    b := D[2];
    P1 := Parent(a);
    K1 := BaseRing(P1);
    K2 := BaseRing(J2);
    P2 := PolynomialRing(K2);
    check, incl := IsSubfield(K1, K2);
    assert check;
    hom12 := hom<P1->P2 | incl, P2.1>;
    return elt<J2 | hom12(a), hom12(b), Degree(a)>;
end intrinsic;


intrinsic SortBy(A::SeqEnum, B::SeqEnum) -> SeqEnum
    { Sorts A by B. }
    sorted_indices := Sort([1..#A], func<i, j | B[i] - B[j]>);
    return [A[i] : i in sorted_indices];
end intrinsic;


intrinsic SortBy(A::List, B::SeqEnum) -> List
    { Sorts A by B. }
    sorted_indices := Sort([1..#A], func<i, j | B[i] - B[j]>);
    return [* A[i] : i in sorted_indices *];
end intrinsic;


intrinsic TorsionSubgroup(f::RngUPolElt) -> GrpAb
    { Returns the torsion subgroup for the hyperelliptic curve y^2 = f(x),
    assuming deg f = 5 or 6. }
    assert Degree(f) in [5, 6];
    C := HyperellipticCurve(f);
    return TorsionSubgroup(Jacobian(IntegralModel(C)));
end intrinsic;


intrinsic RemoveMultipleFactors(poly::RngUPolElt) -> RngUPolElt
    { Factorises poly into poly1^e1 * ... * polyn^en, and only keeps the factors
    with en <= 1. }
    factors := [factor[1] : factor in Factorisation(poly) | factor[2] le 1];
    result := LeadingCoefficient(poly);
    for factor in factors do
        result *:= factor;
    end for;
    return result;
end intrinsic;


intrinsic NormalisePolynomialModuloSquares(f::RngUPolElt) -> RngUPolElt
    { Given a polynomial f(x) over the rationals, with leading coefficient a, we divide by
    the unique rational number b^2 such that c = a / b^2 is a squarefree integer. }
    num := Numerator(LeadingCoefficient(f));
    den := Denominator(LeadingCoefficient(f));
    a_num, b_num := Squarefree(num);
    a_den, b_den := Squarefree(den);

    a := a_num * a_den;
    b := b_num / b_den * a_den^2;
    f_norm := f / b^2;
    assert LeadingCoefficient(f) / LeadingCoefficient(f_norm) eq b^2;
    return f_norm;
end intrinsic;


intrinsic SliceSequence(seq::SeqEnum, start::RngIntElt, step::RngIntElt) -> SeqEnum
    { Slices the sequence, returning the subsequence of elements starting at start and
    adding step each time.}
    return seq[[start..#seq by step]];
end intrinsic;


intrinsic RationalsUpToHeight(H::RngIntElt, n::RngIntElt, specialise::SeqEnum)
    -> []
    { Returns all n-tuples of rational numbers up to height H. The variable
    specialise is a list of 2-tuples <i, x>, where we specialise the ith
    variable to be the value x. }
    rationals := RationalsUpToHeight(H);
    
    product := CartesianProduct([rationals : i in [1..n]]);
    product := [[elt[i] : i in [1..n]] : elt in product];
    return product;
end intrinsic;


intrinsic RationalsUpToHeight(H::RngIntElt, n::RngIntElt : include_zero := true, include_negatives := true) -> []
    { Returns all n-tuples of rational numbers up to height H. }
    rationals := RationalsUpToHeight(H : include_zero := include_zero, include_negatives := include_negatives);
    product := CartesianProduct([rationals : i in [1..n]]);
    product := [[elt[i] : i in [1..n]] : elt in product];
    return product;
end intrinsic;


intrinsic RationalsUpToHeight(H::RngIntElt : include_zero := true, include_negatives := true) -> []
    { Returns all rational numbers up to height H. }

    farey := [t : t in FareySequence(H) | t ne 0];
    inv_farey := Reverse([1/t : t in farey | t ne 0 and t ne 1]);
    rationals := farey cat inv_farey;
    if include_negatives then
        rationals := [e * t : e in [1, -1], t in rationals];
    end if;
    if include_zero then
        rationals := [0] cat rationals;
    end if;
    return rationals;
end intrinsic;


intrinsic RationalsUpToHeightOld(H::RngIntElt) -> []
    { Returns all rational numbers up to height H. }

    return [0] cat [e * a/b : a in [1..H], b in [1..H], e in [1, -1] | GCD(a, b)
        eq 1];
end intrinsic;


intrinsic HomogeneousDiscriminant(poly::RngMPolElt) -> RngElt
    { Computes the discriminant of a homogeneous polynomial in two variables. }
    P<x,y> := Parent(poly);
    K := BaseRing(P);
    Pt<t> := PolynomialRing(K);
    assert Rank(P) eq 2;
    return Discriminant(hom<P->Pt | t, 1>(poly));
end intrinsic;


intrinsic NumeratorTimesDenominator(elt::RngElt) -> RngElt
    { Returns numerator times denominator for a given element. }
    return NumeratorTimesDenominator(elt / 1);
end intrinsic;


intrinsic NumeratorTimesDenominator(elt::FldElt) -> RngElt
    { Returns numerator times denominator for a given field element. }
    K := Parent(elt);
    R := Integers(K);
    num := Numerator(elt);
    den := Denominator(elt);

    if elt eq 0 then
        return 0;
    end if;
    
    constant := elt / (num/den);
    return R!(constant * num * den);
end intrinsic;


intrinsic FactorModSquares(elt::RngElt) -> SeqEnum
    { Returns a list of the factors of the element modulo squares. }
    if elt eq 0 then
        return [0];
    end if;

    num := Numerator(elt);
    den := Denominator(elt);
    
    constant := LeadingCoefficient(elt);
    if constant in Rationals() then
        constant := Squarefree(Numerator(constant)) *
            Squarefree(Denominator(constant));
    end if;

    num_factor := [factor[1] : factor in Factorisation(num) | factor[2] mod 2 eq 1];
    den_factor := [factor[1] : factor in Factorisation(den) | factor[2] mod 2 eq 1];

    factors := num_factor cat den_factor;

    assert IsSquare(constant * Product(factors) * elt);

    return [constant] cat factors;
end intrinsic;


intrinsic FactorModSquares(x::RngIntElt) -> SeqEnum
    { Factors the integer x modulo squares. Returns the list of prime
    divisors of x such that x is a square times the product of the list. }
    if x eq 0 then
        return [0];
    end if;

    factors := [factor[1] : factor in Factorisation(x) | factor[2] mod 2 eq 1];
    if x lt 0 then
        factors := [-1] cat factors;
    end if;

    return factors;
end intrinsic;


intrinsic FactorModSquares(x::FldRatElt) -> SeqEnum
    { Factors the rational number x modulo squares. Returns the list of prime
    divisors of x such that x is a square times the product of the list. }
    num := NumeratorTimesDenominator(x);

    return FactorModSquares(num);
end intrinsic;


intrinsic FareySequence(n::RngIntElt) -> SeqEnum
    { Computes the nth Farey sequence. }
    a := 0;
    b := 1;
    c := 1;
    d := n;
    sequence := [a/b, c/d];
    while d gt 1 do
        k := Floor((n+b) / d);
        p := k * c - a;
        q := k * d - b;
        Append(~sequence, p/q);
        a := c;
        b := d;
        c := p;
        d := q;
    end while;
    return sequence;
end intrinsic;


intrinsic NormalisePolynomial(poly::RngUPolElt) -> RngUPolElt
    { Returns the polynomial divided by its leading coefficient. }
    return poly / LeadingCoefficient(poly);
end intrinsic;


intrinsic NormalisePolynomial(poly::RngMPolElt) -> RngMPolElt
    { Returns the polynomial divided by its leading coefficient. }
    return poly / LeadingCoefficient(poly);
end intrinsic;


intrinsic HadamardProduct(A::Mtrx, B::Mtrx) -> Mtrx
    { Returns the Hadamard product of A and B. That is, A * B elementwise. }
    assert Nrows(A) eq Nrows(B);
    assert Ncols(A) eq Ncols(B);
    
    return Matrix([[A[i][j] * B[i][j] : j in [1..Ncols(A)]] : i in
        [1..Nrows(A)]]);
end intrinsic;


intrinsic HadamardSquare(A::Mtrx) -> Mtrx
    { Returns the Hadamard product of A and A. That is, A * A elementwise. }
    return HadamardProduct(A, A);
end intrinsic;


intrinsic PointsOnIntegralModelOfCurve(f::RngUPolElt, bound::RngIntElt) ->
    SetIndx
    { Searches for points on the curve y^2 = f(x). First transforms so the curve
    has an integral model, and then searches, and then transforms back. }
    lcm := LCM([Denominator(coeff) : coeff in Coefficients(f)]);
    
    ft := f * lcm^2;
    points := Points(HyperellipticCurve(ft) : Bound := bound);

    C := HyperellipticCurve(f);

    return {@ C![pt[1], pt[2] / lcm, pt[3]] : pt in points @};
end intrinsic;


intrinsic EvaluateSymmetricPolynomial(sym_poly::RngMPolElt,
    roots_poly::RngUPolElt) -> RngElt
    { Given a symmetric polynomial in x1, x2, evaluate it where x1, x2 are the
    roots of the quadratic roots_poly. }
    P<x1, x2> := Parent(sym_poly);
    assert Rank(P) eq 2;
    K := CoefficientRing(sym_poly);
    Q<s1, s2> := PolynomialRing(K, 2);
    check, sym_poly_Q := IsSymmetric(sym_poly, Q);
    assert check;
    assert Degree(roots_poly) eq 2;
    rt_sum := -Coefficient(roots_poly, 1) / Coefficient(roots_poly, 2);
    rt_prod := Coefficient(roots_poly, 0) / Coefficient(roots_poly, 2);
    
    return hom<Q->K | rt_sum, rt_prod>(sym_poly_Q);
end intrinsic;


intrinsic MultiplySequence(seq::SeqEnum, lambda::RngElt) -> seq
    { Returns the sequence with all elements multiplied by lambda. }
    return [elt * lambda : elt in seq];
end intrinsic;


intrinsic AddSequences(seq1::SeqEnum, seq2::SeqEnum) -> SeqEnum
    { Adds two sequences of the same size. }
    assert #seq1 eq #seq2;
    return [seq1[i] + seq2[i] : i in [1..#seq1]];
end intrinsic;


intrinsic MultiplySequences(seq1::SeqEnum, seq2::SeqEnum) -> SeqEnum
    { Muliplies two sequences of the same size. }
    assert #seq1 eq #seq2;
    return [seq1[i] * seq2[i] : i in [1..#seq1]];
end intrinsic;


intrinsic ColumnVectorToSequence(vec::Mtrx) -> SeqEnum
    { Converts the nx1 matrix to a sequence. }
    assert Ncols(vec) eq 1;
    return [vec[i][1] : i in [1..Nrows(vec)]];
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

intrinsic ComputeTwoTorsionPolynomials(f::RngUPolElt) -> SeqEnum
    { Computes all monic polynomials g of degree at most 2 such that <g, 0> is a
    2-torsion point on the Jacobian of y^2 = f(x). }
    quadratics := ComputeQuadraticsDividingF(f);
    if Degree(f) eq 5 then
        quadratics cat:= [factor[1] : factor in Factorisation(f)];
    end if;
    return quadratics;
end intrinsic;


intrinsic ComputeFlipPolynomial(f::RngUPolElt) -> RngUPolElt
    { Returns the flip map applied to the polynomial f(x). Assumes degree of f
    is 5 or 6. If y^2 = f(x), then we use (u, v) = (1/x, y/x^3), and change to
    v^2 = u^6 f(1/u). Then the flip polynomial is u^6 f(1/u). }
    assert Degree(f) in [5, 6];
    coeffs := [Coefficient(f, i) : i in [0..6]];
    P := Parent(f);
    return P!Polynomial(P, Reverse(coeffs));
end intrinsic;


intrinsic ComputeReversePolynomial(f::RngUPolElt) -> RngUPolElt
    { Computes the polynomial with reverse coefficients to f. }
    coeffs := [Coefficient(f, i) : i in [0..Degree(f)]];
    P := Parent(f);
    return P!Polynomial(P, Reverse(coeffs));
end intrinsic;


intrinsic HyperellipticFlipMap(g::RngUPolElt, d::RngIntElt) -> RngUPolElt
    { Substitutes x = 1/u and multiplies by u^d. Returns the result in terms of
    u, but the variable is still in the same polynomial ring. }
    n := Degree(g);
    assert d ge n;
    P<x> := Parent(g);
    coeffs := [Coefficient(g, i) : i in [0..n]];
    return x^(d-n) * P!Polynomial(Reverse(coeffs));
end intrinsic;


intrinsic IsNthPower(elt::RngElt, n::RngIntElt) -> Bool
    { Returns whether or not elt is an nth power in its parent ring. }

    P := PolynomialRing(Parent(elt));
    return #Roots(P.1^n - elt) gt 0;
end intrinsic;


intrinsic IntersectionOfGroups(subgroups::SeqEnum, group::GrpAb) -> GrpAb
    { Returns the intersection of the subgroups of group. }
    intersection := group;
    for subgroup in subgroups do
        intersection meet:= subgroup;
    end for;
    return intersection;
end intrinsic;


intrinsic IgusaInvariantsAreEqual(inv1::SeqEnum, inv2::SeqEnum) -> Bool
    { Returns whether or not the two Igusa invariants are equal over the
    algebraic closure. We use the weighted projective space with weights 1, 2,
    3, 4, 5 rather than 2, 4, 6, 8, 10. This makes sense over the algebraic
    closure. }
    WP := WeightedProjectiveSpace(Rationals(), [1,2,3,4,5]);
    return (WP!inv1) eq (WP!inv2);
end intrinsic;


intrinsic IgusaInvariants(f::RngUPolElt, twist::RngElt) -> SeqEnum
    { Returns the Igusa invariants of y^2 = f(x), scaled by twist. The space is
    weighted with weights 2, 4, 6, 8, 10. }
    invariants := IgusaInvariants(f);
    weights := [2, 4, 6, 8, 10];
    return [invariants[i] * twist^weights[i] : i in [1..5]];
end intrinsic;


intrinsic IgusaInvariantsNormalisedGeometrically(f::RngUPolElt) -> SeqEnum
    { Returns the Igusa invariants of y^2 = f(x), scaled so that the first entry
    is 1, if it is nonzero. The space is weighted with weights 2, 4, 6, 8, 10.
    In scaling by d^k rather than d^2k, we are assuming we are working over a
    field where d is square. This makes sense over the algebraic closure. }
    invariants := IgusaInvariants(f);
    twist := invariants[1];
    weights := [1, 2, 3, 4, 5];
    if twist ne 0 then
        return [invariants[i] / twist^weights[i] : i in [1..5]];
    else
        return invariants;
    end if;
end intrinsic;
    


intrinsic IgusaInvariantsNormalised(f::RngUPolElt) -> SeqEnum
    { Returns the Igusa invariants of y^2 = f(x), scaled so that the first entry
    is factored modulo squares, if it is nonzero. The space is weighted with
    weights 2, 4, 6, 8, 10. }
    invariants := IgusaInvariants(f);
    twist_mod_squares :=
        FactorModSquares(NumeratorTimesDenominator(invariants[1]));
    check, twist := IsSquare(invariants[1] / Product(twist_mod_squares));
    assert check;
    weights := [2, 4, 6, 8, 10];
    if twist ne 0 then
        return [invariants[i] / twist^weights[i] : i in [1..5]];
    else
        return invariants;
    end if;
end intrinsic;


intrinsic IsGeometricallyIsomorphic(f1::RngUPolElt, f2::RngUPolElt) -> Bool
    { Returns whether or not the genus 2 hyperelliptic curves f1, f2 are
    geometrically isomorphic. This happens if and only if they have the same
    Igusa invariants. }
    I1 := IgusaInvariants(HyperellipticCurve(f1));
    I2 := IgusaInvariants(HyperellipticCurve(f2));
    return IgusaInvariantsAreEqual(I1, I2);
end intrinsic;


intrinsic IsIsomorphicHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt) -> Bool
{ Returns whether or not the hyperelliptic curves y^2 = f1 and y^2 = f2 are isomorphic. }
    return IsIsomorphic(HyperellipticCurve(f1), HyperellipticCurve(f2));
end intrinsic;


intrinsic MaxDegreeOfFactor(poly::RngUPolElt) -> RngIntElt
    { Computes the maximum degree of an irreducible factor of poly. }
    if poly eq 0 then
        return 0;
    end if;
    return Max([Degree(factor[1]) : factor in Factorisation(poly)]);
end intrinsic;


intrinsic PrintOneLine(seq::SeqEnum)
    { A procedure to print out a list all on one line. }
    n := #seq;
    printf "[";
    for i in [1..n] do
        printf "%o", seq[i];
        if i eq n then
            printf "]\n";
        else
            printf ", ";
        end if;
    end for;
end intrinsic;


intrinsic TimeString() -> MonStgElt
{ Returns the current time as a string, using the unix command 'date'. }
    time_string := Pipe("date +%Y-%m-%d_%H-%M-%S", "");
    // The last character of time_string is a new line.
    l := #time_string;
    return time_string[1..l-1];
end intrinsic;
