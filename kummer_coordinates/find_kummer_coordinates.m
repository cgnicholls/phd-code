

intrinsic WeightsXSuperelliptic(poly::RngMPolElt) -> RngIntElt
{ Computes the weights of each monomial of the polynomial in
x1,y1,x2,y2,x3,y3,f0,f1,f2,f3,f4 according
to w_x(xi) = 1, w_x(yi) = 0, w_x(fi) = -i.}
    P := Parent(poly);
    K := CoefficientRing(P);
    Q<x1,y1,x2,y2,x3,y3,f0,f1,f2,f3,f4> := PolynomialRing(K, 11);

    the_hom := hom<P->Q | hom<K->Q | f0,f1,f2,f3,f4>, x1,y1,x2,y2,x3,y3>;
    poly_Q := the_hom(poly);

    var_weights := [1,0,1,0,1,0,0,-1,-2,-3,-4];

    // We can still have multiple terms once we involve the f_i.
    monomials := Monomials(poly_Q);
    weights := [ComputeSum([Degree(m, Q.i) * var_weights[i] : i in [1..11]]) : m in monomials];
    return weights, monomials;
end intrinsic;


intrinsic WeightsYSuperelliptic(poly::RngMPolElt) -> RngIntElt
{ Computes the weights of the monomials of the polynomial in
x1,y1,x2,y2,x3,y3,f0,f1,f2,f3,f4 according
to w_x(xi) = 0, w_x(yi) = 1, w_x(fi) = 3.}
    P := Parent(poly);
    K := CoefficientRing(P);
    Q<x1,y1,x2,y2,x3,y3,f0,f1,f2,f3,f4> := PolynomialRing(K, 11);

    the_hom := hom<P->Q | hom<K->Q | f0,f1,f2,f3,f4>, x1,y1,x2,y2,x3,y3>;
    poly_Q := the_hom(poly);

    var_weights := [0,1,0,1,0,1,3,3,3,3,3];

    // We can still have multiple terms once we involve the f_i.
    monomials := Monomials(poly_Q);
    weights := [ComputeSum([Degree(m, Q.i) * var_weights[i] : i in [1..11]]) : m in monomials];
    return weights, monomials;
end intrinsic;


intrinsic HomogeneousWeightXSuperelliptic(poly::RngMPolElt) -> RngIntElt
{ Computes the x-weight of the polynomial, assuming it is homogeneous with
respect to the weight. Otherwise raises an error. }
    weights := WeightsXSuperelliptic(poly);
    assert #Set(weights) eq 1;
    return weights[1];
end intrinsic;


intrinsic HomogeneousWeightYSuperelliptic(poly::RngMPolElt) -> RngIntElt
{ Computes the y-weight of the polynomial, assuming it is homogeneous with
respect to the weight. Otherwise raises an error. }
    weights := WeightsYSuperelliptic(poly);
    assert #Set(weights) eq 1;
    return weights[1];
end intrinsic;


intrinsic WeightOfMonomialSuperelliptic(mon::RngMPolElt, weight_x::RngIntElt, weight_y::RngIntElt) -> RngIntElt
{ Computes the weight of the monomial according to the variable weights. Assumes monomial
is an element of the ring Q<x1, y1, .., xg, yg>, and that weight(xi) = weight_x, weight(yi) = weight_y.
The weight of a monomial is then the maximum weight over i of the xi, yi part.}
    P := Parent(mon);
    two_g := Rank(P);
    assert two_g mod 2 eq 0;
    g := two_g div 2;
    assert IsMonomial(mon);

    weights := [weight_x * Degree(mon, P.(2 * i - 1)) + weight_y * Degree(mon, P.(2 * i)) : i in [1..g]];
    weight := Max(weights);
    return weight;
end intrinsic;


intrinsic WeightOfPolynomialSuperelliptic(poly::RngMPolElt, weight_x::RngIntElt, weight_y::RngIntElt) -> RngIntElt
{ Computes the weight of the polynomial as the maximum of the weights of its monomials. }
    weights := [WeightOfMonomialSuperelliptic(mon, weight_x, weight_y) : mon in Monomials(poly)];
    weight := Max(weights);
    return weight;
end intrinsic;


intrinsic MonomialsOfMaxWeight(max_weight::RngIntElt, g::RngIntElt,
    weight_x::RngIntElt, weight_y::RngIntElt) -> SeqEnum
{ Returns monomials in the variables x1, y1, .., xg, yg of maximum
weight according to the given weights. The parent polynomial ring has
variables in the order x1, y1, .., xg, yg.}
    P := PolynomialRing(Rationals(), 2 * g);
    assert weight_x gt 0 and weight_y gt 0;
    // The maximum degree in each xi, yi is max_weight / Min(weight_x, weight_y), and we can
    // have this in each of the g pairs xi, yi.
    max_degree := g * Floor(Max(max_weight / weight_x, max_weight / weight_y));
    monomials := MonomialsOfMaxDegree(P, max_degree);
    return [mon : mon in monomials | WeightOfMonomialSuperelliptic(mon, weight_x, weight_y) le max_weight];
end intrinsic;


intrinsic MatrixOfHomomorphism(the_hom::Map, V::ModTupFld, monomial_basis::SeqEnum) -> Matrx
{ Let the_hom be a map on the polynomial ring. This function returns the matrix of
the_hom acting on the vector space V. }
    columns := [];
    for m in monomial_basis do
        Append(~columns, PolynomialToVector(the_hom(m), V, monomial_basis));
    end for;
    return Transpose(Matrix(columns));
end intrinsic;


intrinsic SymmetricSubspaceSuperelliptic(V::ModTupFld, monomial_basis::SeqEnum) -> ModTupFld
{ Given a vector space V with basis given by monomials, find the subspace of V
that is symmetric under the action of the symmetric group on (x1, y1), (x2,
y2), (x3, y3). }
    Q<x1,y1,x2,y2,x3,y3> := Universe(monomial_basis);
    K := BaseRing(Q);
    t12 := hom<Q->Q | x2,y2,x1,y1,x3,y3>;
    t13 := hom<Q->Q | x3,y3,x2,y2,x1,y1>;

    M12 := MatrixOfHomomorphism(t12, V, monomial_basis);
    M13 := MatrixOfHomomorphism(t13, V, monomial_basis);
    
    K12 := Kernel(M12 - IdentityMatrix(K, #monomial_basis));
    K13 := Kernel(M13 - IdentityMatrix(K, #monomial_basis));

    return K12 meet K13;
end intrinsic;


intrinsic AntiSymmetricSubspaceSuperelliptic(V::ModTupFld, monomial_basis::SeqEnum) -> ModTupFld
{ Given a vector space V with basis given by monomials, find the subspace of V
satisfying: transpositions of (x1, y1), (x2, y2), (x3, y3) change the sign of
the function. }
    Q<x1,y1,x2,y2,x3,y3> := Universe(monomial_basis);
    K := BaseRing(Q);
    t12 := hom<Q->Q | x2,y2,x1,y1,x3,y3>;
    t13 := hom<Q->Q | x3,y3,x2,y2,x1,y1>;

    M12 := MatrixOfHomomorphism(t12, V, monomial_basis);
    M13 := MatrixOfHomomorphism(t13, V, monomial_basis);
    
    K12 := Kernel(M12 + IdentityMatrix(K, #monomial_basis));
    K13 := Kernel(M13 + IdentityMatrix(K, #monomial_basis));

    return K12 meet K13;
end intrinsic;


intrinsic SpecialisePolynomial(poly::RngMPolElt, coeffs::SeqEnum) -> RngMPolElt
{ Specialises the polynomial to the given coefficients. }
    P := Parent(poly);
    K := BaseRing(P);

    return hom<P->P | hom<K->K | coeffs>, [P.i : i in [1..Rank(P)]]>(poly);
end intrinsic;


intrinsic ReduceInFunctionFieldSuperelliptic(poly::RngMPolElt, f_coeffs::SeqEnum) -> RngMPolElt
{ Given an expression in x1, ..., y3, reduce it by replacing occurrences of yi^3 by f(xi). }
    assert Rank(Parent(poly)) eq 6;
    Q<x1, y1, x2, y2, x3, y3> := Parent(poly);

    ring := Parent(poly);
    poly := ring!poly;
    x1 := ring.1; y1 := ring.2; x2 := ring.3; y2 := ring.4; x3 := ring.5; y3 := ring.6;
    f_coeffs := ChangeUniverse(f_coeffs, ring);
    fx1 := f_coeffs[5]*x1^4 + f_coeffs[4]*x1^3 + f_coeffs[3]*x1^2 + f_coeffs[2]*x1 + f_coeffs[1];
    fx2 := f_coeffs[5]*x2^4 + f_coeffs[4]*x2^3 + f_coeffs[3]*x2^2 + f_coeffs[2]*x2 + f_coeffs[1];
    fx3 := f_coeffs[5]*x3^4 + f_coeffs[4]*x3^3 + f_coeffs[3]*x3^2 + f_coeffs[2]*x3 + f_coeffs[1];
    deg1 := Degree(poly, y1);
    while deg1 ge 3 do
        poly := poly + Coefficient(poly, y1, deg1) *
(fx1^(Floor(deg1/3))*y1^(deg1 mod 3) - y1^deg1);
        poly := ring!poly;
        deg1 := Degree(poly, y1);
    end while;
    deg2 := Degree(poly, y2);
    while deg2 ge 3 do
        poly := poly + Coefficient(poly, y2, deg2) *
(fx2^(Floor(deg2/3))*y2^(deg2 mod 3) - y2^deg2);
        poly := ring!poly;
        deg2 := Degree(poly, y2);
    end while;
    deg3 := Degree(poly, y3);
    while deg3 ge 3 do
        poly := poly + Coefficient(poly, y3, deg3) *
(fx3^(Floor(deg3/3))*y3^(deg3 mod 3) - y3^deg3);
        poly := ring!poly;
        deg3 := Degree(poly, y3);
    end while;
    return poly;
end intrinsic;


generalised_binomial := function(alpha, k)
    // Computes alpha * (alpha-1) * ... * (alpha-k+1) / k!
    prod := 1;
    for i in [0..k-1] do
        prod := prod * (alpha - i);
    end for;
    return prod / Factorial(k);
end function;


intrinsic ApproximateYSquaredSuperelliptic(order::RngIntElt, power::RngElt,
f_coeffs::SeqEnum, Q::RngMPol) -> RngMPolElt
{ Approximates f(x1+e)^(power) to given order. }
    KQ<s1,t1,s2,t2,s3,t3> := FieldOfFractions(Q);
    R<e> := PolynomialRing(KQ);
    K := BaseRing(KQ);

    // Let `small' be such that f(x1) * (1 + e * small) = f(x1+e).
    fx1 := f_coeffs[1] + f_coeffs[2] * s1 + f_coeffs[3] * s1^2 + f_coeffs[4] * s1^3 +
        f_coeffs[5] * s1^4;
    fx2 := f_coeffs[1] + f_coeffs[2] * (s1 + e) + f_coeffs[3] * (s1 + e)^2 +
        f_coeffs[4] * (s1 + e)^3 + f_coeffs[5] * (s1 + e)^4;

    small := (fx2 / fx1 - 1) / e;

    // We then want to approximate (1 + e*small)^(power) to given order
    sum := 0;
    for i in [0..order] do
        sum := sum + generalised_binomial(power, i) * e^i * small^i;
    end for;

    // Now only keep the terms of degree at most the given order.
    expr := R!(sum*t1);
    return ComputeSum([Coefficient(expr, i) * e^i : i in [0..Min(Degree(expr), order)]]);
end intrinsic;


intrinsic SubspaceVanishingToOrderSuperelliptic(sym_polynomials::SeqEnum,
order::RngIntElt, f_coeffs::SeqEnum) -> ModTupFld
{ Given polynomials in x1, y1, x2, y2, x3, y3 finds the linear subspace of
polynomials that have vanishing e^0, ..., e^(order-1) coefficient on
substituting x2 = x1+e, y2 = approximatey2(order). Symmetry then implies
that the function vanishes to the correct order for each variable. }
    Q<x1,y1,x2,y2,x3,y3> := Universe(sym_polynomials);
    Q := ChangeRing(Q, Universe(f_coeffs));
    y2approx := ApproximateYSquaredSuperelliptic(order+1, 1/3, f_coeffs, Q);
    R<e> := Parent(y2approx);
    KQ<s1,t1,s2,t2,s3,t3> := BaseRing(R);
    approx_hom := hom< Q->R | s1, t1, s1+e, y2approx, s3, t3 >;

    sym_polynomials := ChangeUniverse(sym_polynomials, Q);

    V, monomial_basis := VectorSpaceForPolynomials(sym_polynomials);

    subspace := sub< V | [PolynomialToVector(poly, V, monomial_basis) : poly in sym_polynomials] >;
    for i in [0..order-1] do
        print "Computing to order", i, "with subspace of dimension", Dimension(subspace);
        // Compute the polynomials corresponding to the basis of the subspace.
        subspace_basis_polys := [VectorToPolynomial(v, monomial_basis) : v in Basis(subspace)];

        // Multiply up by the common denominator, so the subspace basis polynomials are all in Q.
        common_denom := LCM([Denominator(Coefficient(approx_hom(poly), i)) : poly in subspace_basis_polys]);
        approx_polys := [Q!(common_denom * Coefficient(approx_hom(poly), i)) : poly in subspace_basis_polys];

        // Reduce the polynomials modulo y^3 = f(x).
        approx_polys := [ReduceInFunctionFieldSuperelliptic(poly, f_coeffs) : poly in approx_polys];

        // Compute the linear relations between the polynomials. This is the subspace of vectors v such that
        // v * Matrix(approx_polys_vectors) = 0.
        linear_relations := LinearRelationsBetweenPolynomials(approx_polys);

        // Now compute v * Matrix(u) for each vector u of a subspace basis polynomial, and convert
        // it back into a polynomial.
        M := Matrix(Basis(linear_relations));
        subspace_basis_vectors := [PolynomialToVector(poly, V, monomial_basis) : poly in subspace_basis_polys];
        new_subspace_basis := ChangeRing(M, Q) * ChangeRing(Matrix(subspace_basis_vectors), Q);
        subspace meet:= sub<V | [V!row : row in Rows(new_subspace_basis)]>;
    end for;
    return subspace, V, monomial_basis;
end intrinsic;




intrinsic OrderOfVanishingSuperelliptic_12(poly::RngMPolElt, max_order::RngIntElt, f_coeffs::SeqEnum) -> RngIntElt
{ Given a polynomial in x1, y1, x2, y2, x3, y3 computes the order of vanishing
at the divisor (x1, y1) + (x1, y1) + (x3, y3) on Sym^3 C, up to a maximum order
of max_order. }
    Q<x1,y1,x2,y2,x3,y3> := Parent(poly);
    Q := ChangeRing(Q, Universe(f_coeffs));
    y2approx := ApproximateYSquaredSuperelliptic(max_order, 1/3, f_coeffs, Q);
    R<e> := Parent(y2approx);
    KQ<s1,t1,s2,t2,s3,t3> := BaseRing(R);
    approx_hom := hom< Q->R | s1, t1, s1+e, y2approx, s3, t3 >;

    approx_poly := approx_hom(poly);

    degree := Min(Degree(approx_poly), max_order);
    coeffs := [ReduceInFunctionFieldSuperelliptic(Numerator(Coefficient(approx_poly, i)), f_coeffs) : i in [0..degree]];
    if coeffs[1] ne 0 then
        return 0;
    end if;
    order := 1;
    for i in [1..#coeffs] do
        if coeffs[i] ne 0 then
            return i-1;
        end if;
    end for;
    return max_order;
end intrinsic;


intrinsic OrderOfVanishingSuperelliptic(poly::RngMPolElt, maxorder::RngIntElt, f_coeffs::SeqEnum) -> RngIntElt
{ Given a polynomial in x1, y1, x2, y2, x3, y3 computes the order of vanishing
at the divisor (xi, yi) = (xj, yj), up to a maximum order of maxorder, for
each pair i, j with i != j. }
    Q<x1,y1,x2,y2,x3,y3> := Parent(poly);
    Q := ChangeRing(Q, Universe(f_coeffs));
    t12 := hom< Q->Q | x2,y2,x1,y1,x3,y3 >;
    t13 := hom< Q->Q | x3,y3,x2,y2,x1,y1 >;
    t23 := hom< Q->Q | x1,y1,x3,y3,x2,y2 >;

    ord12 := OrderOfVanishingSuperelliptic_12(poly, maxorder, f_coeffs);
    ord13 := OrderOfVanishingSuperelliptic_12(t23(poly), maxorder, f_coeffs);
    ord23 := OrderOfVanishingSuperelliptic_12(t12(poly), maxorder, f_coeffs);
    minord := Min([ord12, ord13, ord23]);
    return minord;
end intrinsic;


intrinsic DenominatorInFunctionField(poly::RngMPolElt) -> RngElt
{ Computes the denominator of the coefficients. }
    K := BaseRing(Parent(poly));
    return LCM([Denominator(coeff) : coeff in Coefficients(poly)]);
end intrinsic;


intrinsic FindKummerCoordinatesGenus3() -> SeqEnum
{ Derives the Kummer coordinates in genus 3. }
    // This program attempts to compute the Jacobian coordinates for a genus 3
    // superelliptic curve.
    K<f0,f1,f2,f3,f4> := FunctionField(Rationals(), 5);
    f_coeffs := [f0,f1,f2,f3,f4];

    g := 3;
    weight_x := 3;
    weight_y := 4;

    // The following function is a useful denominator. It has weight 4.
    // d := x1*(y2-y3) + x2*(y3-y1) + x3*(y1-y2);

    // We use d^2 as a denominator. Thus we want functions g that vanish to order 2 along
    // the divisor { 2 D + E : D, E in C } and that are of weight at most 10. This gives g / d^2
    // in L(2 Theta).

    // First find the subspace of symmetric polynomials of weight at most 10.
    V, monomial_basis := VectorSpaceForPolynomials(MonomialsOfMaxWeight(10, g, weight_x, weight_y));
    sym_subspace := SymmetricSubspaceSuperelliptic(V, monomial_basis);
    sym_polynomials := [VectorToPolynomial(v, monomial_basis) : v in Basis(sym_subspace)];

    // Now impose that the polynomials vanish to order 2.
    subspace, V, monomial_basis := SubspaceVanishingToOrderSuperelliptic(sym_polynomials, 2, f_coeffs);

    kummer_coordinates := [VectorToPolynomial(v, monomial_basis) : v in Basis(subspace)];
    assert #kummer_coordinates eq 8;

    // Clear denominators in the coefficients fi.
    kummer_coordinates := [DenominatorInFunctionField(coord) * coord : coord in kummer_coordinates];

    // These 8 functions have weight at most 10, and we use d^2 as a denominator.
    // Their order of vanishing at the divisor Pi = Pj is as follows:
    assert { OrderOfVanishingSuperelliptic(poly, 2, f_coeffs) : poly in kummer_coordinates } eq { 2 };

    // Check their weights:
    assert Max([WeightOfPolynomialSuperelliptic(poly, weight_x, weight_y) : poly in kummer_coordinates]) le 10;

    // Check their dimension:
    V, monomial_basis := VectorSpaceForPolynomials(kummer_coordinates);
    assert Dimension(SubspaceOfPolynomials(kummer_coordinates, monomial_basis)) eq 8;

    return kummer_coordinates;
end intrinsic;


intrinsic KummerCoordinatesGenus3Superelliptic() -> SeqEnum
{ Returns the Kummer coordinates for a genus 3 superelliptic curve y^2 = f(x). Here, f(x) has degree 4.
These are as computed by FindKummerCoordinatesGenus3. }
    K<f0,f1,f2,f3,f4> := FunctionField(Rationals(), 5);
    Q<x1,y1,x2,y2,x3,y3> := PolynomialRing(K, 6);

    kummer_coordinates := [
        2*f4^2*x1^3*x2^3*x3^2 - 2*f2*f4*x1^3*x2^3 + 2*f4^2*x1^3*x2^2*x3^3 +
            4*f3*f4*x1^3*x2^2*x3^2 + 4*f2*f4*x1^3*x2^2*x3 + (f1*f4 -
            f2*f3)*x1^3*x2^2 - 2*f4*x1^3*x2*y2*y3^2 + 4*f2*f4*x1^3*x2*x3^2 +
            (2*f1*f4 + 2*f2*f3)*x1^3*x2*x3 + 2*f0*f4*x1^3*x2 - 2*f4*x1^3*y2^2*x3*y3
            - 2*f2*f4*x1^3*x3^3 + (f1*f4 - f2*f3)*x1^3*x3^2 + 2*f0*f4*x1^3*x3 -
            f4*x1^2*y1*x2^2*y3^2 + 2*f4*x1^2*y1*x2*y2*x3*y3 - f4*x1^2*y1*y2^2*x3^2 +
            f2*x1^2*y1*y2^2 - 2*f2*x1^2*y1*y2*y3 + f2*x1^2*y1*y3^2 +
            2*f4^2*x1^2*x2^3*x3^3 + 4*f3*f4*x1^2*x2^3*x3^2 + 4*f2*f4*x1^2*x2^3*x3 +
            (f1*f4 - f2*f3)*x1^2*x2^3 - f4*x1^2*x2^2*y2*y3^2 +
            4*f3*f4*x1^2*x2^2*x3^3 + (-6*f2*f4 + 6*f3^2)*x1^2*x2^2*x3^2 +
            4*f2*f3*x1^2*x2^2*x3 + (2*f0*f4 + 2*f1*f3 - 2*f2^2)*x1^2*x2^2 -
            3*f3*x1^2*x2*y2*y3^2 + 4*f2*f4*x1^2*x2*x3^3 + 4*f2*f3*x1^2*x2*x3^2 +
            (-2*f0*f4 + 2*f1*f3 + 4*f2^2)*x1^2*x2*x3 + 3*f0*f3*x1^2*x2 -
            f4*x1^2*y2^2*x3^2*y3 - 3*f3*x1^2*y2^2*x3*y3 + (f1*f4 - f2*f3)*x1^2*x3^3
            + (2*f0*f4 + 2*f1*f3 - 2*f2^2)*x1^2*x3^2 + 3*f0*f3*x1^2*x3 -
            2*f4*x1*y1*x2^3*y3^2 + 2*f4*x1*y1*x2^2*y2*x3*y3 - 3*f3*x1*y1*x2^2*y3^2 +
            2*f4*x1*y1*x2*y2*x3^2*y3 + 6*f3*x1*y1*x2*y2*x3*y3 + 4*f2*x1*y1*x2*y2*y3
            - 4*f2*x1*y1*x2*y3^2 - 2*f4*x1*y1*y2^2*x3^3 - 3*f3*x1*y1*y2^2*x3^2 -
            4*f2*x1*y1*y2^2*x3 - f1*x1*y1*y2^2 + 4*f2*x1*y1*y2*x3*y3 +
            2*f1*x1*y1*y2*y3 - f1*x1*y1*y3^2 + 4*f2*f4*x1*x2^3*x3^2 + (2*f1*f4 +
            2*f2*f3)*x1*x2^3*x3 + 2*f0*f4*x1*x2^3 + 4*f2*f4*x1*x2^2*x3^3 +
            4*f2*f3*x1*x2^2*x3^2 + (-2*f0*f4 + 2*f1*f3 + 4*f2^2)*x1*x2^2*x3 +
            3*f0*f3*x1*x2^2 - 4*f2*x1*x2*y2*y3^2 + (2*f1*f4 + 2*f2*f3)*x1*x2*x3^3 +
            (-2*f0*f4 + 2*f1*f3 + 4*f2^2)*x1*x2*x3^2 + (-6*f0*f3 +
            12*f1*f2)*x1*x2*x3 + (4*f0*f2 + 2*f1^2)*x1*x2 - 4*f2*x1*y2^2*x3*y3 -
            2*f1*x1*y2^2*y3 - 2*f1*x1*y2*y3^2 + 2*f0*f4*x1*x3^3 + 3*f0*f3*x1*x3^2 +
            (4*f0*f2 + 2*f1^2)*x1*x3 + 4*f0*f1*x1 - 2*f4*y1^2*x2^3*x3*y3 -
            f4*y1^2*x2^2*y2*x3^2 + f2*y1^2*x2^2*y2 - f4*y1^2*x2^2*x3^2*y3 -
            3*f3*y1^2*x2^2*x3*y3 - 2*f4*y1^2*x2*y2*x3^3 - 3*f3*y1^2*x2*y2*x3^2 -
            4*f2*y1^2*x2*y2*x3 - f1*y1^2*x2*y2 - 4*f2*y1^2*x2*x3*y3 -
            2*f1*y1^2*x2*y3 + 6*y1^2*y2^2*y3^2 - 2*f1*y1^2*y2*x3 - 3*f0*y1^2*y2 +
            f2*y1^2*x3^2*y3 - f1*y1^2*x3*y3 - 3*f0*y1^2*y3 - 2*f2*y1*x2^2*y2*y3 +
            4*f2*y1*x2*y2*x3*y3 + 2*f1*y1*x2*y2*y3 - 2*f1*y1*x2*y3^2 -
            2*f1*y1*y2^2*x3 - 3*f0*y1*y2^2 - 2*f2*y1*y2*x3^2*y3 + 2*f1*y1*y2*x3*y3 +
            6*f0*y1*y2*y3 - 3*f0*y1*y3^2 - 2*f2*f4*x2^3*x3^3 + (f1*f4 -
            f2*f3)*x2^3*x3^2 + 2*f0*f4*x2^3*x3 + f2*x2^2*y2*y3^2 + (f1*f4 -
            f2*f3)*x2^2*x3^3 + (2*f0*f4 + 2*f1*f3 - 2*f2^2)*x2^2*x3^2 +
            3*f0*f3*x2^2*x3 - f1*x2*y2*y3^2 + 2*f0*f4*x2*x3^3 + 3*f0*f3*x2*x3^2 +
            (4*f0*f2 + 2*f1^2)*x2*x3 + 4*f0*f1*x2 + f2*y2^2*x3^2*y3 - f1*y2^2*x3*y3
            - 3*f0*y2^2*y3 - 3*f0*y2*y3^2 + 4*f0*f1*x3 + 6*f0^2,
        2*f4*x1^3*x2^3 - 2*f4*x1^3*x2^2*x3 + f3*x1^3*x2^2 - 2*f4*x1^3*x2*x3^2 -
            2*f3*x1^3*x2*x3 + 2*f4*x1^3*x3^3 + f3*x1^3*x3^2 - x1^2*y1*y2^2 +
            2*x1^2*y1*y2*y3 - x1^2*y1*y3^2 - 2*f4*x1^2*x2^3*x3 + f3*x1^2*x2^3 +
            6*f4*x1^2*x2^2*x3^2 + 2*f2*x1^2*x2^2 - 2*f4*x1^2*x2*x3^3 -
            2*f2*x1^2*x2*x3 + f1*x1^2*x2 - x1^2*y2^2*y3 - x1^2*y2*y3^2 +
            f3*x1^2*x3^3 + 2*f2*x1^2*x3^2 + f1*x1^2*x3 + 2*f0*x1^2 -
            2*x1*y1*x2*y2*y3 + 2*x1*y1*x2*y3^2 + 2*x1*y1*y2^2*x3 - 2*x1*y1*y2*x3*y3
            - 2*f4*x1*x2^3*x3^2 - 2*f3*x1*x2^3*x3 - 2*f4*x1*x2^2*x3^3 -
            2*f2*x1*x2^2*x3 + f1*x1*x2^2 + 2*x1*x2*y2*y3^2 - 2*f3*x1*x2*x3^3 -
            2*f2*x1*x2*x3^2 - 6*f1*x1*x2*x3 - 2*f0*x1*x2 + 2*x1*y2^2*x3*y3 +
            f1*x1*x3^2 - 2*f0*x1*x3 - y1^2*x2^2*y2 - y1^2*x2^2*y3 + 2*y1^2*x2*y2*x3
            + 2*y1^2*x2*x3*y3 - y1^2*y2*x3^2 - y1^2*x3^2*y3 + 2*y1*x2^2*y2*y3 -
            y1*x2^2*y3^2 - 2*y1*x2*y2*x3*y3 - y1*y2^2*x3^2 + 2*y1*y2*x3^2*y3 +
            2*f4*x2^3*x3^3 + f3*x2^3*x3^2 - x2^2*y2*y3^2 + f3*x2^2*x3^3 +
            2*f2*x2^2*x3^2 + f1*x2^2*x3 + 2*f0*x2^2 + f1*x2*x3^2 - 2*f0*x2*x3 -
            y2^2*x3^2*y3 + 2*f0*x3^2,
        2*f4*x1^3*x2^3*y3 - 2*f4*x1^3*x2^2*x3*y3 + f3*x1^3*x2^2*y3 -
            2*f4*x1^3*x2*y2*x3^2 - f3*x1^3*x2*y2*x3 - f3*x1^3*x2*x3*y3 +
            2*f4*x1^3*y2*x3^3 + f3*x1^3*y2*x3^2 + 2*f4*x1^2*y1*x2^2*x3^2 +
            f3*x1^2*y1*x2^2*x3 + f3*x1^2*y1*x2*x3^2 + 2*f2*x1^2*y1*x2*x3 +
            f1*x1^2*y1*x2 - x1^2*y1*y2^2*y3 - x1^2*y1*y2*y3^2 + f1*x1^2*y1*x3 +
            2*f0*x1^2*y1 - 2*f4*x1^2*x2^3*x3*y3 + f3*x1^2*x2^3*y3 +
            2*f4*x1^2*x2^2*y2*x3^2 + f3*x1^2*x2^2*y2*x3 + 2*f4*x1^2*x2^2*x3^2*y3 -
            2*f3*x1^2*x2^2*x3*y3 + 2*f2*x1^2*x2^2*y3 - 2*f4*x1^2*x2*y2*x3^3 -
            2*f3*x1^2*x2*y2*x3^2 - 2*f2*x1^2*x2*y2*x3 - f1*x1^2*x2*y2 +
            f3*x1^2*x2*x3^2*y3 - 2*f2*x1^2*x2*x3*y3 + f1*x1^2*x2*y3 +
            f3*x1^2*y2*x3^3 + 2*f2*x1^2*y2*x3^2 + f1*x1^2*y2*x3 - f1*x1^2*x3*y3 -
            2*f4*x1*y1*x2^3*x3^2 - f3*x1*y1*x2^3*x3 - 2*f4*x1*y1*x2^2*x3^3 -
            2*f3*x1*y1*x2^2*x3^2 - 2*f2*x1*y1*x2^2*x3 - f1*x1*y1*x2^2 +
            2*x1*y1*x2*y2*y3^2 - f3*x1*y1*x2*x3^3 - 2*f2*x1*y1*x2*x3^2 -
            2*f1*x1*y1*x2*x3 - 2*f0*x1*y1*x2 + 2*x1*y1*y2^2*x3*y3 - f1*x1*y1*x3^2 -
            2*f0*x1*y1*x3 - f3*x1*x2^3*x3*y3 + f3*x1*x2^2*y2*x3^2 +
            2*f2*x1*x2^2*y2*x3 + f1*x1*x2^2*y2 + f3*x1*x2^2*x3^2*y3 -
            2*f2*x1*x2^2*x3*y3 + f1*x1*x2^2*y3 - f3*x1*x2*y2*x3^3 -
            2*f2*x1*x2*y2*x3^2 - 2*f1*x1*x2*y2*x3 - 2*f0*x1*x2*y2 +
            2*f2*x1*x2*x3^2*y3 - 2*f1*x1*x2*x3*y3 + 2*f0*x1*x2*y3 + f1*x1*y2*x3^2 +
            2*f0*x1*y2*x3 + f1*x1*x3^2*y3 - 2*f0*x1*x3*y3 - y1^2*x2^2*y2*y3 +
            2*y1^2*x2*y2*x3*y3 - y1^2*y2*x3^2*y3 + 2*f4*y1*x2^3*x3^3 +
            f3*y1*x2^3*x3^2 - y1*x2^2*y2*y3^2 + f3*y1*x2^2*x3^3 + 2*f2*y1*x2^2*x3^2
            + f1*y1*x2^2*x3 + f1*y1*x2*x3^2 + 2*f0*y1*x2*x3 - y1*y2^2*x3^2*y3 +
            f1*x2^2*y2*x3 + 2*f0*x2^2*y2 - f1*x2^2*x3*y3 - f1*x2*y2*x3^2 -
            2*f0*x2*y2*x3 + f1*x2*x3^2*y3 - 2*f0*x2*x3*y3 + 2*f0*x3^2*y3,
        2*f4*x1^3*x2^3*x3 - 2*f4*x1^3*x2^2*x3^2 + f3*x1^3*x2^2*x3 +
            2*f4*x1^3*x2*x3^3 + f3*x1^3*x2*x3^2 + 2*f2*x1^3*x2*x3 + f1*x1^3*x2 -
            x1^3*y2^2*y3 - x1^3*y2*y3^2 + f1*x1^3*x3 + 2*f0*x1^3 + x1^2*y1*x2*y2*y3
            - x1^2*y1*x2*y3^2 - x1^2*y1*y2^2*x3 + x1^2*y1*y2*x3*y3 -
            2*f4*x1^2*x2^3*x3^2 + f3*x1^2*x2^3*x3 - 2*f4*x1^2*x2^2*x3^3 -
            6*f3*x1^2*x2^2*x3^2 - 2*f2*x1^2*x2^2*x3 - 2*f1*x1^2*x2^2 +
            2*x1^2*x2*y2*y3^2 + f3*x1^2*x2*x3^3 - 2*f2*x1^2*x2*x3^2 - 2*f0*x1^2*x2 +
            2*x1^2*y2^2*x3*y3 - 2*f1*x1^2*x3^2 - 2*f0*x1^2*x3 + x1*y1*x2^2*y2*y3 +
            2*x1*y1*x2^2*y3^2 - 6*x1*y1*x2*y2*x3*y3 + 2*x1*y1*y2^2*x3^2 +
            x1*y1*y2*x3^2*y3 + 2*f4*x1*x2^3*x3^3 + f3*x1*x2^3*x3^2 + 2*f2*x1*x2^3*x3
            + f1*x1*x2^3 - x1*x2^2*y2*y3^2 + f3*x1*x2^2*x3^3 - 2*f2*x1*x2^2*x3^2 -
            2*f0*x1*x2^2 + 2*f2*x1*x2*x3^3 + 6*f0*x1*x2*x3 - x1*y2^2*x3^2*y3 +
            f1*x1*x3^3 - 2*f0*x1*x3^2 - y1^2*x2^3*y3 - y1^2*x2^2*y2*x3 +
            2*y1^2*x2^2*x3*y3 + 2*y1^2*x2*y2*x3^2 - y1^2*x2*x3^2*y3 - y1^2*y2*x3^3 -
            y1*x2^3*y3^2 + y1*x2^2*y2*x3*y3 + y1*x2*y2*x3^2*y3 - y1*y2^2*x3^3 +
            f1*x2^3*x3 + 2*f0*x2^3 - 2*f1*x2^2*x3^2 - 2*f0*x2^2*x3 + f1*x2*x3^3 -
            2*f0*x2*x3^2 + 2*f0*x3^3,
        x1^2*y2^2 - 2*x1^2*y2*y3 + x1^2*y3^2 - 2*x1*y1*x2*y2 + 2*x1*y1*x2*y3 +
            2*x1*y1*y2*x3 - 2*x1*y1*x3*y3 + 2*x1*x2*y2*y3 - 2*x1*x2*y3^2 -
            2*x1*y2^2*x3 + 2*x1*y2*x3*y3 + y1^2*x2^2 - 2*y1^2*x2*x3 + y1^2*x3^2 -
            2*y1*x2^2*y3 + 2*y1*x2*y2*x3 + 2*y1*x2*x3*y3 - 2*y1*y2*x3^2 + x2^2*y3^2
            - 2*x2*y2*x3*y3 + y2^2*x3^2,
        x1^3*y2^2 - 2*x1^3*y2*y3 + x1^3*y3^2 - x1^2*y1*x2*y2 + x1^2*y1*x2*y3 +
            x1^2*y1*y2*x3 - x1^2*y1*x3*y3 + x1^2*x2*y2*y3 - x1^2*x2*y3^2 -
            x1^2*y2^2*x3 + x1^2*y2*x3*y3 - x1*y1*x2^2*y2 + x1*y1*x2^2*y3 +
            x1*y1*y2*x3^2 - x1*y1*x3^2*y3 + x1*x2^2*y2*y3 - x1*x2^2*y3^2 -
            x1*y2^2*x3^2 + x1*y2*x3^2*y3 + y1^2*x2^3 - y1^2*x2^2*x3 - y1^2*x2*x3^2 +
            y1^2*x3^3 - 2*y1*x2^3*y3 + y1*x2^2*y2*x3 + y1*x2^2*x3*y3 + y1*x2*y2*x3^2
            + y1*x2*x3^2*y3 - 2*y1*y2*x3^3 + x2^3*y3^2 - x2^2*y2*x3*y3 -
            x2*y2*x3^2*y3 + y2^2*x3^3,
        x1^3*x2*y2 - x1^3*x2*y3 - x1^3*y2*x3 + x1^3*x3*y3 - x1^2*y1*x2^2 +
            2*x1^2*y1*x2*x3 - x1^2*y1*x3^2 - x1^2*x2^2*y2 + 2*x1^2*x2^2*y3 -
            x1^2*x2*y2*x3 - x1^2*x2*x3*y3 + 2*x1^2*y2*x3^2 - x1^2*x3^2*y3 +
            x1*y1*x2^3 - x1*y1*x2^2*x3 - x1*y1*x2*x3^2 + x1*y1*x3^3 - x1*x2^3*y3 +
            2*x1*x2^2*y2*x3 - x1*x2^2*x3*y3 - x1*x2*y2*x3^2 + 2*x1*x2*x3^2*y3 -
            x1*y2*x3^3 - y1*x2^3*x3 + 2*y1*x2^2*x3^2 - y1*x2*x3^3 + x2^3*x3*y3 -
            x2^2*y2*x3^2 - x2^2*x3^2*y3 + x2*y2*x3^3,
        x1^3*x2*y2*y3 - x1^3*x2*y3^2 - x1^3*y2^2*x3 + x1^3*y2*x3*y3 -
            x1^2*y1*x2^2*y3 + x1^2*y1*x2*y2*x3 + x1^2*y1*x2*x3*y3 - x1^2*y1*y2*x3^2
            - x1^2*x2^2*y2*y3 + 2*x1^2*x2^2*y3^2 - 2*x1^2*x2*y2*x3*y3 +
            2*x1^2*y2^2*x3^2 - x1^2*y2*x3^2*y3 + x1*y1*x2^3*y3 + x1*y1*x2^2*y2*x3 -
            2*x1*y1*x2^2*x3*y3 - 2*x1*y1*x2*y2*x3^2 + x1*y1*x2*x3^2*y3 +
            x1*y1*y2*x3^3 - x1*x2^3*y3^2 + x1*x2^2*y2*x3*y3 + x1*x2*y2*x3^2*y3 -
            x1*y2^2*x3^3 - y1^2*x2^3*x3 + 2*y1^2*x2^2*x3^2 - y1^2*x2*x3^3 +
            y1*x2^3*x3*y3 - y1*x2^2*y2*x3^2 - y1*x2^2*x3^2*y3 + y1*x2*y2*x3^3
    ];
    return kummer_coordinates;
end intrinsic;


intrinsic KummerCoordinatesGenus3SuperellipticOld() -> SeqEnum
{ Returns the Kummer coordinates for a genus 3 superelliptic curve y^2 = f(x). Here, f(x) has degree 4.
These are as computed by FindKummerCoordinatesGenus3. }
    K<f0,f1,f2,f3,f4> := FunctionField(Rationals(), 5);
    Q<x1,y1,x2,y2,x3,y3> := PolynomialRing(K, 6);

    kummer_coordinates :=
        [
            x1^3*x2*y2 - x1^3*x2*y3 - x1^3*y2*x3 + x1^3*x3*y3 - x1^2*y1*x2^2 +
                2*x1^2*y1*x2*x3 - x1^2*y1*x3^2 - x1^2*x2^2*y2 + 2*x1^2*x2^2*y3 -
                x1^2*x2*y2*x3 - x1^2*x2*x3*y3 + 2*x1^2*y2*x3^2 - x1^2*x3^2*y3 +
                x1*y1*x2^3 - x1*y1*x2^2*x3 - x1*y1*x2*x3^2 + x1*y1*x3^3 - x1*x2^3*y3 +
                2*x1*x2^2*y2*x3 - x1*x2^2*x3*y3 - x1*x2*y2*x3^2 + 2*x1*x2*x3^2*y3 -
                x1*y2*x3^3 - y1*x2^3*x3 + 2*y1*x2^2*x3^2 - y1*x2*x3^3 + x2^3*x3*y3 -
                x2^2*y2*x3^2 - x2^2*x3^2*y3 + x2*y2*x3^3,
            2*f3*f4*x1^3*x2^3*x3 + 2*f2*f4*x1^3*x2^3 - 2*f3*f4*x1^3*x2^2*x3^2 +
                (-2*f2*f4 + f3^2)*x1^3*x2^2*x3 + f2*f3*x1^3*x2^2 + 2*f3*f4*x1^3*x2*x3^3
                + (-2*f2*f4 + f3^2)*x1^3*x2*x3^2 + f1*f3*x1^3*x2 - f3*x1^3*y2^2*y3 -
                f3*x1^3*y2*y3^2 + 2*f2*f4*x1^3*x3^3 + f2*f3*x1^3*x3^2 + f1*f3*x1^3*x3 +
                2*f0*f3*x1^3 + f3*x1^2*y1*x2*y2*y3 - f3*x1^2*y1*x2*y3^2 -
                f3*x1^2*y1*y2^2*x3 - f2*x1^2*y1*y2^2 + f3*x1^2*y1*y2*x3*y3 +
                2*f2*x1^2*y1*y2*y3 - f2*x1^2*y1*y3^2 - 2*f3*f4*x1^2*x2^3*x3^2 +
                (-2*f2*f4 + f3^2)*x1^2*x2^3*x3 + f2*f3*x1^2*x2^3 -
                2*f3*f4*x1^2*x2^2*x3^3 + (6*f2*f4 - 6*f3^2)*x1^2*x2^2*x3^2 -
                2*f2*f3*x1^2*x2^2*x3 + (-2*f1*f3 + 2*f2^2)*x1^2*x2^2 +
                2*f3*x1^2*x2*y2*y3^2 + (-2*f2*f4 + f3^2)*x1^2*x2*x3^3 -
                2*f2*f3*x1^2*x2*x3^2 - 2*f2^2*x1^2*x2*x3 + (-2*f0*f3 + f1*f2)*x1^2*x2 +
                2*f3*x1^2*y2^2*x3*y3 - f2*x1^2*y2^2*y3 - f2*x1^2*y2*y3^2 +
                f2*f3*x1^2*x3^3 + (-2*f1*f3 + 2*f2^2)*x1^2*x3^2 + (-2*f0*f3 +
                f1*f2)*x1^2*x3 + 2*f0*f2*x1^2 + f3*x1*y1*x2^2*y2*y3 +
                2*f3*x1*y1*x2^2*y3^2 - 6*f3*x1*y1*x2*y2*x3*y3 - 2*f2*x1*y1*x2*y2*y3 +
                2*f2*x1*y1*x2*y3^2 + 2*f3*x1*y1*y2^2*x3^2 + 2*f2*x1*y1*y2^2*x3 +
                f3*x1*y1*y2*x3^2*y3 - 2*f2*x1*y1*y2*x3*y3 + 2*f3*f4*x1*x2^3*x3^3 +
                (-2*f2*f4 + f3^2)*x1*x2^3*x3^2 + f1*f3*x1*x2^3 - f3*x1*x2^2*y2*y3^2 +
                (-2*f2*f4 + f3^2)*x1*x2^2*x3^3 - 2*f2*f3*x1*x2^2*x3^2 -
                2*f2^2*x1*x2^2*x3 + (-2*f0*f3 + f1*f2)*x1*x2^2 + 2*f2*x1*x2*y2*y3^2 -
                2*f2^2*x1*x2*x3^2 + (6*f0*f3 - 6*f1*f2)*x1*x2*x3 - 2*f0*f2*x1*x2 -
                f3*x1*y2^2*x3^2*y3 + 2*f2*x1*y2^2*x3*y3 + f1*f3*x1*x3^3 + (-2*f0*f3 +
                f1*f2)*x1*x3^2 - 2*f0*f2*x1*x3 - f3*y1^2*x2^3*y3 - f3*y1^2*x2^2*y2*x3 -
                f2*y1^2*x2^2*y2 + 2*f3*y1^2*x2^2*x3*y3 - f2*y1^2*x2^2*y3 +
                2*f3*y1^2*x2*y2*x3^2 + 2*f2*y1^2*x2*y2*x3 - f3*y1^2*x2*x3^2*y3 +
                2*f2*y1^2*x2*x3*y3 - f3*y1^2*y2*x3^3 - f2*y1^2*y2*x3^2 - f2*y1^2*x3^2*y3
                - f3*y1*x2^3*y3^2 + f3*y1*x2^2*y2*x3*y3 + 2*f2*y1*x2^2*y2*y3 -
                f2*y1*x2^2*y3^2 + f3*y1*x2*y2*x3^2*y3 - 2*f2*y1*x2*y2*x3*y3 -
                f3*y1*y2^2*x3^3 - f2*y1*y2^2*x3^2 + 2*f2*y1*y2*x3^2*y3 +
                2*f2*f4*x2^3*x3^3 + f2*f3*x2^3*x3^2 + f1*f3*x2^3*x3 + 2*f0*f3*x2^3 -
                f2*x2^2*y2*y3^2 + f2*f3*x2^2*x3^3 + (-2*f1*f3 + 2*f2^2)*x2^2*x3^2 +
                (-2*f0*f3 + f1*f2)*x2^2*x3 + 2*f0*f2*x2^2 + f1*f3*x2*x3^3 + (-2*f0*f3 +
                f1*f2)*x2*x3^2 - 2*f0*f2*x2*x3 - f2*y2^2*x3^2*y3 + 2*f0*f3*x3^3 +
                2*f0*f2*x3^2,
            -2*f4*x1^3*x2^3 + 2*f4*x1^3*x2^2*x3 - f3*x1^3*x2^2 + 2*f4*x1^3*x2*x3^2 +
                2*f3*x1^3*x2*x3 - 2*f4*x1^3*x3^3 - f3*x1^3*x3^2 + x1^2*y1*y2^2 -
                2*x1^2*y1*y2*y3 + x1^2*y1*y3^2 + 2*f4*x1^2*x2^3*x3 - f3*x1^2*x2^3 -
                6*f4*x1^2*x2^2*x3^2 - 2*f2*x1^2*x2^2 + 2*f4*x1^2*x2*x3^3 +
                2*f2*x1^2*x2*x3 - f1*x1^2*x2 + x1^2*y2^2*y3 + x1^2*y2*y3^2 -
                f3*x1^2*x3^3 - 2*f2*x1^2*x3^2 - f1*x1^2*x3 - 2*f0*x1^2 +
                2*x1*y1*x2*y2*y3 - 2*x1*y1*x2*y3^2 - 2*x1*y1*y2^2*x3 + 2*x1*y1*y2*x3*y3
                + 2*f4*x1*x2^3*x3^2 + 2*f3*x1*x2^3*x3 + 2*f4*x1*x2^2*x3^3 +
                2*f2*x1*x2^2*x3 - f1*x1*x2^2 - 2*x1*x2*y2*y3^2 + 2*f3*x1*x2*x3^3 +
                2*f2*x1*x2*x3^2 + 6*f1*x1*x2*x3 + 2*f0*x1*x2 - 2*x1*y2^2*x3*y3 -
                f1*x1*x3^2 + 2*f0*x1*x3 + y1^2*x2^2*y2 + y1^2*x2^2*y3 - 2*y1^2*x2*y2*x3
                - 2*y1^2*x2*x3*y3 + y1^2*y2*x3^2 + y1^2*x3^2*y3 - 2*y1*x2^2*y2*y3 +
                y1*x2^2*y3^2 + 2*y1*x2*y2*x3*y3 + y1*y2^2*x3^2 - 2*y1*y2*x3^2*y3 -
                2*f4*x2^3*x3^3 - f3*x2^3*x3^2 + x2^2*y2*y3^2 - f3*x2^2*x3^3 -
                2*f2*x2^2*x3^2 - f1*x2^2*x3 - 2*f0*x2^2 - f1*x2*x3^2 + 2*f0*x2*x3 +
                y2^2*x3^2*y3 - 2*f0*x3^2,
            -2*f3*f4^2*x1^3*x2^3*x3^2 - 2*f1*f4^2*x1^3*x2^3 - 2*f3*f4^2*x1^3*x2^2*x3^3 -
                4*f3^2*f4*x1^3*x2^2*x3^2 + (2*f1*f4^2 - 2*f2*f3*f4)*x1^3*x2^2*x3 -
                2*f1*f3*f4*x1^3*x2^2 + 2*f3*f4*x1^3*x2*y2*y3^2 + (2*f1*f4^2 -
                2*f2*f3*f4)*x1^3*x2*x3^2 - 2*f0*f3*f4*x1^3*x2 + 2*f3*f4*x1^3*y2^2*x3*y3
                - 2*f1*f4^2*x1^3*x3^3 - 2*f1*f3*f4*x1^3*x3^2 - 2*f0*f3*f4*x1^3*x3 +
                f3*f4*x1^2*y1*x2^2*y3^2 - 2*f3*f4*x1^2*y1*x2*y2*x3*y3 +
                f3*f4*x1^2*y1*y2^2*x3^2 + f1*f4*x1^2*y1*y2^2 - 2*f1*f4*x1^2*y1*y2*y3 +
                f1*f4*x1^2*y1*y3^2 - 2*f3*f4^2*x1^2*x2^3*x3^3 - 4*f3^2*f4*x1^2*x2^3*x3^2
                + (2*f1*f4^2 - 2*f2*f3*f4)*x1^2*x2^3*x3 - 2*f1*f3*f4*x1^2*x2^3 +
                f3*f4*x1^2*x2^2*y2*y3^2 - 4*f3^2*f4*x1^2*x2^2*x3^3 + (-6*f1*f4^2 -
                6*f3^3)*x1^2*x2^2*x3^2 - 4*f2*f3^2*x1^2*x2^2*x3 + (-2*f0*f3*f4 -
                2*f1*f2*f4 - 2*f1*f3^2)*x1^2*x2^2 + 3*f3^2*x1^2*x2*y2*y3^2 + (2*f1*f4^2
                - 2*f2*f3*f4)*x1^2*x2*x3^3 - 4*f2*f3^2*x1^2*x2*x3^2 + (2*f0*f3*f4 +
                2*f1*f2*f4 - 2*f1*f3^2 - 2*f2^2*f3)*x1^2*x2*x3 + (-3*f0*f3^2 - f1^2*f4 -
                f1*f2*f3)*x1^2*x2 + f3*f4*x1^2*y2^2*x3^2*y3 + 3*f3^2*x1^2*y2^2*x3*y3 +
                (f1*f4 + f2*f3)*x1^2*y2^2*y3 + (f1*f4 + f2*f3)*x1^2*y2*y3^2 -
                2*f1*f3*f4*x1^2*x3^3 + (-2*f0*f3*f4 - 2*f1*f2*f4 - 2*f1*f3^2)*x1^2*x3^2
                + (-3*f0*f3^2 - f1^2*f4 - f1*f2*f3)*x1^2*x3 + (-2*f0*f1*f4 -
                2*f0*f2*f3)*x1^2 + 2*f3*f4*x1*y1*x2^3*y3^2 - 2*f3*f4*x1*y1*x2^2*y2*x3*y3
                + 3*f3^2*x1*y1*x2^2*y3^2 - 2*f3*f4*x1*y1*x2*y2*x3^2*y3 -
                6*f3^2*x1*y1*x2*y2*x3*y3 + (2*f1*f4 - 2*f2*f3)*x1*y1*x2*y2*y3 +
                (-2*f1*f4 + 2*f2*f3)*x1*y1*x2*y3^2 + 2*f3*f4*x1*y1*y2^2*x3^3 +
                3*f3^2*x1*y1*y2^2*x3^2 + (-2*f1*f4 + 2*f2*f3)*x1*y1*y2^2*x3 +
                f1*f3*x1*y1*y2^2 + (2*f1*f4 - 2*f2*f3)*x1*y1*y2*x3*y3 -
                2*f1*f3*x1*y1*y2*y3 + f1*f3*x1*y1*y3^2 + (2*f1*f4^2 -
                2*f2*f3*f4)*x1*x2^3*x3^2 - 2*f0*f3*f4*x1*x2^3 + (2*f1*f4^2 -
                2*f2*f3*f4)*x1*x2^2*x3^3 - 4*f2*f3^2*x1*x2^2*x3^2 + (2*f0*f3*f4 +
                2*f1*f2*f4 - 2*f1*f3^2 - 2*f2^2*f3)*x1*x2^2*x3 + (-3*f0*f3^2 - f1^2*f4 -
                f1*f2*f3)*x1*x2^2 + (-2*f1*f4 + 2*f2*f3)*x1*x2*y2*y3^2 + (2*f0*f3*f4 +
                2*f1*f2*f4 - 2*f1*f3^2 - 2*f2^2*f3)*x1*x2*x3^2 + (6*f0*f3^2 + 6*f1^2*f4
                - 6*f1*f2*f3)*x1*x2*x3 + (2*f0*f1*f4 - 2*f0*f2*f3 - 2*f1^2*f3)*x1*x2 +
                (-2*f1*f4 + 2*f2*f3)*x1*y2^2*x3*y3 + 2*f1*f3*x1*y2^2*y3 +
                2*f1*f3*x1*y2*y3^2 - 2*f0*f3*f4*x1*x3^3 + (-3*f0*f3^2 - f1^2*f4 -
                f1*f2*f3)*x1*x3^2 + (2*f0*f1*f4 - 2*f0*f2*f3 - 2*f1^2*f3)*x1*x3 -
                4*f0*f1*f3*x1 + 2*f3*f4*y1^2*x2^3*x3*y3 + f3*f4*y1^2*x2^2*y2*x3^2 +
                f1*f4*y1^2*x2^2*y2 + f3*f4*y1^2*x2^2*x3^2*y3 + 3*f3^2*y1^2*x2^2*x3*y3 +
                (f1*f4 + f2*f3)*y1^2*x2^2*y3 + 2*f3*f4*y1^2*x2*y2*x3^3 +
                3*f3^2*y1^2*x2*y2*x3^2 + (-2*f1*f4 + 2*f2*f3)*y1^2*x2*y2*x3 +
                f1*f3*y1^2*x2*y2 + (-2*f1*f4 + 2*f2*f3)*y1^2*x2*x3*y3 +
                2*f1*f3*y1^2*x2*y3 - 6*f3*y1^2*y2^2*y3^2 + (f1*f4 + f2*f3)*y1^2*y2*x3^2
                + 2*f1*f3*y1^2*y2*x3 + 3*f0*f3*y1^2*y2 + f1*f4*y1^2*x3^2*y3 +
                f1*f3*y1^2*x3*y3 + 3*f0*f3*y1^2*y3 - 2*f1*f4*y1*x2^2*y2*y3 + (f1*f4 +
                f2*f3)*y1*x2^2*y3^2 + (2*f1*f4 - 2*f2*f3)*y1*x2*y2*x3*y3 -
                2*f1*f3*y1*x2*y2*y3 + 2*f1*f3*y1*x2*y3^2 + (f1*f4 + f2*f3)*y1*y2^2*x3^2
                + 2*f1*f3*y1*y2^2*x3 + 3*f0*f3*y1*y2^2 - 2*f1*f4*y1*y2*x3^2*y3 -
                2*f1*f3*y1*y2*x3*y3 - 6*f0*f3*y1*y2*y3 + 3*f0*f3*y1*y3^2 -
                2*f1*f4^2*x2^3*x3^3 - 2*f1*f3*f4*x2^3*x3^2 - 2*f0*f3*f4*x2^3*x3 +
                f1*f4*x2^2*y2*y3^2 - 2*f1*f3*f4*x2^2*x3^3 + (-2*f0*f3*f4 - 2*f1*f2*f4 -
                2*f1*f3^2)*x2^2*x3^2 + (-3*f0*f3^2 - f1^2*f4 - f1*f2*f3)*x2^2*x3 +
                (-2*f0*f1*f4 - 2*f0*f2*f3)*x2^2 + f1*f3*x2*y2*y3^2 - 2*f0*f3*f4*x2*x3^3
                + (-3*f0*f3^2 - f1^2*f4 - f1*f2*f3)*x2*x3^2 + (2*f0*f1*f4 - 2*f0*f2*f3 -
                2*f1^2*f3)*x2*x3 - 4*f0*f1*f3*x2 + f1*f4*y2^2*x3^2*y3 + f1*f3*y2^2*x3*y3
                + 3*f0*f3*y2^2*y3 + 3*f0*f3*y2*y3^2 + (-2*f0*f1*f4 - 2*f0*f2*f3)*x3^2 -
                4*f0*f1*f3*x3 - 6*f0^2*f3,
            x1^3*x2*y2*y3 - x1^3*x2*y3^2 - x1^3*y2^2*x3 + x1^3*y2*x3*y3 -
                x1^2*y1*x2^2*y3 + x1^2*y1*x2*y2*x3 + x1^2*y1*x2*x3*y3 - x1^2*y1*y2*x3^2
                - x1^2*x2^2*y2*y3 + 2*x1^2*x2^2*y3^2 - 2*x1^2*x2*y2*x3*y3 +
                2*x1^2*y2^2*x3^2 - x1^2*y2*x3^2*y3 + x1*y1*x2^3*y3 + x1*y1*x2^2*y2*x3 -
                2*x1*y1*x2^2*x3*y3 - 2*x1*y1*x2*y2*x3^2 + x1*y1*x2*x3^2*y3 +
                x1*y1*y2*x3^3 - x1*x2^3*y3^2 + x1*x2^2*y2*x3*y3 + x1*x2*y2*x3^2*y3 -
                x1*y2^2*x3^3 - y1^2*x2^3*x3 + 2*y1^2*x2^2*x3^2 - y1^2*x2*x3^3 +
                y1*x2^3*x3*y3 - y1*x2^2*y2*x3^2 - y1*x2^2*x3^2*y3 + y1*x2*y2*x3^3,
            -2*f4*x1^3*x2^3*y3 + 2*f4*x1^3*x2^2*x3*y3 - f3*x1^3*x2^2*y3 +
                2*f4*x1^3*x2*y2*x3^2 + f3*x1^3*x2*y2*x3 + f3*x1^3*x2*x3*y3 -
                2*f4*x1^3*y2*x3^3 - f3*x1^3*y2*x3^2 - 2*f4*x1^2*y1*x2^2*x3^2 -
                f3*x1^2*y1*x2^2*x3 - f3*x1^2*y1*x2*x3^2 - 2*f2*x1^2*y1*x2*x3 -
                f1*x1^2*y1*x2 + x1^2*y1*y2^2*y3 + x1^2*y1*y2*y3^2 - f1*x1^2*y1*x3 -
                2*f0*x1^2*y1 + 2*f4*x1^2*x2^3*x3*y3 - f3*x1^2*x2^3*y3 -
                2*f4*x1^2*x2^2*y2*x3^2 - f3*x1^2*x2^2*y2*x3 - 2*f4*x1^2*x2^2*x3^2*y3 +
                2*f3*x1^2*x2^2*x3*y3 - 2*f2*x1^2*x2^2*y3 + 2*f4*x1^2*x2*y2*x3^3 +
                2*f3*x1^2*x2*y2*x3^2 + 2*f2*x1^2*x2*y2*x3 + f1*x1^2*x2*y2 -
                f3*x1^2*x2*x3^2*y3 + 2*f2*x1^2*x2*x3*y3 - f1*x1^2*x2*y3 -
                f3*x1^2*y2*x3^3 - 2*f2*x1^2*y2*x3^2 - f1*x1^2*y2*x3 + f1*x1^2*x3*y3 +
                2*f4*x1*y1*x2^3*x3^2 + f3*x1*y1*x2^3*x3 + 2*f4*x1*y1*x2^2*x3^3 +
                2*f3*x1*y1*x2^2*x3^2 + 2*f2*x1*y1*x2^2*x3 + f1*x1*y1*x2^2 -
                2*x1*y1*x2*y2*y3^2 + f3*x1*y1*x2*x3^3 + 2*f2*x1*y1*x2*x3^2 +
                2*f1*x1*y1*x2*x3 + 2*f0*x1*y1*x2 - 2*x1*y1*y2^2*x3*y3 + f1*x1*y1*x3^2 +
                2*f0*x1*y1*x3 + f3*x1*x2^3*x3*y3 - f3*x1*x2^2*y2*x3^2 -
                2*f2*x1*x2^2*y2*x3 - f1*x1*x2^2*y2 - f3*x1*x2^2*x3^2*y3 +
                2*f2*x1*x2^2*x3*y3 - f1*x1*x2^2*y3 + f3*x1*x2*y2*x3^3 +
                2*f2*x1*x2*y2*x3^2 + 2*f1*x1*x2*y2*x3 + 2*f0*x1*x2*y2 -
                2*f2*x1*x2*x3^2*y3 + 2*f1*x1*x2*x3*y3 - 2*f0*x1*x2*y3 - f1*x1*y2*x3^2 -
                2*f0*x1*y2*x3 - f1*x1*x3^2*y3 + 2*f0*x1*x3*y3 + y1^2*x2^2*y2*y3 -
                2*y1^2*x2*y2*x3*y3 + y1^2*y2*x3^2*y3 - 2*f4*y1*x2^3*x3^3 -
                f3*y1*x2^3*x3^2 + y1*x2^2*y2*y3^2 - f3*y1*x2^2*x3^3 - 2*f2*y1*x2^2*x3^2
                - f1*y1*x2^2*x3 - f1*y1*x2*x3^2 - 2*f0*y1*x2*x3 + y1*y2^2*x3^2*y3 -
                f1*x2^2*y2*x3 - 2*f0*x2^2*y2 + f1*x2^2*x3*y3 + f1*x2*y2*x3^2 +
                2*f0*x2*y2*x3 - f1*x2*x3^2*y3 + 2*f0*x2*x3*y3 - 2*f0*x3^2*y3,
            x1^2*y2^2 - 2*x1^2*y2*y3 + x1^2*y3^2 - 2*x1*y1*x2*y2 + 2*x1*y1*x2*y3 +
                2*x1*y1*y2*x3 - 2*x1*y1*x3*y3 + 2*x1*x2*y2*y3 - 2*x1*x2*y3^2 -
                2*x1*y2^2*x3 + 2*x1*y2*x3*y3 + y1^2*x2^2 - 2*y1^2*x2*x3 + y1^2*x3^2 -
                2*y1*x2^2*y3 + 2*y1*x2*y2*x3 + 2*y1*x2*x3*y3 - 2*y1*y2*x3^2 + x2^2*y3^2
                - 2*x2*y2*x3*y3 + y2^2*x3^2,
            -x1^3*y2^2 + 2*x1^3*y2*y3 - x1^3*y3^2 + x1^2*y1*x2*y2 - x1^2*y1*x2*y3 -
                x1^2*y1*y2*x3 + x1^2*y1*x3*y3 - x1^2*x2*y2*y3 + x1^2*x2*y3^2 +
                x1^2*y2^2*x3 - x1^2*y2*x3*y3 + x1*y1*x2^2*y2 - x1*y1*x2^2*y3 -
                x1*y1*y2*x3^2 + x1*y1*x3^2*y3 - x1*x2^2*y2*y3 + x1*x2^2*y3^2 +
                x1*y2^2*x3^2 - x1*y2*x3^2*y3 - y1^2*x2^3 + y1^2*x2^2*x3 + y1^2*x2*x3^2 -
                y1^2*x3^3 + 2*y1*x2^3*y3 - y1*x2^2*y2*x3 - y1*x2^2*x3*y3 - y1*x2*y2*x3^2
                - y1*x2*x3^2*y3 + 2*y1*y2*x3^3 - x2^3*y3^2 + x2^2*y2*x3*y3 +
                x2*y2*x3^2*y3 - y2^2*x3^3
        ];
    return kummer_coordinates;
end intrinsic;


intrinsic KummerCoordinatesGenus3Superelliptic(f::RngUPolElt) -> SeqEnum
{ Specialises the Kummer coordinates at f. }
    kummer_coordinates := KummerCoordinatesGenus3Superelliptic();

    Q2 := Universe(kummer_coordinates);
    K2 := BaseRing(Q2);

    P := Parent(f);
    K := BaseRing(P);
    Q<x1,y1,x2,y2,x3,y3> := PolynomialRing(K, 6);

    assert Degree(f) eq 4;

    f_coeffs := [Coefficient(f, i) : i in [0..4]];

    spec_hom := hom<Q2->Q | hom<K2->K | f_coeffs>, x1,y1,x2,y2,x3,y3>;
    return [spec_hom(poly) : poly in kummer_coordinates];
end intrinsic;