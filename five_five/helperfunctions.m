// Reduce an expression in k1,k2,k3,k4 modulo the Kummer equation.
reduce := function(expr, kummeqn)
    // We just replace all occurrences of k2^2*k4^2 with the other terms of the
    // Kummer equation.
    //quot := (k2^2 - 4*k1*k3)*k4^2;
    quot := k2^2*k4^2;
    q, r := Quotrem(P!kummeqn, P!quot);
    lower := r;
    while true do
        q, r := Quotrem(expr, quot);
        expr := q * (-lower) + r;
        if q eq 0 then
            break;
        end if;
    end while;
    return expr;
end function;

reduceall := function(exprs, kummeqn)
    reducedexprs := [];
    for expr in exprs do
        reducedexprs := Append(reducedexprs, reduce(expr, kummeqn));
    end for;
    return reducedexprs;
end function;

vectorToPolynomial := function(vector, monomials)
    poly := 0;
    for i in [1..#monomials] do
        poly := poly + monomials[i] * vector[i];
    end for;
    return poly;
end function;

subspaceOfPolys := function(polys, monomials)
    V := VectorSpace(K, #monomials);
    vectors := [[MonomialCoefficient(poly, mon) : mon in monomials] : poly in
                                                  polys];
    return sub<V | vectors>, V;
end function;

degreencombinations := function(polys, n)
    _R := Universe(polys);
    _P := PolynomialRing(_R, #polys);
    degreenmonomials := MonomialsOfDegree(_P, n);
    h := hom<_P->_R | polys>;
    return [h(mon) : mon in degreenmonomials];
end function;

vectorSpaceForPolys := function(polys)
    monomials := {};
    for poly in polys do
        monomials := monomials join Set(Monomials(poly));
    end for;
    monomials := SetToSequence(monomials);
    V := VectorSpace(K, #monomials);
    return V, monomials;
end function;

polyToVector := function(poly, V, monomials)
    vector := [];
    for monomial in monomials do
        vector := Append(vector, MonomialCoefficient(poly, monomial));
    end for;
    return V!vector;
end function;

vectorToPoly := function(vector, monomials)
    poly := 0;
    for i in [1..#monomials] do
        poly := poly + vector[i] * monomials[i];
    end for;
    return poly;
end function;

linearRelations := function(polys)
    V, monomials := vectorSpaceForPolys(polys);
    M := Matrix([polyToVector(poly, V, monomials) : poly in polys]);
    nullspace := Nullspace(M);
    return nullspace, V, monomials;
end function;

// Check if two Igusa invariants are equal
checkEqualityIgusa := function(inv1, inv2)
    WP := WeightedProjectiveSpace(Rationals(), [1,2,3,4,5]);
    return (WP!inv1) eq (WP!inv2);
end function;

checkGeometricallyIsomorphic := function(curve1, curve2)
    I1 := IgusaInvariants(curve1);
    I2 := IgusaInvariants(curve2);
    return checkEqualityIgusa(I1, I2);
end function;
