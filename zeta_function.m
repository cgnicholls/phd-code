
intrinsic ZetaFunctionOfJacobian(f::RngUPolElt, p::RngIntElt) -> RngUPolElt
    { Computes the zeta function of the Jacobian of the curve y^2 = f(x). }
    C := HyperellipticCurve(f);
    g := Genus(C);
    while p in BadPrimesIntegralModel(f) do
        p := NextPrime(p);
    end while;
    // We use the formula as in 'Arithmetic of Curves' by Miller on page 66.
    S<t> := PolynomialRing(Rationals());
    genfun := 0;
    for i in [1..g] do
        genfun := genfun + #Points(ChangeRing(C, GF(p^i))) * t^i / i;
    end for;

    approximateexp := 1;
    for i in [1..g] do
        approximateexp := approximateexp + genfun^i / Factorial(i);
    end for;
    poly := (1-t)*(1-p*t) * (approximateexp);

    PJ := t^(2*g);
    for i in [1..g] do
        PJ := PJ + Coefficient(poly, i) * t^(2*g-i);
    end for;
    for i in [1..g-1] do
        PJ := PJ + Coefficient(poly, i) * t^i * p^(g-i);
    end for;
    PJ := PJ + p^g;

    return PJ;
end intrinsic;

compute_roots_splitting_field := function(poly)
    Kfield := GaloisSplittingField(poly);
    roots := Roots(ChangeRing(poly, Kfield));
    return Kfield, roots;
end function;

compute_product := function(elts)
    result := Universe(elts)!1;
    for elt in elts do
        result *:= elt;
    end for;
    return result;
end function;

compute_char_frob_J_over_extension_with_roots := function(roots, n)
    PT<T> := PolynomialRing(Universe([root[1] : root in roots]));
    poly := compute_product([(T-root[1]^n)^root[2] : root in roots]);
    return ChangeRing(poly, Rationals());
end function;

// Returns the characteristic polynomial of the Jacobian of the curve over F_{p^n}.
compute_char_frob_J_over_extension := function(f, p, n)
    assert not p in BadPrimesIntegralModel(f);
    char_frob := ZetaFunctionOfJacobian(f, p);
    Kfield, roots := compute_roots_splitting_field(char_frob);

    return compute_char_frob_J_over_extension_with_roots(roots, n);
end function;

// Returns the values of n for which the characteristic polynomial of Frobenius
// is reducible over this extension for some n in [1..max_n].
check_simple_over_extensions := function(f, p, max_n)
    assert not p in BadPrimesIntegralModel(f);
    char_frob := ZetaFunctionOfJacobian(f, p);
    Kfield, roots := compute_roots_splitting_field(char_frob);

    return { n : n in [1..max_n] | not IsIrreducible(compute_char_frob_J_over_extension_with_roots(roots, n)) };
end function;

// Calls the above function for each p in ps, excluding bad primes.
check_simple_over_extensions_multiple_p := function(f, ps, max_n)
    ps := [p : p in ps | not p in BadPrimesIntegralModel(f)];
    
    successful_p := [];
    for p in ps do
        bad_n := check_simple_over_extensions(f, p, max_n);
        if #bad_n eq 0 then
            Append(~successful_p, p);
        end if;
    end for;
    return successful_p;
end function;

// Returns the possible roots of unity in a number field of degree degree.
possible_roots_of_unity_in_field := function(degree)
    return [n : n in [1..100*degree] | EulerPhi(n) le degree];
end function;

// We check whether the condition in the simple lemma holds. Let K = Q(alpha) be
// the simple extension where alpha is a root of P_J. If all strict subfields of
// K are real, and zeta * root(p) is not a root of P_J for all roots of unity
// zeta in K, then J is geometrically simple.
check_geometrically_simple_at_p := function(f, p)
    assert not p in BadPrimesIntegralModel(f);
    char_frob := ZetaFunctionOfJacobian(f, p);
    if not IsIrreducible(char_frob) then
        return false;
    end if;
    Kfield := NumberField(char_frob);
    subfields := [subfield[1] : subfield in Subfields(Kfield) | Degree(subfield[1]) lt Degree(Kfield)];
    if false in {IsTotallyReal(subfield) : subfield in subfields} then
        return false;
    end if;

    // We can test whether zeta * root(p) is a root of P_J as follows. Firstly,
    // note that the only possible n where there can be an nth root of unity in
    // K are those where EulerPhi(n) le Degree(P_J).
    // Then we have to check whether the minimal polynomial of zeta * root(p)
    // and the polynomial P_J share a root. We can check this using GCD.
    P<x> := PolynomialRing(Rationals());
    return {GCD(x^(2*n) - p^n, char_frob) : n in possible_roots_of_unity_in_field(Degree(char_frob))} eq {1};
end function;


intrinsic IsGeometricallySimple(f::RngUPolElt : max_tests := 10) -> BoolElt, RngIntElt
{ Returns whether the method described in my PhD thesis determines that the curve y^2 = f(x)
has geometrically simple Jacobian. If confirmed true, then returns true together with the prime
that witnessed its simplicity. If this returns false, that does not mean the Jacobian is
geometrically simple. }

    bad_primes := BadPrimesIntegralModel(f);
    p := 2;
    num_checks := 0;
    while num_checks lt max_tests do
        p := NextPrime(p);
        if p in bad_primes then
            continue;
        end if;
        try
            if check_geometrically_simple_at_p(f, p) then
                return true, p;
            end if;
            num_checks +:= 1;
        catch e
            print e;
        end try;
    end while;
    return false;
end intrinsic;


intrinsic IsGeometricallySimpleLeprevost(f::RngUPolElt : max_tests := 10) -> BoolElt, RngIntElt
{ Returns whether the method due to Leprevost determines that the curve y^2 = f(x)
has geometrically simple Jacobian. We just check for max_tests good primes whether
the Galois group of the zeta function is the Dihedral group of order 8. }
    p := 2;
    bad_primes := BadPrimesIntegralModel(f);
    num_checks := 0;
    D8 := DihedralGroup(4);
    while num_checks lt max_tests do
        p := NextPrime(p);
        if p in bad_primes then
            continue;
        end if;
        try
            zeta_function := ZetaFunctionOfJacobian(f, p);
            galois_group := GaloisGroup(zeta_function);
            if IsIsomorphic(galois_group, D8) then
                return true, p;
            end if;
            num_checks +:= 1;
        catch e
            print e;
        end try;
    end while;
    return false;
end intrinsic;
