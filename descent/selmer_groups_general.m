intrinsic MSelmerGroup(K::FldPad, m::RngIntElt) -> GrpAb, Map
{ Computes a group G isomorphic to K^* / K^*m, where K is a local field.
Returns G as well as a map from K^* to G. Also returns generators such that
the ith generator maps to G.i. }
    U, U_map := UnitGroup(K);

    m_selmer, qU := quo<U | m * U>;

    // Now compute the map K^* to G.
    m_selmer_image := function(alpha)
        U_img := qU(alpha @@ U_map);
        return U_img;
    end function;

    m_selmer_preimage := function(g)
        return K!U_map(g @@ qU);
    end function;

    m_selmer_map := map<K->m_selmer | x :-> m_selmer_image(x), y :-> m_selmer_preimage(y)>;

    return m_selmer, m_selmer_map;
end intrinsic;


intrinsic MSelmerGroup(Ap::RngUPolRes, m::RngIntElt) -> GrpAb, Map
{ Computes the m-Selmer group for the Qp-algebra Ap. Returns a group G isomorphic to the m-Selmer group,
together with a map Ap -> G. }
    modulus := Modulus(Ap);
    QpT := Parent(modulus);
    Qp := BaseRing(QpT);
    factors := [factor[1] : factor in Factorisation(modulus)];

    homs := [* *];
    inv_maps := [* *];
    ram_field_factors := [];
    m_selmer_factors := [];
    m_selmer_factors_maps := [* *];
    for factor in factors do
        field_factor := LocalField(Qp, factor);
        hom_Ap_field_factor := hom<Ap->field_factor | field_factor.1>;
        Append(~homs, hom_Ap_field_factor);
        ram_field_factor, ram_hom := RamifiedRepresentation(field_factor);
        Append(~ram_field_factors, ram_field_factor);
        Append(~inv_maps, Inverse(ram_hom));
        m_selmer_factor, m_selmer_factor_map := MSelmerGroup(ram_field_factor, m);
        Append(~m_selmer_factors, m_selmer_factor);
        Append(~m_selmer_factors_maps, m_selmer_factor_map);
    end for;

    ram_fields := CartesianProduct(ram_field_factors);

    m_selmer, incls, projs := DirectProduct(m_selmer_factors);

    m_selmer_image := function(elt)
        // Compute the image of elt in each factor of Ap = sum_i Qp[T] / factors[i].
        img_in_factors := ram_fields!<inv_maps[i](homs[i](elt)) : i in [1..#homs]>;
        assert { img_in_factors[i] eq 0 : i in [1..#img_in_factors] } eq { false };
        components := [incls[i](m_selmer_factors_maps[i](img_in_factors[i])) : i in [1..#img_in_factors]];
        return ComputeSum(components);
    end function;

    m_selmer_map := map<Ap->m_selmer | x :-> m_selmer_image(x)>;

    return m_selmer, m_selmer_map;
end intrinsic;


intrinsic PrimesAboveElements(S::SeqEnum, K::FldNum) -> SeqEnum
{ Returns the prime ideals that lie above the elements in S. }
    OK := Integers(K);
    primes := {};
    for s in S do
        factorisation := Factorisation(ideal<OK | s>);
        primes join:= {factor[1] : factor in factorisation};
    end for;
    return SetToSequence(primes);
end intrinsic;

intrinsic PrimesAboveElements(S::SeqEnum, K::FldRat) -> SeqEnum
{}
    return PrimesAboveElements(S, RationalsAsNumberField());
end intrinsic;


intrinsic ProductOfIdeals(ideals::SeqEnum, exponents::SeqEnum) -> RngOrdIdl
{ Returns the product of the ideals to the given exponents. }
    return Product([ideals[i]^exponents[i] : i in [1..#exponents]]);
end intrinsic;


intrinsic ProductWithExponents(xs::SeqEnum, es::SeqEnum) -> RngElt
{ Computes the product prod_i xs[i]^es[i]. }
    return Product([xs[i]^es[i] : i in [1..#xs]]);
end intrinsic;


intrinsic IsLinearCombination(x::RngIntElt, y::RngIntElt, z::RngIntElt) -> BoolElt, RngIntElt, RngIntElt
{ Returns whether z is an integral linear combination of x and y. That is, if there
are integers a and b such that z = a * x + b * y. If so, also returns a, b.}
    g := GCD(x, y);
    if IsDivisibleBy(z, g) then
        q := z div g;
        _, a, b := XGCD(x, y);
        assert a * q * x + b * q * y eq z;
        return true, a * q, b * q;
    end if;
    return false;
end intrinsic;


compute_x_for_e := function(e, fij, sj, m)
    // This function computes the vector x such that
    // sum_i e[i] * f_ij = x[j] * m + sj[j] * y[j].
    x := [];
    t := Matrix(e) * fij;
    for j in [1..Ncols(fij)] do
        _, xj, _ := IsLinearCombination(m, sj[j], t[1][j]);
        Append(~x, xj);
    end for;
    return x;
end function;


intrinsic BasisModM(gens::SeqEnum, m::RngIntElt) -> SeqEnum
{ Takes a subspace of Z^n generated by gens and returns a basis for
the subspace with coefficients reduced modulo m. }
    n := Ncols(Matrix(gens));
    Zm := quo<Integers() | m * Integers()>;
    Vspace := RSpace(Zm, n);
    basis := Basis(sub<Vspace | [Vspace!gen : gen in gens]>);

    return [ChangeRing(v, Integers()) : v in basis];
end intrinsic;


intrinsic ComputeSelmerExponents(primes::SeqEnum, m::RngIntElt) -> SeqEnum
{ Let primes be the primes P1, .., Pn. Let C1, .., Cg generate the class group, and suppose
Pi = prod Ci^f_ij for each i. This function computes all vectors (e1, .., en) such that
sum e_i f_ij = 0 mod gcd(s_j, m), where s_j is the order of C_j. }
    OK := Ring(Universe(primes));
    K := FieldOfFractions(OK);

    CK, CK_map := ClassGroup(K);

    fij := Matrix([Eltseq(Pi @@ CK_map) : Pi in primes]);

    sj := [Order(CK.i) : i in [1..#Generators(CK)]];

    moduli := [GCD(sj[i], m) : i in [1..#sj]];

    e_basis := NullspaceForModuli(fij, moduli);
    e_basis := BasisModM(e_basis, m);

    xs := [compute_x_for_e(e, fij, sj, m) : e in e_basis];

    CK_ideals := [CK_map(CK.i) : i in [1..#Generators(CK)]];

    Is := [ProductOfIdeals(CK_ideals, x) : x in xs];

    Pes := [ProductOfIdeals(primes, Eltseq(e)) : e in e_basis];

    alphas := [];
    for i in [1..#Is] do
        _, alpha := IsPrincipal(Pes[i] / Is[i]^m);
        Append(~alphas, K!alpha);
    end for;

    return e_basis, alphas;
end intrinsic;


intrinsic TorsionSubgroup(G::GrpAb, m::RngIntElt) -> GrpAb
{ Returns G[m], the subgroup of G of elements with order dividing m. }
    mult_map := hom<G->G | [G.i->m*G.i : i in [1..#Generators(G)]]>;
    return Kernel(mult_map);
end intrinsic;


intrinsic IsIdealMthPower(I::RngOrdFracIdl, m::RngIntElt) -> BoolElt, RngOrdIdl
{ Returns whether the ideal I is an mth power. If so, also returns J such that I = J^m. }
    K := FieldOfFractions(Ring(Parent(I)));
    OK := Integers(K);
    factorisation := Factorisation(I);
    factors := [factor[1] : factor in factorisation];
    exps := [factor[2] : factor in factorisation];
    J := ideal<OK | 1>;
    for i in [1..#exps] do
        if exps[i] mod m ne 0 then
            return false;
        end if;
        e := exps[i] div m;
        J *:= factors[i]^e;
    end for;
    assert J^m eq I;
    return true, J;
end intrinsic;


intrinsic RepresentativeInOKModMthPowers(OK::RngOrd, alpha::RngElt, m::RngIntElt) -> RngElt
{ Returns alpha2 in OK such that alpha / alpha2 is an mth power in K. }
    den := Denominator(alpha);
    return alpha * den^m;
end intrinsic;


intrinsic ClassGroupTorsion(K::Fld, m::RngIntElt) -> GrpAb, Map
{ Returns an abelian group G isomorphic to C[m], where C is the class group of K, together
with a map from G to ideals of the ring of integers of K. }
    CK, CK_map := ClassGroup(K);
    CK_m := TorsionSubgroup(CK, m);

    OK := Integers(K);

    inverse_map := function(I)
        // This map sends an ideal to its image in the group CK_m.
        return CK_m!(I @@ CK_map);
    end function;

    CK_m_map := map<CK_m->PowerIdeal(OK) | x :-> CK_map(CK!x), y :-> inverse_map(y)>;

    return CK_m, CK_m_map;
end intrinsic;


intrinsic ComputeKerPhi(primes::SeqEnum, m::RngIntElt) -> GrpAb, Map, SeqEnum
{ Computes the kernel of the map phi for the m-Selmer group. Computes the image of
alpha in the Selmer group, provided that (alpha) = I^m for some ideal I. }
    OK := Ring(Universe(primes));
    K := FieldOfFractions(OK);

    CK_m, CK_m_map := ClassGroupTorsion(K, m);
    CK_m_ideals := [CK_m_map(CK_m.i) : i in [1..#Generators(CK_m)]];

    betas := [];
    for i in [1..#Generators(CK_m)] do
        _, beta := IsPrincipal(CK_m_ideals[i]^m);
        Append(~betas, K!beta);
    end for;

    U, U_map := UnitGroup(OK);
    U_mU, q := quo<U | m * U>;

    ker_phi, incls, projs := DirectProduct([U_mU, CK_m]);

    ker_phi_image := function(alpha)
        alpha := RepresentativeInOKModMthPowers(OK, alpha, m);
        assert alpha in OK;

        // First assert that alpha does lie in the kernel of phi. That is, (alpha) = I^m for some ideal I.
        check, I := IsIdealMthPower(ideal<OK | alpha>, m);
        assert check;

        // Now write I as a product prod_i I_i^{f_i}, where I_i generate CK[m].
        img := I @@ CK_m_map;
        fi := Eltseq(img);

        check, gamma := IsPrincipal(I / ProductOfIdeals(CK_m_ideals, fi));
        assert check;

        u := alpha / gamma^m / Product([betas[i]^fi[i] : i in [1..#fi]]);
        assert IsUnit(u);

        U_elt := q(u @@ U_map);
        return incls[1](U_elt) + incls[2](img);
    end function;


    ker_phi_preimage := function(g)
        U_part := U_map(projs[1](g) @@ q);

        beta_part := ProductWithExponents(betas, Eltseq(projs[2](g)));
        
        return U_part * beta_part;
    end function;

    ker_phi_map := map<K->ker_phi | x :-> ker_phi_image(x), y :-> ker_phi_preimage(y)>;

    return ker_phi, ker_phi_map;
end intrinsic;


intrinsic ComputeImPhi(primes::SeqEnum, m::RngIntElt) -> GrpAb, Map
{ Computes the image of the map K^* -> ideals / ideals^m, given by alpha mapsto (alpha). }
    // First compute es that are a basis for the Selmer congruences
    e_basis, alphas := ComputeSelmerExponents(primes, m);

    Vspace := RSpace(Integers(), #primes);
    e_space := sub<Vspace | e_basis>;

    OK := Ring(Universe(primes));
    K := FieldOfFractions(OK);

    // We need the order of each basis element modulo m.
    basis_orders := [m div GCD(Eltseq(e)) : e in e_basis];

    // They might not all have order m. We should compute their actual order.
    im_phi := AbelianGroup(basis_orders);

    im_phi_image := function(alpha)
        // This function takes alpha in K^* to its image in im phi.
        // We first remove any ideal factors that occur with exponent divisible by m.
        factors := Factorisation(ideal<OK | alpha>);
        ideal_mod_mth_powers := ProductOfIdeals([factor[1] : factor in factors], [factor[2] mod m : factor in factors]);
        es := Vspace![Valuation(K!alpha, P) : P in primes];
        assert IsIdealMthPower(ideal_mod_mth_powers * ProductOfIdeals(primes, Eltseq(es))^-1, m);

        // We now want to write es in terms of our e_basis.
        assert es in e_space;
        e_solution := Solution(Matrix(e_basis), Vspace!es);

        beta := ProductWithExponents(alphas, Eltseq(e_solution));
        assert IsIdealMthPower(ideal<OK | alpha / beta>, m);

        return im_phi!Eltseq(e_solution);
    end function;

    im_phi_preimage := function(g)
        return ProductWithExponents(alphas, Eltseq(g));
    end function;

    im_phi_map := map<K->im_phi | x :-> im_phi_image(x), y :-> im_phi_preimage(y)>;

    return im_phi, im_phi_map;
end intrinsic;


intrinsic MSelmerGroup(primes::SeqEnum, m::RngIntElt) -> GrpAb, Map, SeqEnum
{ Returns a group isomorphic to K(primes, m). That is, the subgroup of
K^* / K^*m generated by the elements that are unramified outside primes. Returns
the group G, a map from K^* to G and a sequence of generators in K^* such that
gens[i] maps to G.i under the map. }
    OK := Ring(Universe(primes));
    K := FieldOfFractions(OK);

    ker_phi, ker_phi_map := ComputeKerPhi(primes, m);
    im_phi, im_phi_map := ComputeImPhi(primes, m);

    m_selmer, incls, projs := DirectProduct([ker_phi, im_phi]);

    compute_m_selmer_image := function(alpha)
        beta := im_phi_map(alpha) @@ im_phi_map;
        gamma := alpha / beta;
        ker_phi_part := ker_phi_map(gamma);

        return incls[1](ker_phi_part) + incls[2](im_phi_map(beta));
    end function;

    compute_m_selmer_preimage := function(g)
        ker_phi_preimage := projs[1](g) @@ ker_phi_map;
        im_phi_preimage := projs[2](g) @@ im_phi_map;
        return ker_phi_preimage * im_phi_preimage;
    end function;

    m_selmer_map := map<K->m_selmer | x :-> compute_m_selmer_image(x), y :-> compute_m_selmer_preimage(y)>;

    return m_selmer, m_selmer_map;
end intrinsic;


intrinsic CheckSelmerGroup(m_selmer::GrpAb, m_selmer_map::Map, m::RngIntElt) -> BoolElt
{ Checks whether the m-Selmer group is correct. In particular, checks whether there are any
nontrivial elements in the group that are actually mth powers. }
    K := Domain(m_selmer_map);
    for g in m_selmer do
        alpha := g @@ m_selmer_map;
        if g ne m_selmer!0 and IsNthPower(K!alpha, m) then
            print "Error: ", g, "maps to", alpha, ", which is a power of", m;
            return false;
        end if;
    end for;
    return true;
end intrinsic;


intrinsic NullspaceForModuli(M::Mtrx, moduli::SeqEnum) -> SeqEnum
{ For a matrix M and integer sequence moduli, we return a basis for the subspace of e satisfying
the congruences: sum_i e_i M_ij = 0 mod moduli[j]. This is a basis over Z, so the group generated
by moduli[j] times the jth standard basis vector is a subgroup. }
    assert #moduli eq Ncols(M);
    Vspace := RSpace(Integers(), Nrows(M));
    intersection := Vspace;    
    for j in [1..#moduli] do
        // Compute the jth column of M modulo moduli[j].
        Mj := ColumnSubmatrix(M, [j]);
        Zmj := quo<Integers() | moduli[j] * Integers()>;
        Mj := ChangeRing(Mj, Zmj);

        // Compute the kernel of Mj.
        basis_j := ChangeRing(Matrix(Basis(Kernel(Mj))), Integers());

        // Add on the standard basis vectors multiplied by moduli[j].
        basis_j := VerticalJoin(basis_j, moduli[j] * IdentityMatrix(Integers(), Ncols(basis_j)));

        // Intersect the subspace.
        intersection := intersection meet sub<Vspace | [Vspace!v : v in Rows(basis_j)]>;
    end for;
    return Rows(Matrix(Basis(intersection)));
end intrinsic;


intrinsic NullspaceForModuliNaive(M::Mtrx, moduli::SeqEnum) -> SeqEnum
{ For a matrix M and integer sequence moduli, we return a basis for the subspace of e satisfying
the congruences: sum_i e_i M_ij = 0 mod moduli[j]. }
    n1 := Nrows(M);
    n2 := Ncols(M);
    assert n2 eq #moduli;
    vs := ComputeVectorsModM(n1, LCM(moduli));
    solutions := [];
    Vspace := RSpace(Integers(), n1);
    for v in vs do
        result := Vspace!v * M;
        if { result[j] mod moduli[j] : j in [1..n2]} eq { 0 } then
            Append(~solutions, v);
        end if;
    end for;
    space := sub<Vspace | [Vspace!v : v in solutions]>;
    return Rows(Matrix(Basis(space)));
end intrinsic;
