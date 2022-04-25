intrinsic FieldToAlgebra(field::Fld) -> RngUPolRes
{ Returns the algebra for the given field. This is used in computing Selmer groups. }
    modulus := DefiningPolynomial(AbsoluteField(field));
    QT := PolynomialRing(Rationals());
    A := quo<QT | modulus>;
    return A;
end intrinsic;


intrinsic FieldToAlgebra(field::FldPad) -> RngUPolRes
{ Returns the algebra for the p-adic field. }
    modulus := DefiningPolynomial(field);
    QpT := Parent(modulus);
    Ap := quo<QpT | modulus>;
    return Ap;
end intrinsic;


intrinsic FieldElementToAlgebraElement(field::Fld, A::RngUPolRes, alpha::FldElt) -> RngElt
{ Computes the image of alpha in A, where alpha is in field. }
    if Type(field) eq FldRat then
        return A!alpha;
    end if;
    return hom<field->A | A.1>(alpha);
end intrinsic;


intrinsic ComputeMSelmerGroupLocal(p::RngIntElt, m::RngIntElt, As::SetCart :
    precision := 100) -> GrpAb, Map, SetCart
{ Localises the algebras, and computes the direct product of local Selmer groups. That is,
for each field F, computes Fs^* / Fs^*m, where Fs is the completion of F at the
primes s above p. We represent each F as Q[T] / g(T) for some monic irreducible g(T). }
    // For each field, Q[T] / g(T), we create the Qp-algebra Qp[T] / g(T), denoted Ap.
    Aps_list := [];
    local_selmers := [];
    local_selmer_maps := [* *];
    for A in Components(As) do
        modulus := Modulus(A);
        Qp := pAdicField(p, precision);
        QpT := PolynomialRing(Qp);
        Ap := quo<QpT | modulus>;
        Append(~Aps_list, Ap);
        local_selmer, local_selmer_map := MSelmerGroup(Ap, m);
        Append(~local_selmers, local_selmer);
        Append(~local_selmer_maps, local_selmer_map);
    end for;

    // Store the Aps in a Cartesian product.
    Aps := CartesianProduct(Aps_list);

    // Compute the direct product of the Selmer group for each A.
    local_selmer_product, incls, projs := DirectProduct(local_selmers);

    local_selmer_image := function(elt)
        components := [incls[i](local_selmer_maps[i](elt[i])) : i in [1..#Components(Aps)]];
        return ComputeSum(components);
    end function;

    local_selmer_product_map := map<Aps->local_selmer_product | x :-> local_selmer_image(x)>;

    return local_selmer_product, local_selmer_product_map, Aps;
end intrinsic;


intrinsic ImageInDirectProduct(elt::., maps::List, incls::SeqEnum,
    direct_product::GrpAb) -> .
    { Each map takes elt to one of the summand groups in direct_product; incls
    are the inclusions of each summand group into the direct product. }
    img := direct_product!0;
    for i in [1..#incls] do
        img +:= incls[i](maps[i](elt[i]));
    end for;
    return img;
end intrinsic;


intrinsic ComputeMSelmerGroupGlobal(bad_primes::SeqEnum, m::RngIntElt, fields::SetCart)
    -> GrpAb, Map, SetCart
{ Computes the m-Selmer group. Takes in bad_primes (a list of rational primes),
the integer m for the m-Selmer group, and a Cartesian product of fields. \\

Returns:
    - Selmer group: abelian group isomorphic to the product of m-Selmer groups, one for each field in fields. \\

    - Selmer map: map from element in the direct product of fields to the group. \\

    - Generators: generators for the Selmer group. These are elements of the direct product of fields, with 1s in all but one entry. \\

    - As: the list of algebras, one for each field.
}
    compute_m_selmer := function(field)
        primes := PrimesAboveElements(bad_primes, field);
        return MSelmerGroup(primes, m);
    end function;

    As := [];
    m_selmer_field_list := [];
    m_selmer_field_map_list := [* *];
    for field in Components(fields) do
        m_selmer_field, m_selmer_field_map := MSelmerGroup(PrimesAboveElements(bad_primes, field), m);
        Append(~m_selmer_field_list, m_selmer_field);
        Append(~m_selmer_field_map_list, m_selmer_field_map);
        Append(~As, FieldToAlgebra(field));
    end for;

    As := CartesianProduct(As);

    m_selmer, incls, projs := DirectProduct(m_selmer_field_list);

    m_selmer_image := function(alpha)
        return ComputeSum([incls[i](m_selmer_field_map_list[i](alpha[i])) : i in [1..#m_selmer_field_list]]);
    end function;

    m_selmer_preimage := function(g)
        preimage := fields!<projs[i](g) @@ m_selmer_field_map_list[i] : i in [1..#projs]>;
        return As!<FieldElementToAlgebraElement(fields[i], As[i], preimage[i]) : i in [1..#Components(fields)]>;
    end function;

    m_selmer_map := map<As->m_selmer | x :-> m_selmer_image(x), y :-> m_selmer_preimage(y)>;

    return m_selmer, m_selmer_map, As;
end intrinsic;


intrinsic ComputeRightVerticalMap(global_selmer_map::Map, local_selmer_map::Map) -> Map
{ Computes the right vertical map given a global Selmer group and local
Selmer group. }
    global_selmer := Codomain(global_selmer_map);
    As := Domain(global_selmer_map);
    local_selmer := Codomain(local_selmer_map);
    Aps := Domain(local_selmer_map);
    // Need to define the image of each generator of global_selmer.
    imgs := [* *];
    for i in [1..#Generators(global_selmer)] do
        // Check the ith generator maps to the ith generator of global_selmer.
        gen := global_selmer.i @@ global_selmer_map;
        
        img_gen := Aps!<hom<As[j]->Aps[j] | Aps[j].1>(gen[j]) : j in [1..#Components(Aps)]>;
        Append(~imgs, local_selmer_map(img_gen));
    end for;
    rv_map := hom<global_selmer->local_selmer | [global_selmer.i->imgs[i] : i in [1..#imgs]]>;
    return rv_map;
end intrinsic;


intrinsic ComputeModuloNthPowers(elt::RngElt, gens::SeqEnum, n::RngIntElt) -> SeqEnum
{ Computes elt modulo nth powers, assuming elt is in the group generated by gens. }
    exponents := ComputeVectorsModM(#gens, n);
    exponent_relations := [];
    for e in exponents do
        test_elt := Product([gens[i]^e[i] : i in [1..#gens]]);
        if IsNthPower(elt / test_elt, n) then
            Append(~exponent_relations, e);
        end if;
    end for;
    return exponent_relations;
end intrinsic;


intrinsic PreimageOfMap(f::Map, H::GrpAb) -> GrpAb
    { Returns the preimage of the subgroup H under the map f. This assumes that
    f is a map from gp1 to gp2 and H is a subgroup of gp2. }
    // Let f be a map from gp1 to gp2. Let H be a subgroup of gp2.
    // This function computes the preimage of subgroup in gp1.
    kernel := Kernel(f);
    kernel_gens := [gen : gen in Generators(kernel)];

    // First restrict the subgroup to the image of the map.
    subgroup_meet_image := Image(f) meet H;
    preimages := [gen @@ f : gen in Generators(subgroup_meet_image)];
    return sub<Domain(f) | kernel_gens cat preimages>;
end intrinsic;


intrinsic MSelmerGroupAtInfinity(field::Fld, m::RngIntElt) -> GrpAb, Map
{ Computes the m-Selmer group for the infinite places of the field, where field
is a number field, including the rationals. If there are no real places, then the
only completions are the complex numbers; since CC^* / CC^*m is trivial, we let G be
the trivial group. If m is odd, then also RR^* / RR^*m is trivial, so we let G be the
trivial group again. If there is a real place, and m is even, we let G be isomorphic to
RR^* / RR^*m. We also return a map from field to G. }
    real_places := RealPlaces(field);

    // If no real places, or m is odd, then the group is trivial
    if (#real_places eq 0) or (m mod 2 eq 1) then
        selmer := AbelianGroup([1]);
        selmer_map := map<field->selmer | x :-> selmer!0, y :-> field!1>;
        return selmer, selmer_map;
    end if;

    // Else, there are real places and m is even, so we return a group isomorphic to RR^* / RR*^2,
    // which is isomorphic to the cyclic group of order 2, generated by -1.
    selmer := AbelianGroup([2]);

    // Use the first real place for the embedding into RR.
    real_place := real_places[1];
    selmer_image := function(alpha)
        assert alpha ne 0;
        return Sign(Evaluate(alpha, real_place)) gt 0 select selmer!0 else selmer.1;
    end function;

    selmer_preimage := function(g)
        return g eq selmer!0 select field!1 else field!-1;
    end function;

    selmer_map := map<field->selmer | x :-> selmer_image(x), y :-> selmer_preimage(y)>;

    return selmer, selmer_map;
end intrinsic;


intrinsic MSelmerGroupAtInfinity(fields::SetCart, m::RngIntElt) -> GrpAb, Map
{ Returns the product of the m-Selmer groups at infinity for the fields. }
    
    selmer_factors := [];
    selmer_factor_maps := [* *];
    for field in Components(fields) do
        selmer_factor, selmer_factor_map := MSelmerGroupAtInfinity(field, m);
        Append(~selmer_factors, selmer_factor);
        Append(~selmer_factor_maps, selmer_factor_map);
    end for;

    As := CartesianProduct([FieldToAlgebra(field) : field in Components(fields)]);

    selmer, incls, projs := DirectProduct(selmer_factors);

    selmer_image := function(alpha)
        return ComputeSum([incls[i](selmer_factor_maps[i](alpha[i])) : i in [1..#selmer_factors]]);
    end function;

    selmer_preimage := function(g)
        preimage := fields!<projs[i](g) @@ selmer_factor_maps[i] : i in [1..#projs]>;
        return As!<FieldElementToAlgebraElement(fields[i], As[i], preimage[i]) : i in [1..#Components(fields)]>;
    end function;

    selmer_map := map<As -> selmer | x :-> selmer_image(x), y :-> selmer_preimage(y)>;

    return selmer, selmer_map;
end intrinsic;



// intrinsic RealsModSquares(dim::RngIntElt) -> GrpAb, Map
// { Computes (R^* / R^*2)^dim. Returns an abelian group and a map from length dim
// sequences of nonzero real numbers to this group. }
//     selmer := AbelianGroup([2 : i in [1..dim]]);
//     selmer_image := function(alpha)
//         assert #[i : i in [1..#alpha] | alpha[i] eq 0] eq 0;
//         components := [ai lt 0 select 1 else 0 : ai in TupleToList(alpha)];
//         return selmer!components;
//     end function;

//     domain := CartesianPower(Rationals(), dim);

//     selmer_preimage := function(g)
//         // The element [g_1, .., g_dim] has preimage <(-1)^g_1, .., (-1)^g_dim>.
//         g_vec := Eltseq(g);
//         return domain!<(-1)^g_vec[i] : i in [1..dim]>;
//     end function;

//     selmer_map := map<domain->selmer | x :-> selmer_image(x), y :-> selmer_preimage(y)>;

//     return selmer, selmer_map;
// end intrinsic;

