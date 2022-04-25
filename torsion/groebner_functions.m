// intrinsic GroebnerSolutions(groebner::SeqEnum : max_height := 2) -> SeqEnum
// {Find points on the scheme satisfied by the given groebner basis.}

//     _K := Universe(groebner);
//     S := Scheme(AffineSpace(_K), groebner);
//     solved := true;
//     points := [];
//     if Dimension(S) eq 0 then
//         points := Points(S);
//         points := [Eltseq(point) : point in points];
//     else
//         // If the dimension of S is positive, then we can try a point search
//         // instead.
//         print "Positive dimension", Dimension(S), "so using PointSearch rather than Points.
//         Could also try specialising some of the free parameters.";
//         print S;

//         time points := RandomSearchSpecialise(S);
//         if #points gt 0 then
//             print "Found points by random specialisation";
//             print points;
//         end if;

//         // if Dimension(S) eq 1 then
//         //     max_height := 10;
//         // elif Dimension(S) eq 2 then
//         //     max_height := 5;
//         // end if;
//         // print "Max height", max_height;
//         // print "Searching using point search reduced";
//         // time points_reduced := PointSearchReduced(S, max_height);
//         // print "Found points", points_reduced;
//         // print "Searching using point search";
//         // // time points := PointSearch(S, max_height);
//         // // points := [Eltseq(point) : point in points];
//         // points := points_reduced cat points;
//     end if;
//     return points;
// end intrinsic;

// Returns the last reducible element and true (if there is one) or 0 and false
// (if there isn't).
function get_last_reducible_element(list)
    for i in Reverse([1..#list]) do
        if not IsIrreducible(list[i]) then
            return list[i], true;
        end if;
    end for;
    return 0, false;
end function;

// returns whether the maximum degree of every variable in poly is at most max_deg.
degrees := function(poly)
    _K := Parent(poly);
    Pt := PolynomialRing(Rationals());
    variables := [_K.i : i in [1..Rank(_K)]];
    return [Degree(poly, var) : var in variables];
end function;

intrinsic ExhaustGroebnerRelations(initial_relations::SeqEnum, max_deg::RngIntElt,
avoid::SeqEnum) -> SeqEnum
{For the initial relations, recursively computes Groebner bases whenever there
is a reducible element in the list -- until all choices have been made
regarding factors. Only adds a factor of a reducible polynomial if it has
degree at most max_deg. If you set max_deg = -1 then the max_deg condition
doesn't apply. Also, don't consider any groebner bases that have elements in
the list avoid.}
    irred_groebners := [];
    relations_to_try := [initial_relations];
    while #relations_to_try gt 0 do
        // Do a depth first search (so use a stack).
        // Remove the top item from the stack.
        relation_to_try := relations_to_try[#relations_to_try];
        relations_to_try := relations_to_try[1..#relations_to_try-1];
        // Compute the Groebner basis
        groebner := GroebnerBasis(relation_to_try);
        // Iterate through the elements of the groebner basis in reverse order.
        last_reducible, exists_reducible := get_last_reducible_element(groebner);
        // If all elements in the groebner basis are irreducible, then add this
        // groebner basis to the list of complete ones.
        if not exists_reducible then
            ideal_contains_an_avoid := true in {a in Ideal(groebner) : a in avoid};
            if not ideal_contains_an_avoid then
                irred_groebners := irred_groebners cat [groebner];
            end if;
        else
            factors := Factorisation(last_reducible);
            for factor in factors do
                degree_cond := true;
                if max_deg ne -1 then
                    degree_cond := (Max(degrees(factor[1])) le max_deg);
                end if;
                if not degree_cond then
                    print "Skipping (degree)", factor[1];
                    continue;
                end if;
                relations_to_add := relation_to_try cat [factor[1]];
                ideal_contains_an_avoid := true in {a in Ideal(relations_to_add) : a in avoid};
                if ideal_contains_an_avoid then
                    print "Skipping (contains an element to avoid)", factor[1];
                    continue;
                end if;
                print "Trying", factor[1];
                relations_to_try := relations_to_try cat [relations_to_add];
            end for;
        end if;
    end while;
    return irred_groebners;
end intrinsic;


intrinsic SearchUsingGroebners(eqns, avoid : max_deg := 1, height_bound := 5) -> SeqEnum
{ Searches for points on the given equations. }
    groebners := ExhaustGroebnerRelations(eqns, max_deg, avoid);
    solns := [];
    for groebner in groebners do
        solns cat:= PointSearchReduced(groebner, height_bound);
    end for;
    return solns;
end intrinsic;


intrinsic SearchUsingIrreds(eqns, avoid : verbose := true) -> SeqEnum
{Searches for points on the given equations.}
    if verbose then
        print "Searching", eqns;
    end if;
    all_solns := [];
    _K := Universe(eqns);
    S := Scheme(AffineSpace(_K), eqns);
    if verbose then
        print "Scheme of dimension", Dimension(S);
        print "Computing reduced subscheme";
    end if;
    time S := ReducedSubscheme(S);
    if verbose then
        print "Computing irreducible components";
    end if;
    time components := IrreducibleComponents(S);
    for c in components do
        c_eqns := Equations(c);
        time ideal_contains_an_avoid := true in {a in Ideal(c_eqns) : a in avoid};
        if not ideal_contains_an_avoid then
            time solutions := PointSearchReduced(Equations(c), 10);
            all_solns cat:= solutions;
        end if;
    end for;
    return all_solns;
end intrinsic;
