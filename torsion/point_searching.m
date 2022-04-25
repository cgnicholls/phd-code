higher_order_variables := function(eqns)
    K := Universe(eqns);
    return [i : i in [1..Rank(K)] | Max([Degree(eqn, K.i) : eqn in eqns]) gt 1];
end function;

// Determine which variables have 
random_search_specialise := function(scheme)
    dim := Dimension(scheme);
    eqns := Equations(scheme);
    K := Universe(eqns);
    high_vars := higher_order_variables(eqns);
    specs := [];
    while Dimension(Scheme(AffineSpace(K), eqns cat specs)) gt 0 do
        // if #high_vars gt 0 then
            // var_to_use := high_vars[1];
            // Remove(~high_vars, 1);
        // else
        var_to_use := Random([1..Rank(K)]);
        // end if;
        Append(~specs, K.var_to_use - Random(1,100) / Random(1,100));
    end while;
    scheme := Scheme(AffineSpace(K), eqns cat specs);
    points := Points(scheme);
    return [Eltseq(pt) : pt in points];
end function;

// Returns the indices of the variables occurring in eqn.
variables_occuring := function(eqn)
    K := Parent(eqn);
    return [i : i in [1..Rank(K)] | Degree(eqn, K.i) gt 0];
end function;

index_in_list := function(list, elt)
    indices := [i : i in [1..#list] | list[i] eq elt];
    if #indices gt 0 then
        return indices[1];
    else
        return -1;
    end if;
end function;

specialise_hom := function(K, fixed_variables)
    imgs := [];
    fixed_vars := [fixed[1] : fixed in fixed_variables];
    for i in [1..Rank(K)] do
        index := index_in_list(fixed_vars, i);
        if index gt 0 then
            Append(~imgs, K!fixed_variables[index][2]);
        else
            Append(~imgs, K.i);
        end if;
    end for;
    return hom<K->K | imgs>;
end function;

map_to_minimal_space := function(scheme)
    eqns := Equations(scheme);
    K := Universe(eqns);
    vars_occurring := {};
    for eqn in eqns do
        vars_occurring join:= Set(variables_occuring(eqn));
    end for;
    vars_occurring := [v : v in vars_occurring];
    // Create a new polynomial ring to map to.
    newK := PolynomialRing(Rationals(), #vars_occurring);

    index_correspondence := [];
    imgs := [];
    current := 1;
    for i in [1..Rank(K)] do
        // Check if variable i occurs
        if i in vars_occurring then
            Append(~imgs, newK.current);
            Append(~index_correspondence, [i, current]);
            current +:= 1;
        else
            Append(~imgs, newK!0);
            Append(~index_correspondence, [i, 0]);
        end if;
    end for;

    thehom := hom<K->newK | imgs>;
    return Scheme(AffineSpace(newK), [thehom(eqn) : eqn in eqns]), index_correspondence;
end function;

// This function takes a scheme and searches for points. But it first removes
// all variables that are actually fixed.
find_fixed_variables := function(scheme)
    eqns := Equations(scheme);
    K := Universe(eqns);

    fixed_variables := [];
    for eqn in eqns do
        vars_occurring := variables_occuring(eqn);
        if (#vars_occurring eq 1) and (Degree(eqn) eq 1) then
            var := K.vars_occurring[1];
            value := -MonomialCoefficient(eqn, 1) / MonomialCoefficient(eqn, var);
            Append(~fixed_variables, [vars_occurring[1], value]);
        end if;
    end for;
    thehom := specialise_hom(Universe(eqns), fixed_variables);
    spec_eqns := [thehom(eqn) : eqn in eqns];
    spec_eqns := [eqn : eqn in spec_eqns | eqn ne 0];
    spec_scheme := Scheme(AffineSpace(K), spec_eqns);
    return fixed_variables, spec_scheme;
end function;

// Given the index correspondence between the large space and the small space,
// together with a list of tuples [index, val] for each fixed variable, and a
// list of solutions in the small space, patch them together to form solutions
// in the big space.
// index_correspondence should be a list of tuples [big_index, small_index],
// where small_index = 0 if it doesn't occur.
patch_solutions := function(index_correspondence, fixed_variables, small_solutions)
    solns := [];
    R := Rationals();
    for small_soln in small_solutions do
        soln := [R!0 : i in [1..#index_correspondence]];
        // First set all the fixed variables
        for fixed in fixed_variables do
            soln[Integers()!fixed[1]] := R!fixed[2];
        end for;
        // Now set the values from the small_soln.
        for corresp in [corresp : corresp in index_correspondence | corresp[2] gt 0] do
            soln[corresp[1]] := R!small_soln[corresp[2]];
        end for;
        Append(~solns, soln);
    end for;
    return solns;
end function;

// Given a polynomial 'poly', returns if the polynomial is a conic and, if so,
// the variables in which it is a conic. This is two variables if it's affine,
// and 3 variables if it's projective.
is_conic := function(poly)
    if Degree(poly) ne 2 then
        return false, [];
    end if;
    Kpoly := Parent(poly);
    // Check that at most 3 variables occur in poly.
    variable_indices := [ i : i in [1..Rank(Kpoly)] | Degree(poly, Kpoly.i) gt 0 ];
    if #variable_indices gt 3 then
        return false, [];
    elif #variable_indices le 2 then
        return true, [Kpoly.i : i in variable_indices];
    elif #variable_indices eq 3 then
        // If three variables, then we need the conic to be homogeneous.
        if {Degree(term) : term in Terms(poly)} eq {2} then
            return true, [Kpoly.i : i in variable_indices];
        else
            return false, [];
        end if;
    end if;
end function;

// Search for points by first removing variables that are already determined.
point_search := function(scheme, bound)
    fixed_variables, spec_scheme := find_fixed_variables(scheme);
    if #Equations(spec_scheme) eq 0 then
        // All variables are fixed, so just return the solution.
        K := Universe(Equations(scheme));
        soln := [K!0 : i in [1..Rank(K)]];
        for i in [1..Rank(K)] do
            index := index_in_list([v[1] : v in fixed_variables], i);
            // Currently, if a variable doesn't matter, we just set it to zero,
            // but this is actually a free parameter (if index == -1).
            if index eq -1 then
                soln[i] := 0;
            else
                soln[i] := fixed_variables[index][2];
            end if;
        end for;
        return [soln];
    end if;
    new_scheme, index_correspondence := map_to_minimal_space(spec_scheme);

    random_solutions := RandomSearchSpecialise(new_scheme : num_repeats := 20);
    if #random_solutions gt 0 then
        print "Found solutions using random specialisation";
        return patch_solutions(index_correspondence, fixed_variables, random_solutions);
    end if;

    num_variables := Dimension(AmbientSpace(new_scheme));
    print "Num variables in scheme", num_variables;
    if num_variables ge 3 then
        bound := 2;
    else
        bound := 10;
    end if;

    print "Refuse to search for points!";
    return [];

    // small_solutions := PointSearch(new_scheme, bound);
    // small_solutions := [Eltseq(soln) : soln in small_solutions];
    // return patch_solutions(index_correspondence, fixed_variables, small_solutions);
end function;


intrinsic PointSearchReduced(scheme::Sch, height::RngIntElt) -> SeqEnum
{Search for rational points on the scheme up to bounded height. But first
remove variables that are already determined from the search space.}
    return point_search(scheme, height);
end intrinsic;


intrinsic RandomSearchSpecialise(scheme::Sch : num_repeats := 20) -> SeqEnum
{ Finds points by randomly specialising variables that are not determined. }
    points := {};
    for i in [1..num_repeats] do
        points join:= Set(random_search_specialise(scheme));
    end for;
    return SetToSequence(points);
end intrinsic;


intrinsic RandomSearchSpecialise(eqns::SeqEnum : num_repeats := 20) -> SeqEnum
{ Finds points by randomly specialising variables that are not determined. }
    K := Universe(eqns);
    scheme := Scheme(AffineSpace(K), eqns);
    return RandomSearchSpecialise(scheme : num_repeats := num_repeats);
end intrinsic;


point_search_specialise := function(scheme, rationals)
    eqns := Equations(scheme);
    K := Universe(eqns);
    specs := [];
    high_vars := higher_order_variables(eqns cat specs);
    vars_used := [];
    i := 1;
    spec_scheme := Scheme(AffineSpace(K), eqns cat specs);
    while Dimension(spec_scheme) gt 0 do
        print high_vars;
        if #high_vars gt 0 then
            var_to_use := high_vars[1];
            Remove(~high_vars, 1);
        else
            fixed_variables := find_fixed_variables(eqns cat specs);
            fixed_variables := [j[1] : j in fixed_variables];
            var_to_use := Min([j : j in [1..Rank(K)] | not j in fixed_variables]);
        end if;
        print var_to_use;
        Append(~specs, K.var_to_use - rationals[i]);
        print specs;
        i +:= 1;
        spec_scheme := Scheme(AffineSpace(K), eqns cat specs);
    end while;
    points := Points(spec_scheme);
    return [Eltseq(pt) : pt in points];
end function;


// TODO: Implement this properly later. We should iterate over a small number of undetermined variables
// and specialise their values, then call e.g. search using irreds again.
intrinsic PointSearchSpecialise(scheme::Sch : bound := 10) -> SeqEnum
{Finds points by specialising variables that are not determined. Searches up to height bound.}
    dim := Dimension(scheme);
    num_variables := Rank(Universe(Equations(scheme)));
    specs_list := RationalsUpToHeight(bound, num_variables);
    points := [];
    for specs in specs_list do
        points cat:= point_search_specialise(scheme, specs);
    end for;
    return points;
end intrinsic;


intrinsic PointSearchReduced(eqns::SeqEnum, height_bound::RngIntElt) -> SeqEnum
{ Search for rational points on the scheme defined by the equations. }
    K := Universe(eqns);
    S := Scheme(AffineSpace(K), eqns);

    return PointSearchReduced(S, height_bound);
end intrinsic;