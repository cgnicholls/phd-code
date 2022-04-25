import "groebner_functions.m": exhaust_groebner_relations, groebner_solutions;

// returns whether two of the three pairs in pq are the same.
contains_duplicate := function(pq)
    len := (#pq) / 3;
    if pq[1..len] eq pq[len+1..2*len] then
        return true;
    end if;
    if pq[1..len] eq pq[2*len+1..3*len] then
        return true;
    end if;
    if pq[len+1..2*len] eq pq[2*len+1..3*len] then
        return true;
    end if;
    return false;
end function;

get_all_equations := function(polys)
    eqns := [];
    for i in [2..#polys] do
        eqns cat:= Coefficients(polys[1] - polys[i]);
    end for;
    return eqns;
end function;

find_curve_from_solutions := function(pq, get_f, get_curve, torsion_function, solutions)
    curves := [];
    torsions := [];
    for point in solutions do
        f := get_f(pq, point);
        worked := false;
        if f eq 0 then
            print "f is zero!";
            continue;
        end if;
        if IsSquarefree(f) then
            print "Found", f;
            try
                curve := get_curve(f);
                worked := true;
            catch e
                print e;
            end try;
        end if;
        if worked then
            torsion := torsion_function(curve);
            // Only add the curve if it has nonzero torsion.
            if #torsion gt 0 and Max(torsion) gt 0 then
                curves := curves cat [curve];
                torsions := torsions cat [torsion];
            else
                print "The curve", curve, "doesn't have torsion!";
            end if;
        end if;
    end for;
    return curves, torsions;
end function;

search_for_curves := function(pq, polys_function, get_f, get_curve, torsion_function, extra_relations, avoid)
    eqns := get_all_equations(polys_function(pq)) cat extra_relations;
    print "Computing groebner basis for equations";
    print eqns;
    time groebners := ExhaustGroebnerRelations(eqns, 1, avoid);
    print groebners;
    all_curves := [];
    all_torsion_orders := [];
    unsolved_groebners := [];
    for groebner in groebners do
        solutions, solved := groebner_solutions(groebner, 2);
        // If the equation isn't solved, then we failed to do a point search,
        // so we might want to manually investigate this.
        if not solved then
            unsolved_groebners := unsolved_groebners cat [groebner];
        end if;
        curves, torsion_orders := find_curve_from_solutions(pq, get_f, get_curve, torsion_function, solutions);
        if #curves gt 0 then
            all_curves := all_curves cat curves;
            all_torsion_orders := all_torsion_orders cat [torsion_orders];
        end if;
    end for;
    return all_curves, all_torsion_orders, unsolved_groebners;
end function;

is_isomorphic := function(integral_model1, integal_model2)
    try
        is_iso := IsIsomorphic(integral_model1, integal_model2);
        return is_iso;
    catch e
        print e;
        print "Error in IsIsomorphic";
        return false;
    end try;
end function;

uniqify_curves := function(curves)
    integral_models := [IntegralModel(ChangeRing(curve, Rationals())) : curve in curves];
    unique_indices := [1];
    for i in [2..#curves] do
        if not true in {is_isomorphic(integral_models[i], integral_models[j]) : j
        in unique_indices} then
            unique_indices := unique_indices cat [i];
        end if;
    end for;
    return unique_indices;
end function;

// Take the unique curves every uniqify_every times (set to zero if every time).
search_for_curves_multiple_pq := function(pqs, polys_function, get_f, extra_relations, avoid, uniqify_every)
    print "Searching", #pqs, "pqs";
    all_curves := [];
    all_torsion_relations := [];
    all_unsolved_groebners := [];
    for i in [1..#pqs] do
        pq := pqs[i];
        //if contains_duplicate(pq) then
        //    continue;
        //end if;
        print "pq", pq;
        use_relations := extra_relations;
        time curves, torsion_relations, unsolved_groebners := search_for_curves(pq, get_f, use_relations, avoid);
        if #curves gt 0 then
            all_curves := all_curves cat curves;
            all_torsion_relations := all_torsion_relations cat torsion_relations;
        end if;
        if #unsolved_groebners gt 0 then
            all_unsolved_groebners := all_unsolved_groebners cat [unsolved_groebners];
        end if;
        if (i mod uniqify_every) eq 0 and #all_curves gt 0 then
            print "Uniqifying curves";
            time unique_indices := uniqify_curves(all_curves);
            all_curves := all_curves[unique_indices];
            all_torsion_relations := all_torsion_relations[unique_indices];
        end if;
        print "Unsolved groebners", all_unsolved_groebners;
        print "Curves so far", all_curves;
        print "Torsions so far", all_torsion_relations;
        print "Fraction done", i, "/", #pqs;
    end for;
    return all_curves, all_torsion_relations;
end function;

search_for_curves_multiple_relations := function(pqs, polys_function, get_f, extra_relations, avoid, uniqify_every)
    all_curves := [];
    all_torsions := [];
    for rels in extra_relations do
        curves, torsions := search_for_curves_multiple_pq(pqs, polys_function, get_f, rels, avoid, uniqify_every);
        all_curves cat:= curves;
        all_torsions cat:= torsions;
        print "Curves so far", curves;
        print "Torsions so far", torsions;
    end for;
    return all_curves;
    return all_torsions;
end function;

// Returns all lists of length n that sum to c (where c >= 0).
intrinsic ListsOfLengthAndSum(length::RngIntElt, sum::RngIntElt) -> SeqEnum
    { Construct all lists of given length summing to sum. }
    // We first construct all lists of length 1 summing to 0..sum, then all
    // lists of size 2 summing to 0..sum etc.  last_lists holds the lists of
    // length `length-1` such that the first element is all lists summing to 0,
    // the next element has all lists summing to 1, and so on.
    last_lists := [[[i]] : i in [0..sum]];
    for l in [2..length] do
        current_lists := [];
        for s in [0..sum] do
            lists_sum := [];
            // Now construct all lists of length l with sum s.
            for i in [0..s] do
                // Look at all the lists that sum to i and append s-i. Requires i <= s.
                for list in last_lists[i+1] do
                    lists_sum := lists_sum cat [list cat [s-i]];
                end for;
            end for;
            current_lists := current_lists cat [lists_sum];
        end for;
        last_lists := current_lists;
    end for;
    return last_lists[sum+1];
end intrinsic;


intrinsic ListsOfLengthAndSumInRange(length::RngIntElt, min_sum::RngIntElt,
max_sum::RngIntElt : IncludeNegatives := false) -> SeqEnum
{ Construct all lists of non-negative integers of given length summing to between min_sum and max_sum. }
    lists := [];
    for i in [min_sum..max_sum] do
        lists cat:= ListsOfLengthAndSum(length, i);
    end for;
    if IncludeNegatives then
        return AllPossibleSignsForLists(lists);
    else
        return lists;
    end if;
end intrinsic;

intrinsic AllPQTriples(length, min_pq, max_pq) -> SeqEnum
{Returns only the unique triple of sums between min_pq and max_pq. Each element of the triple
is a list of given length.}

    possible_triples := [];
    for i in [min_pq..max_pq] do
        possible_triples := possible_triples cat ListsOfLengthAndSum(length, i);
    end for;
    triples := [];
    for i in [1..#possible_triples] do
        for j in [i+1..#possible_triples] do
            for k in [j+1..#possible_triples] do
                triples := triples cat [possible_triples[i] cat possible_triples[j] cat possible_triples[k]];
            end for;
        end for;
    end for;
    return triples;
end intrinsic;


// Take the unique curves every uniqify_every times (set to zero if every time).
search_multiple_pq_using_irreds := function(pqs, polys_function, get_f, get_curve, torsion_function, extra_relations, avoid, uniqify_every)
    print "Searching", #pqs, "pqs";
    all_curves := [];
    all_torsion_relations := [];
    for i in [1..#pqs] do
        pq := pqs[i];
        print "pq", pq;
        use_relations := extra_relations;
        equations := get_all_equations(polys_function(pq));
        equations cat:= extra_relations;
        _K := Universe(equations);
        S := Scheme(AffineSpace(_K), equations);
        print "Scheme of dimension", Dimension(S);
        print "Computing reduced subscheme";
        time Sred := ReducedSubscheme(S);
        print "Computing irreducible components";
        time components := IrreducibleComponents(Sred);
        print components;
        for c in components do
            c_eqns := Equations(c);
            time ideal_contains_an_avoid := true in {a in Ideal(c_eqns) : a in avoid};
            if not ideal_contains_an_avoid then
                time solutions := groebner_solutions(Equations(c), 2);
                time curves, torsion_orders := find_curve_from_solutions(pq, get_f, get_curve, torsion_function, solutions);
                print curves;
                print torsion_orders;

                if #curves gt 0 then
                    all_curves := all_curves cat curves;
                    all_torsion_relations := all_torsion_relations cat torsion_orders;
                end if;
            end if;
        end for;
        if (i mod uniqify_every) eq 0 and #all_curves gt 0 then
            print "Uniqifying curves";
            time unique_indices := uniqify_curves(all_curves);
            all_curves := all_curves[unique_indices];
            all_torsion_relations := all_torsion_relations[unique_indices];
        end if;
        print "Curves so far", all_curves;
        print "Torsions so far", all_torsion_relations;
        print "Fraction done", i, "/", #pqs;
    end for;
    return all_curves, all_torsion_relations;
end function;


intrinsic AllPQ(length::RngIntElt, num::RngIntElt, min_sum::RngIntElt, max_sum::RngIntElt) -> SeqEnum
{ Returns lists of size length * num, where the list is formed of 'num' chunks of size 'length'. Each
chunk represents the possible exponents. And each chunk has sum in [min_sum..max_sum]. }
    possible_chunks := [];
    for i in [min_sum..max_sum] do
        possible_chunks cat:= ListsOfLengthAndSum(length, i);
    end for;

    product := CartesianPower(possible_chunks, num);

    pqs := [TupleToList(elt) : elt in product];
    pqs := [[seq : seq in pq] : pq in pqs];

    // Restrict to the pqs that have distinct elements.
    pqs := [pq : pq in pqs | #Set(pq) eq num];

    return pqs;
end intrinsic;


// Returns only the unique pair of sums between min_pq and max_pq, and stop
// after max_num pqs have been found (unless max_num is -1). Each element of the
// triple is a list of length 'length'.
intrinsic AllPQPairs(length::RngIntElt, min_sum::RngIntElt, max_sum::RngIntElt)
-> SeqEnum
{ Computes all pairs of lists pi, qi of length 'length' of non-negative
integers such that the sum of each list is between min_sum and max_sum
(inclusive). }
    possible_pairs := [];
    for i in [min_sum..max_sum] do
        possible_pairs := possible_pairs cat ListsOfLengthAndSum(length, i);
    end for;
    pairs := [];
    for i in [1..#possible_pairs] do
        for j in [i..#possible_pairs] do
            pairs := pairs cat [possible_pairs[i] cat possible_pairs[j]];
        end for;
    end for;
    return pairs;
end intrinsic;


intrinsic AllPossibleSigns(seq::SeqEnum) -> SeqEnum
    { Given a sequence of ring elements, returns a sequence of sequences of ring
    elements. We have one element in the new sequence for each possible
    combination of signs of the original sequence. }
    
    // Compute all possible signs.
    vectors := Reverse(ComputeVectorsModM(#seq, 2));
    signs := [[2*vi-1 : vi in vec] : vec in vectors];

    return [MultiplySequences(sign, seq) : sign in signs];
end intrinsic;


intrinsic AllPossibleSignsForLists(seq_of_seqs::SeqEnum) -> SeqEnum
{ Apply AllPossibleSigns to each sequence in seq_of_seqs. Returns a sequence of sequences. }
    all_seqs := {};
    for seq in seq_of_seqs do
        all_seqs join:= Set(AllPossibleSigns(seq));
    end for;
    return [seq : seq in all_seqs];
end intrinsic;
