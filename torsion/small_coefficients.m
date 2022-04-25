

intrinsic SearchSmallCoefficients(g::RngIntElt, bound::RngIntElt : max_number := 10000,
set_to_zero := [], set_to_one := []) -> SeqEnum
{ Searches for curves of the form y^2 = f(x), where f(x) has coefficients of small height. Searches
with random coefficients. Sets all coefficients in set_to_zero to zero and sets all coefficients in
set_to_one to one. }
    P<x> := PolynomialRing(Rationals());
    torsion_dict := AssociativeArray();
    degree := 2 * g + 2;
    for i in [1..max_number] do
        coefficients := [Random(-bound, bound) : j in [0..degree]];
        for j in set_to_zero do
            coefficients[j + 1] := 0;
        end for;
        for j in set_to_one do
            coefficients[j + 1] := 1;
        end for;
        f := P!Polynomial(coefficients);
        if not IsSquarefree(f) then
            continue;
        end if;
        try
            order := HeuristicTorsionOrder(f);
            if order gt 1 then
                InsertIntoTorsionDict(~torsion_dict, f, order);
                SummariseTorsion(torsion_dict);
            end if;
        catch e
            print e;
            print "f", f;
        end try;
    end for;
    return torsion_dict;
end intrinsic;