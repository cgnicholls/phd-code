
intrinsic Divisors(poly::RngUPolElt) -> SeqEnum
	{ Computes all monic divisors of the polynomial. }
	factorisation := Factorisation(poly);
	factors := [factor[1] : factor in factorisation];
	max_exponents := [factor[2] : factor in factorisation];
	l := #factors;
	exponent := [0 : i in [1..l]];
	divisors := [];
	while exponent ne [0 : i in [1..l]] or #divisors eq 0 do
		element := Product([factors[j]^exponent[j] : j in [1..l]]);
		Append(~divisors, element);

		// Go to the next exponent.
		i := l;
		while i gt 0 do
			// If the ith component is less than its maximum, then we can increment it
			// and we've found the next exponent.
			if exponent[i] lt max_exponents[i] then
				exponent[i] +:= 1;
				break;
			else
				// Otherwise, we reset the ith exponent to zero, and move on to i - 1.
				exponent[i] := 0;
				i -:= 1;
			end if;
		end while;
		// If we have reset them all to zero, then we're done.
	end while;
	return divisors;
end intrinsic;


intrinsic FactorIntoProductOfMaxDegree(poly::RngUPolElt, max_degree::RngIntElt)
	-> SeqEnum
	{ Returns all possible factorisations of poly into A * B, where
	B is monic and the degrees of A and B are both at most max_degree. }
	if poly eq 0 then
		return [];
	end if;
	lead := LeadingCoefficient(poly);
	
	divisors := Divisors(poly);
	pairs := [[poly div divisor, divisor] : divisor in divisors];
	return [pair : pair in pairs | Degree(pair[1]) le max_degree and Degree(pair[2]) le max_degree];
end intrinsic;


intrinsic OrderOfPoint(D::JacHypPt : max_order := 200) -> RngIntElt
	{ Computes the order of the point, up to a maximum of max_order. Returns -1 if order not found. }
	J := Parent(D);
	iD := D;
	prediction := 0;
	i := 1;
	while 2 * i le max_order do
		ip1D := iD + D;
		if iD eq -iD then
			return 2 * i;
		end if;
		if iD eq -ip1D then
			return 2 * i + 1;
		end if;
		i +:= 1;
		iD := ip1D;
	end while;
	return -1;
end intrinsic;


intrinsic TwoTorsion(f::RngUPolElt) -> SeqEnum
	{ Returns the two torsion of the Jacobian of y^2 = f(x). }
	factors := Divisors(f);
	J := Jacobian(HyperellipticCurve(f));
	if Degree(f) mod 2 eq 1 then
		return [elt<J | factor, 0> : factor in factors | Degree(factor) le 2];
	else
		return [J!0] cat [elt<J | factor, 0> : factor in factors | Degree(factor) eq 2];
	end if;
end intrinsic;


intrinsic HeuristicTorsionOrder(f::RngUPolElt : bound := 100, max_order := 200) -> RngIntElt
{ Computes as much of the torsion subgroup of y^2 = f(x) as possible by first searching
for points on the curve. Returns the least common multiple of the found torsion orders,
which is the largest order torsion point we can find on the Jacobian. If we find no nontrivial
torsion points we return 1. }
	_, orders := HeuristicTorsionSubgroup(f : bound := bound, max_order := max_order);
	if #orders gt 0 then
		return LCM(orders);
	else
		return 1;
	end if;
end intrinsic;


intrinsic HeuristicTorsionOrder(fs::SeqEnum[RngUPolElt] : bound := 100, max_order := 200) -> SeqEnum[RngIntElt]
{Calls HeuristicTorsionOrder on each f.}
	good_fs := [];
	bad_fs := [];
	orders := [];
	for f in fs do
		try
			order := HeuristicTorsionOrder(f : bound := bound, max_order := max_order);
			Append(~good_fs, f);
			Append(~orders, order);
		catch e
			Append(~bad_fs, f);
		end try;
	end for;
	return good_fs, orders, bad_fs;
end intrinsic;


intrinsic HeuristicTorsionSubgroup(f::RngUPolElt : bound := 100, max_order := 200) -> SeqEnum, SeqEnum
	{ Computes as much of the torsion subgroup of y^2 = f(x) as possible by first searching for points on the curve. }

	curve := HyperellipticCurve(f);
	torsion_bound := TorsionBound(Jacobian(IntegralModel(HyperellipticCurve(RandomSpecialisation(f)))), 10);
	J := Jacobian(curve);

	if torsion_bound gt 100 then
		print "Warning, torsion_bound is large:", torsion_bound;
	end if;

	points := [pt : pt in PointsAtInfinity(curve)];
	for x_coord in RationalsUpToHeight(bound) do
		points cat:= [pt : pt in Points(curve, x_coord)];
	end for;

	// Also look for 2-torsion.
	two_torsion := TwoTorsion(f);

	base_pt := points[1];
	torsion_subgroup := [];
	orders := [];
	for pt in points[2..#points] do
		for tt in two_torsion do
			jac_pt := (pt - base_pt) + tt;
			order := OrderOfPoint(jac_pt : max_order := torsion_bound);
			if order gt 1 then
				Append(~torsion_subgroup, jac_pt);
				Append(~orders, order);
			end if;
		end for;
	end for;

	return torsion_subgroup, orders;
end intrinsic;


intrinsic TorsionOrderGenus2(f::RngUPolElt) -> SeqEnum[RngIntElt]
{ Computes the orders for generators of the torsion subgroup of the Jacobian of the genus 2 curve y^2 = f(x). }
	torsion_subgroup := TorsionSubgroup(Jacobian(IntegralModel(HyperellipticCurve(f))));
	orders := [Order(gen) : gen in Generators(torsion_subgroup)];
	if #orders gt 0 then
		return LCM(orders);
	else
		return 1;
	end if;
end intrinsic;


intrinsic UniqifyCurves(torsion_dict::Assoc) -> Assoc
{ Returns a torsion dictionary such that the curves are pairwise nonisomorphic
over Q. We only have to check curves for each torsion order separately, so
this should be much faster than the other version of UniqifyCurves.}
	unique_torsion_dict := AssociativeArray();
	for order in Keys(torsion_dict) do
		unique_fs, unique_indices := UniqifyCurves(SetToSequence(torsion_dict[order]));
		unique_torsion_dict[order] := Set(unique_fs);
	end for;
	return unique_torsion_dict;
end intrinsic;


intrinsic UniqifyCurves(fs::SeqEnum[RngUPolElt]) -> SeqEnum[RngUPolElt]
{ Returns the sequence of fs such that the curves y^2 = f(x) are unique up to isomorphism over Q.
Only returns fs of degree at least 3. }
	unique_fs := [];
	unique_indices := [];
	for i in [1..#fs] do
		f := fs[i];
		if Degree(f) lt 3 then
			continue;
		end if;
		if f in unique_fs then
			continue;
		end if;
		already_in := false;
		for f2 in unique_fs do
			if IsIsomorphic(HyperellipticCurve(f), HyperellipticCurve(f2)) then
				already_in := true;
				break;
			end if;
		end for;
		if not already_in then
			Append(~unique_fs, f);
			Append(~unique_indices, i);
		end if;
	end for;
	return unique_fs, unique_indices;
end intrinsic;


intrinsic NewTorsionDict() -> Assoc
{ Returns a new associative array. }
	torsion_dict := AssociativeArray();
	return torsion_dict;
end intrinsic;


intrinsic InsertIntoTorsionDict(~torsion_dict::Assoc, f::RngUPolElt, order::RngIntElt)
{Inserts the given f and order into the torsion dictionary. The torsion dictionary
has keys the order and values a set of all curves with a torsion point of that order.}
	if IsDefined(torsion_dict, order) then
		Include(~torsion_dict[order], f);
	else
		torsion_dict[order] := {f};
	end if;
end intrinsic;


intrinsic InsertIntoTorsionDict(~torsion_dict::Assoc, fs::SeqEnum[RngUPolElt], orders::SeqEnum[RngIntElt])
{Inserts the given fs and orders into the torsion dictionary. The torsion dictionary
has keys the order and values a set of all curves with a torsion point of that order.}
	assert #fs eq #orders;
	for i in [1..#fs] do
		InsertIntoTorsionDict(~torsion_dict, fs[i], orders[i]);
	end for;
end intrinsic;


intrinsic InsertIntoTorsionDict(~torsion_dict::Assoc, torsion_dict_to_insert::Assoc)
{ Inserts the second torsion dict into the first. }
	for order in Keys(torsion_dict_to_insert) do
		fs := SetToSequence(torsion_dict_to_insert[order]);
		orders := [order : i in [1..#fs]];
		if #fs gt 0 then
			InsertIntoTorsionDict(~torsion_dict, fs, orders);
		end if;
	end for;
end intrinsic;


intrinsic SummariseTorsion(torsion_dict::Assoc : verbose := false)
{ Given a list of curves and orders, sort them by genus and print out a list of unique orders occurring. }
	fs := [];
	orders := [];
	for order in Keys(torsion_dict) do
		fs_of_order := torsion_dict[order];
		for f in fs_of_order do
			Append(~fs, f);
			Append(~orders, order);
		end for;
	end for;

	// If verbose, then print out one example for each order found.
	if verbose then
		for order in Keys(torsion_dict) do
			fs_of_order := SetToSequence(torsion_dict[order]);
			print order, fs_of_order[1];
		end for;
	end if;

	SummariseCurves(fs, orders);
end intrinsic;


intrinsic SummariseCurves(fs::SeqEnum, orders::SeqEnum)
{ Given a list of curves and orders, sort them by genus and print out a list of unique orders occurring. }
	assert #fs eq #orders;
	N := #fs;
	if N eq 0 then
		return;
	end if;
	min_g := Ceiling(Min([Degree(f) : f in fs]) / 2) - 1;
	max_g := Ceiling(Max([Degree(f) : f in fs]) / 2) - 1;

	for g in [min_g..max_g] do
		print "All orders genus", g;
		indices_g := [i : i in [1..#fs] | Degree(fs[i]) gt 0 and Genus(HyperellipticCurve(fs[i])) eq g];
		orders_g := UniqueElements(orders[indices_g]);
		print Sort(orders_g);
		print "Generated by", GeneratorsForOrders(orders_g);
	end for;
end intrinsic;


intrinsic OrdersGeneratedByOrders(orders::SeqEnum) -> SeqEnum
	{ Computes all the orders of torsion points generated by the given orders.
	For example, 4, 6, 13 generate 1, 2, 3, 4, 6, 13. This is not the same as the orders
	generated by these points if they were all in the same group. }
	all_orders := {};
	for order in orders do
		all_orders join:= Set(Divisors(order));
	end for;
	return Sort([order : order in all_orders]);
end intrinsic;


intrinsic OrdersNotGeneratedByOrders(orders::SeqEnum) -> SeqEnum
	{ Computes all the orders of torsion points in the range [1..Max(orders)] that are not
	generated by the given orders. For example, 4, 6, 13 generate 1, 2, 3, 4, 6, 13, so
	5, 7, 8, 9, 10, 11, 12 are not generated. This is not the same as the orders
	generated by these points if they were all in the same group. }
	orders_generated := OrdersGeneratedByOrders(orders);
	return [i : i in [1..Max(orders_generated)] | not i in orders_generated];
end intrinsic;


intrinsic GeneratorsForOrders(orders::SeqEnum) -> SeqEnum
	{ Given orders of torsion points, finds orders that generate all these orders.
	For example, if given [1, 4, 8, 3, 9], then we return [8, 9]. }

	orders := Reverse(Sort(UniqueElements(orders)));
	generators := [];
	for order in orders do
		if not order in OrdersGeneratedByOrders(generators) then
			Append(~generators, order);
		end if;
	end for;
	return Sort(generators);
end intrinsic;


intrinsic RandomSpecialisation(poly::RngUPolElt) -> RngUPolElt
	{ Specialises a polynomial over a function field to random values for the parameters
	in the function field. Returns a polynomial over the rationals. }
	P := Parent(poly);
	K := CoefficientRing(P);
	if Type(K) eq FldRat then
		return poly;
	end if;
	PQ := PolynomialRing(Rationals());
	specialisation := [Random(5, 100) : i in [1..Rank(K)]];
	return hom<P->PQ | hom<K->Rationals() | specialisation>, PQ.1>(poly);
end intrinsic;


intrinsic SpecialisePolynomial(poly::RngUPolElt, values::SeqEnum) -> RngUPolElt
	{ Specialises a polynomial over a function field so that the function field
	parameters have values given by the sequence values. }
	P := Parent(poly);
	K := CoefficientRing(P);
	assert #values eq Rank(K);
	return hom<P->P | hom<K->K | values>, P.1>(poly);
end intrinsic;


intrinsic UniqueElements(seq::SeqEnum) -> SeqEnum
	{ Returns the unique elements in the list. }
	return SetToSequence(Set(seq));
end intrinsic;


intrinsic PossibleDeterminants(pq::SeqEnum) -> SeqEnum
	{ Returns the possible determinants for pq. pq should be length 4, defining the
	rows of a 2 x 2 matrix. We then consider the determinants of all possible signs
	of the matrix formed by the pq. }
	return [Determinant(Matrix(2, 2, pq_sign)) : pq_sign in AllPossibleSigns(pq)];
end intrinsic;


intrinsic SummariseTorsionOnSimpleCurves(fs::SeqEnum) -> SeqEnum, SeqEnum
	{ First restricts to those y^2 = f(x) with simple Jacobian. Then computes the
	unique ones of these, up to isomorphism. Then returns simple_fs, simple_orders,
	where simple_orders is computed using HeuristicTorsionSubgroup. Checks simplicity
	using random specialisations of the curve, if it is defined over a function field. }
	fs := UniqueElements(fs);
	simple_fs := [f : f in fs | IsGeometricallySimple(RandomSpecialisation(f))];
	all_orders := [];
	for f in simple_fs do
		order := HeuristicTorsionOrder(f);
		Append(~all_orders, order);
	end for;
	return simple_fs, all_orders;
end intrinsic;


intrinsic SummariseTorsionOnSimpleCurves(torsion_dict::Assoc) -> SeqEnum, SeqEnum
	{ First restricts to those y^2 = f(x) with simple Jacobian. Then computes the
	unique ones of these, up to isomorphism. Then returns simple_fs, simple_orders,
	where simple_orders is computed using HeuristicTorsionSubgroup. Checks simplicity
	using random specialisations of the curve, if it is defined over a function field. }
	fs := [];
	orders := [];
	simple_torsion_dict := AssociativeArray();
	for order in Keys(torsion_dict) do
		fs_of_order := torsion_dict[order];
		simple_fs_of_order := [f : f in fs_of_order | IsGeometricallySimple(RandomSpecialisation(f))];
		for f in fs_of_order do
			if IsGeometricallySimple(RandomSpecialisation(f)) then
				InsertIntoTorsionDict(~simple_torsion_dict, f, order);
			end if;
		end for;
	end for;
	return simple_torsion_dict;
end intrinsic;


intrinsic CurvesWithTorsionOfOrder(fs::SeqEnum, orders::SeqEnum, order::RngIntElt) -> SeqEnum
	{ Returns just those fs and orders that have an order 'order' point. }
	indices := [i : i in [1..#fs] | order in OrdersGeneratedByOrders(orders[i])];
	return fs[indices], orders[indices];
end intrinsic;


intrinsic CurvesWithTorsionOfOrder(torsion_dict::Assoc, order::RngIntElt) -> SeqEnum
{ Returns just those fs and orders that have an order 'order' point. }
	if IsDefined(torsion_dict, order) then
		return torsion_dict[order];
	else
		return [];
	end if;
end intrinsic;


intrinsic RelationsBetweenDivisors(divisors::SeqEnum : bound := 10) -> SeqEnum
{ Returns the relations between the divisors. If a1 * D1 + .. + an * Dn, then we
return [a1, .., an]. We bound the sum of the absolute values of the ai by bound.
We return a list of all the relations we find in this range. }
	n := #divisors;
	J := Universe(divisors);
	ais := ListsOfLengthAndSumInRange(n, 1, bound : IncludeNegatives := true);
	relations := [];
	for ai in ais do
		dot := ComputeSum(MultiplySequences(ai, divisors));
		if dot eq J!0 then
			Append(~relations, ai);
		end if;
	end for;
	return relations;
end intrinsic;


intrinsic HeuristicRelationsBetweenDivisors(f::RngUPolElt : bound := 10) -> SeqEnum
{ If there are points with x-coordinates 0, 1, and if infinity+, infinity- are both rational,
then we search for relations between the divisors P0 - infty-, P1 - infty-, infty+ - infty-. }
	curve := HyperellipticCurve(f);
	P0 := Points(curve, 0)[1];
	P1 := Points(curve, 1)[1];
	infty1 := PointsAtInfinity(curve)[1];
	infty2 := PointsAtInfinity(curve)[2];
	D0 := P0 - infty1;
	D1 := P1 - infty1;
	Dinf := infty2 - infty1;
	return RelationsBetweenDivisors([D0, D1, Dinf] : bound := bound);
end intrinsic;


// intrinsic SolveForQuadraticSplitting(quadratic::RngUPolElt) -> RngElt
// 	{ Given a quadratic over a function field in one variable, solve for this quadratic splitting, if possible. }
// 	P<x> := Parent(quadratic);
// 	K<t> := CoefficientRing(P);

// 	condition := Product(FactorModSquares(NumeratorTimesDenominator(Discriminant(quadratic))));
// end intrinsic;

intrinsic ReadTorsionDict(file_name::MonStgElt) -> Assoc
{ Reads the torsion dictionary stored at the file name. }
	command := Read(file_name);
	pairs := eval command;
	torsion_dict := AssociativeArray();
	for pair in pairs do
		torsion_dict[pair[1]] := pair[2];
	end for;
	return torsion_dict;
end intrinsic;


intrinsic SaveTorsionDict(file_name::MonStgElt, torsion_dict::Assoc)
{ Saves the given torsion dict to file. }
	keys := [key : key in Keys(torsion_dict)];
	values := [* torsion_dict[key] : key in keys *];
	pairs := [* *];
	for key in keys do
		Append(~pairs, [* key, torsion_dict[key] *]);
	end for;
	PrintFileMagma(file_name, pairs : Overwrite := true);
end intrinsic;


intrinsic SpecialiseTorsionDict(torsion_dict::Assoc) -> Assoc
{ Returns the torsion dict with all curves specialised to be defined over Q. If they are over Q(t), then we
take a random specialisation. }
	P := PolynomialRing(Rationals());
	torsion_dict_spec := NewTorsionDict();
	for key in Keys(torsion_dict) do
		torsion_dict_spec[key] := {P!RandomSpecialisation(f) : f in torsion_dict[key]};
	end for;
	return torsion_dict_spec;
end intrinsic;


intrinsic ReadTorsionPairs(file_name::MonStgElt) -> Assoc
{ Given a file consisting of a list where each element is a list [order, fs], where fs is a set of polynomials,
we return the corresponding torsion dictionary. }
	pairs := eval Read(file_name);
	torsion_dict := AssociativeArray();
	for pair in pairs do
		torsion_dict[pair[1]] := pair[2];
	end for;
	return torsion_dict;
end intrinsic;


intrinsic IntegralModel(f::RngUPolElt) -> RngUPolElt
{ Computes the equation of an integral model of y^2 = f(x). }
	f_integral := HyperellipticPolynomials(IntegralModel(HyperellipticCurve(f)));
	return f_integral;
end intrinsic;