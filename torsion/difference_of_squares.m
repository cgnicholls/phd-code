intrinsic TorsionDifferenceOfSquares(pq::SeqEnum : t_bound := 200) -> SeqEnum, SeqEnum
	{ Searches for solutions to 
	A^2 - f = lambda * x^p1 * (x-1)^q1
	B^2 - f = mu * x^p2 * (x-1)^q2,
	where 2g + 1 <= p1 + p2 <= p2 + q2 <= 2g + 2.

	First reduces to only one parameter, t, instead of lambda and mu.

	Parameters: pq should be of the form [p1, q1, p2, q2].

	If necessary, looks for specialisations in t up to height t_bound. }

	K<t> := FunctionField(Rationals());
	P<x> := PolynomialRing(K);

	// Compute the genus.
	g := Ceiling((pq[1] + pq[2]) / 2) - 1;

	assert g ge 1;

	// Check pq is in the right range, and reorder so that the sum of the first
	// two elements are at most the sum of the last two.
	assert pq[1] + pq[2] in [2 * g + 1, 2 * g + 2];
	assert pq[3] + pq[4] in [2 * g + 1, 2 * g + 2];
	if pq[1] + pq[2] gt pq[3] + pq[4] then
		pq := pq[3..4] cat pq[1..2];
	end if;

	// Eliminate lambda, mu differently depending on whether or not
	// the last two pqs are 2 * g + 2 or 2 * g + 1.
	if pq[3] + pq[4] eq 2 * g + 2 then
		rhs1 := t * x^pq[1] * (x-1)^pq[2];
		rhs2 := x^pq[3] * (x-1)^pq[4];
		g_bound := g + 1;
	else
		rhs1 := t * x^pq[1] * (x-1)^pq[2];
		rhs2 := t * x^pq[3] * (x-1)^pq[4];
		g_bound := g;
	end if;
	rhs := rhs1 - rhs2;

	max_degree := MaxDegreeOfFactor(rhs);

	// First search for some specialisations in t for which the maximum degree is less
	// than max_degree.
	ts := [t0 : t0 in RationalsUpToHeight(t_bound) |
		MaxDegreeOfFactor(SpecialisePolynomial(rhs, [t0])) le Min(max_degree - 1, g_bound) and t0 ne 0];
	ts := [t] cat ts;

	pairs := [];
	ts_list := [];
	for t0 in ts do
		new_pairs := FactorIntoProductOfMaxDegree(SpecialisePolynomial(rhs, [t0]), g_bound);
		pairs cat:= new_pairs;
		ts_list cat:= [t0 : i in [1..#new_pairs]];
	end for;
	if #ts_list gt 0 then
		print "ts";
		PrintOneLine(Sort(UniqueElements(ts_list)));
	end if;

	fs := [];
	heuristic_orders := [];
	for i in [1..#pairs] do
		pair := pairs[i];
		t0 := ts_list[i];
		A := (pair[1] + pair[2]) / 2;
		B := (pair[1] - pair[2]) / 2;
		f := SpecialisePolynomial(A^2 - rhs1, [t0]);
		assert A^2 - B^2 eq SpecialisePolynomial(rhs, [t0]);
		assert B^2 - SpecialisePolynomial(rhs2, [t0]) eq f;
		
		// Remove multiple factors from f.
		f := RemoveMultipleFactors(f);

		if Degree(f) lt 3 then
			continue;
		end if;

		order := HeuristicTorsionOrder(f);

		if order gt 1 then
			Append(~fs, f);
			Append(~heuristic_orders, order);
		end if;
	end for;

	return fs, heuristic_orders;
end intrinsic;


intrinsic TorsionDifferenceOfSquaresIncludingC(pq::SeqEnum : u_bound := 100)
	-> SeqEnum, SeqEnum
	{ Searches for solutions to 
	A^2 - f = lambda * x^p1 * (x-1)^q1
	B^2 - f = mu * x^p2 * (x-1)^q2,
	where 2g + 1 <= p1 + p2 <= 2g + 2, and 2g + 3 <= p2 + q2 <= 2g + 4.

	First reduces to only one parameter, t, instead of lambda and mu.

	Parameters: pq should be of the form [p1, q1, p2, q2].

	If necessary, looks for specialisations in t up to height t_bound. }

	// We need the first pqs to add to 5 and the next to add to 7.
	K<s, t, u> := FunctionField(Rationals(), 3);
	OK := Integers(K);
	P<x> := PolynomialRing(K);
	C := x - u;

	// Compute the genus.
	g := Ceiling((pq[1] + pq[2]) / 2) - 1;
	assert g ge 1;

	// Check pq is in the right range.
	assert pq[1] + pq[2] in [2 * g + 1, 2 * g + 2];
	assert pq[3] + pq[4] in [2 * g + 3, 2 * g + 4];

	// Eliminate lambda, mu differently depending on whether or not
	// any of the sums are even. If any is even, then we can set its parameter
	// (lambda or mu, respectively) to 1. If both are odd, we have lambda = mu.
	if pq[1] + pq[2] mod 2 eq 0 then
		lambda := 1;
		mu := s;
	elif pq[3] + pq[4] mod 2 eq 0 then
		lambda := s;
		mu := 1;
	else
		lambda := s;
		mu := s;
	end if;
	rhs1 := lambda * x^pq[1] * (x-1)^pq[2];
	rhs := mu * x^pq[3] * (x-1)^pq[4] - lambda * x^pq[1] * (x-1)^pq[2] * C^2;

	g_bound := g + 2;

	u0s := [u0 : u0 in RationalsUpToHeight(u_bound) | u0 ne 0 and u0 ne 1];
	// u0s := [u] cat u0s;

	print Factorisation(rhs);

	max_degree := MaxDegreeOfFactor(rhs);

	u0s := [u0 : u0 in RationalsUpToHeight(u_bound) | u0 ne 0 and u0 ne 1 and 
		MaxDegreeOfFactor(SpecialisePolynomial(rhs, [s, t, u0])) lt max_degree];

	// If we don't get any u0s then just try a few small ones.
	if #u0s eq 0 then
		u0s := [u0 : u0 in RationalsUpToHeight(5) | u0 ne 0 and u0 ne 1];
	end if;

	fs := [];
	all_orders := [];

	error_pqs := [];

	print "u0s";
	PrintOneLine(u0s);
	for u0 in u0s do
		pairs := FactorIntoProductOfMaxDegree(SpecialisePolynomial(rhs, [s, t, u0]), g_bound);
		for pair in pairs do
			try
				G1 := pair[1];
				G2 := pair[2];
				AC := (G1 - G2) / 2;
				B := (G1 + G2) / 2;
				assert SpecialisePolynomial(B^2 - AC^2 - rhs, [s, t, u0]) eq 0;
				// Need to ensure that A * C is divisible by C, i.e. has a root at u.
				condition := OK!Numerator(Evaluate(SpecialisePolynomial(AC, [s, t, u0]), u0));

				s0 := -Coefficient(condition, OK!s, 0) / Coefficient(condition, OK!s, 1);
				AC0 := SpecialisePolynomial(AC, [s0, t, u0]);
				C0 := SpecialisePolynomial(C, [s0, t, u0]);
				assert IsDivisibleBy(AC0, C0);
				A := AC0 div C0;

				f := SpecialisePolynomial(A^2 - rhs1, [s0, t, u0]);
				
				assert SpecialisePolynomial(B^2 - f * C^2, [s0, t, u0]) eq
					SpecialisePolynomial(mu * x^pq[3] * (x-1)^pq[4], [s0, t, u0]);

				f := P!RemoveMultipleFactors(f);
				if Degree(f) lt 5 then
					continue;
				end if;
				if Degree(f) in [5, 6] then
					order := TorsionOrderGenus2(RandomSpecialisation(f));
				else
					order := HeuristicTorsionOrder(RandomSpecialisation(f));
				end if;
				if order gt 1 then
					Append(~fs, f);
					Append(~all_orders, order);
				end if;
			catch e
				print e;
				Append(~error_pqs, pq);
			end try;
		end for;
	end for;
	return fs, all_orders;
end intrinsic;
