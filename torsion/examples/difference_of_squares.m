

run_difference_of_squares := function(g : t_bound := 200)
	print "Running difference of squares for genus", g;
	pqs := AllPQPairs(2, 2 * g + 1, 2 * g + 2);

	torsion_dict := AssociativeArray();

	error_pqs := [];
	for pq in pqs do
		print "pq", pq;
		try
			fs, orders := TorsionDifferenceOfSquares(pq : t_bound := t_bound);
			for i in [1..#fs] do
				if orders[i] gt 1 then
					InsertIntoTorsionDict(~torsion_dict, fs[i], orders[i]);
				end if;
			end for;
			SummariseTorsion(torsion_dict);
		catch e
			print "Error with", pq;
			error_pqs cat:= [pq];
			print e;
		end try;
	end for;

	SummariseTorsion(torsion_dict);

	return torsion_dict;
end function;


run_difference_of_squares_including_c := function(g : u_bound := 200)
	print "Running difference of squares including C for genus", g;
	pqs := AllPQPairs(2, 2 * g + 1, 2 * g + 4);
	pqs := [pq : pq in pqs | pq[1] + pq[2] le 2 * g + 2 and pq[3] + pq[4] ge 2 * g + 3];

	torsion_dict := AssociativeArray();

	error_pqs := [];
	for pq in pqs do
		print "pq", pq;
		try
			fs, orders := TorsionDifferenceOfSquaresIncludingC(pq : u_bound := u_bound);
			for i in [1..#fs] do
				if orders[i] gt 1 then
					InsertIntoTorsionDict(~torsion_dict, fs[i], orders[i]);
				end if;
			end for;
			SummariseTorsion(torsion_dict);
		catch e
			print "Error with", pq;
			error_pqs cat:= [pq];
			print e;
		end try;
	end for;

	SummariseTorsion(torsion_dict);

	return torsion_dict;
end function;
