

three_polynomials_two_points := function(pq)
	K<a0,a1,a2,a3,b0,b1,b2,b3,c0,c1,c2,c3,l1,l2,l3> := PolynomialRing(Rationals(), 15);

	P<x> := PolynomialRing(K);

	A := x^4 + a3 * x^3 + a2*x^2 + a1*x + a0;
	B := x^4 + b3 * x^3 + b2*x^2 + b1*x + b0;
	C := x^4 + c3 * x^3 + c2*x^2 + c1*x + c0;

	avoid := [l1, l2, l3];

	extra_relations := [l1 - 1];

	polys := [A^2 - l1*x^pq[1][1]*(x-1)^pq[1][2], B^2 - l2*x^pq[2][1]*(x-1)^pq[2][2], C^2 - l3*x^pq[3][1]*(x-1)^pq[3][2]];

	eqns := Coefficients(polys[1] - polys[2]) cat Coefficients(polys[1] - polys[3]);

	return polys[1], eqns, avoid, extra_relations;
end function;


even_degree_with_rational_points_at_infinity := function(pq)
	K<a0,a1,a2,b0,b1,b2,l1,l2> := PolynomialRing(Rationals(), 8);

	P<x> := PolynomialRing(K);

	A := x^3 + a2*x^2 + a1*x + a0;
	B := x^3 + b2*x^2 + b1*x + b0;

	avoid := [l1, l2];

	extra_relations := [];

	polys := [A^2 - l1*x^pq[1][1]*(x-1)^pq[1][2], B^2 - l2*x^pq[2][1]*(x-1)^pq[2][2]];

	eqns := Coefficients(polys[1] - polys[2]);

	return polys[1], eqns, avoid, extra_relations;
end function;


weierstrass_points := function(pq : mu_spec := 16/15)
    K<h0,h1,h2,h3,h4, a0,a1,a2,a3, b0,b1,b2,b3, l1,l2> := PolynomialRing(Rationals(), 15);
    P<x> := PolynomialRing(K);

    f := (x-mu_spec) * P!Polynomial(P, [h0,h1,h2,h3,h4]);
    A := P!Polynomial(P, [a0,a1,a2,a3]);
    B := P!Polynomial(P, [b0,b1,b2,b3]);

    poly := A^2 - l1 * x^pq[1][1] * (x-1)^pq[1][2] * (x-mu_spec)^pq[1][3];

    eqns := Coefficients(A^2 - f - l1 * x^pq[1][1] * (x-1)^pq[1][2] * (x-mu_spec)^pq[1][3]) cat
    	Coefficients(B^2 - f - l2 * x^pq[2][1] * (x-1)^pq[2][2] * (x-mu_spec)^pq[2][3]);

    extra_relations := [a3];
    avoid := [l1, l2];
    return f, eqns, avoid, extra_relations;
end function;

get_polynomials := three_polynomials_two_points;
pqs := AllPQ(2, 3, 1, 7);

// get_polynomials := even_degree_with_rational_points_at_infinity;
// pqs := AllPQ(2, 2, 1, 5);

// get_polynomials := weierstrass_points;
// pqs := AllPQ(3, 2, 1, 5);
// pqs := [[[3, 1, 1], [1, 5, 0]]];

pqs := RandomOrder(pqs);
torsion_dict := AssociativeArray();
for i in [1..#pqs] do
	print "Progress", i, "/", #pqs;
	pq := pqs[i];
	print "pq", pq;
	fs, orders := search_for_curves(pq, get_polynomials);
	for i in [1..#fs] do
		if orders[i] gt 1 then
			InsertIntoTorsionDict(~torsion_dict, fs[i], orders[i]);
		end if;
	end for;
	SummariseTorsion(torsion_dict);
end for;



simple_torsion_dict := SummariseTorsionOnSimpleCurves(torsion_dict);

print "On the simple curves, we found the following torsion:";
SummariseTorsion(simple_torsion_dict);


