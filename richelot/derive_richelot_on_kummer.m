K<g10,g11,g12,g20,g21,g22,g30,g31,g32> := FunctionField(Rationals(), 9);
P<x> := PolynomialRing(K);

Pk<k1,k2,k3,k4> := PolynomialRing(K, 4);

splitting := [P!Polynomial(P, [g10,g11,g12]),
              P!Polynomial(P, [g20,g21,g22]),
              P!Polynomial(P, [g30,g31,g32])];

// We first have to find the functions that are invariant under translation by
// T1 and T2 on the Kummer surface.

W1, W2, W3 := ComputeAdditionByTwoTorsionOnKummer(splitting);

xi := Matrix(Pk, [[k1], [k2], [k3], [k4]]);

xi_T1 := ChangeRing(W1, Pk) * xi;
xi_T2 := ChangeRing(W2, Pk) * xi;

eta1 := [xi[i][1] * xi_T1[j][1] + xi[j][1] * xi_T1[i][1] : i, j in [1..4]];
eta2 := [xi[i][1] * xi_T2[j][1] + xi[j][1] * xi_T2[i][1] : i, j in [1..4]];

// Compute a vector space for the polynomials and the subspaces generated by
// eta1 and eta2.
V, monomials := VectorSpaceForPolynomials(eta1 cat eta2);
sub1 := SubspaceOfPolynomials(eta1, monomials);
sub2 := SubspaceOfPolynomials(eta2, monomials);

// Compute the intersection of the two subspaces. These are the vectors for the
// polynomials that are invariant under translation by T1 and T2.
intersection := sub1 meet sub2;

// Compute a basis for the intersection, and convert to polynomials again.
invariant_functions := [VectorToPolynomial(poly, monomials) : poly in
    Basis(intersection)];

f := Product(splitting);
kum_eqn := ComputeKummerEquation(f);
kum_eqn := hom<Parent(kum_eqn)->Pk | k1,k2,k3,k4>(kum_eqn);

// We now transform the invariant functions so that they start with k1 * k4, k2
// * k4, k3 * k4, k4 * k4, respectively, and so that these are the only ki * k4
// terms.
M := Matrix(K, [[MonomialCoefficient(poly, mon) : mon in [k1*k4, k2*k4, k3*k4,
    k4*k4]] : poly in invariant_functions]);
invariant_functions_M := Transpose(Matrix(Pk, [invariant_functions]));
N := ChangeRing(M, Pk)^-1 * invariant_functions_M;
li := [N[i][1] : i in [1..4]];
M2 := Matrix(K, [[MonomialCoefficient(poly, mon) : mon in [k1*k4, k2*k4, k3*k4,
    k4*k4]] : poly in li]);
assert M2 eq IdentityMatrix(Pk, 4);

// Compute the monomials that can occur in the Kummer equation, now that we have
// normalised the quartics.
kummer_monomials := [k4^2 * k2^2, k4^2 * k1 * k3] cat [k4 * mon : mon in
    DegreeNCombinations([k1,k2,k3], 3)] cat DegreeNCombinations([k1,k2,k3], 4);

// First compute the power series.
time power_series := JacobianPowerSeriesUpToDegreeSpecialised(f, 4);
li_power_series := [ComputePowerSeriesForKummerFunction(poly,
    power_series) : poly in li];
li_power_series_10 := [ComputeSum([term : term in Terms(poly) |
    Degree(term) le 9]) : poly in li_power_series];
kummer_monomials_cubic := [mon : mon in kummer_monomials | Degree(mon, k4) ge
    1];
time quartics_power_series := [hom<Pk->Universe(power_series) |
    li_power_series_10>(mon) : mon in kummer_monomials_cubic];
quartics_power_series_22 := [TermsOfMaxDegree(poly, 22) : poly in
    quartics_power_series];
time nullspace := LinearRelationsBetweenPolynomials(quartics_power_series_22);

// We thus have a putative Kummer equation.
kum_eqnd_v := Basis(nullspace)[1];
kum_eqnd := ComputeSum([kum_eqnd_v[i] * kummer_monomials_cubic[i] : i in
    [1..#kummer_monomials_cubic]]);

// But we need to transform so that there are no k4*k2^3, k4*k2^2*k1, k4*k2^2*k3
// terms. Let bi be their coefficients.
// Because the Kummer equation is of the form k4^2 * (k2^2 - 4*k1*k3) + k4 *
// Phi(k1,k2,k3) + Psi(k1,k2,k3), where Phi is cubic and Psi is quartic, we find
// that the change of variables k4 = k4d + a1*k1 + a2*k2 + a3*k3 gives us the
// equation k4d^2 * (k2^2 - 4*k1*k3) + 2*k4d*k2^2*(a1*k1+a2*k2+a3*k3) +
// k4d*Phi(k1,k2,k3) + Psid. In particular, we can cancel the terms k4*k2^2*ki
// (i = 1,2,3) by putting ai = -bi/2.
kum_eqnd_transformed, bi := KummerEquationWithoutBadMonomials(kum_eqnd);

// Thus we want to 
fd := ReadCurveFromKummer(kum_eqnd_transformed);

// Check that we got the correct fd.
_, _, fd_expected := ComputeRichelotIsogenousCurve(splitting);
assert NormalisePolynomial(fd) eq NormalisePolynomial(fd_expected);

// We now expect the Kummer equation to be the one for the isogenous curve.
expected_kum_eqnd_transformed := ComputeKummerEquation(fd);

// Transform back to the coordinates that the quartics are in. We want to check
// that they satisfy this equation.
expected_kum_eqnd := hom<Pk->Pk | k1,k2,k3,k4 + bi[1]/2*k1 + bi[2]/2*k2 +
    bi[3]/2*k3>(expected_kum_eqnd_transformed);

// We should have that li_power_series satisfy kum_eqnd up to and including
// terms of degree 22.
time result1 := hom<Pk->Universe(power_series) | li_power_series_10>(kum_eqnd);
assert TermsOfMaxDegree(result1, 22) eq 0;

time result2 := hom<Pk->Universe(power_series) |
    li_power_series_10>(expected_kum_eqnd);


// Now just solve those equations to find the following solution. You can do
// this by first looking at the last equation, which determines b3, and then
// finding an equation that is linear in b2, and finally, find an equation that
// is linear in b1.
//Pa<a1,a2,a3> := FunctionField(K, 3);
//Qa<b1,b2,b3> := Integers(Pa);
//Pkk<kk1,kk2,kk3,kk4> := PolynomialRing(Pa, 4);
//
//hom_kk := hom<Pk->Pkk | kk1,kk2,kk3,kk4>;
//li_kk := [hom_kk(elt) : elt in li];
//li_a := li_kk[1..3] cat [li_kk[4] + a1 * li_kk[1] + a2 * li_kk[2] + a3 *
//    li_kk[3]];
//time result := hom<Pkk->Pkk | li_a>(hom_kk(expected_kum_eqnd_transformed));
//time result_reduced := ReduceModKummerEquation(result, hom_kk(kum_eqn));
//eqns := [Qa!coeff : coeff in Coefficients(result_reduced)];

// We find the following result.
bs := [(-4*g10^2*g20*g22*g31*g32 + 4*g10^2*g21*g22*g30*g32 -
2*g10*g11*g20*g22*g31^2 + 2*g10*g11*g21^2*g30*g32 + 4*g10*g12*g20^2*g31*g32 +
2*g10*g12*g20*g21*g31^2 - 2*g10*g12*g21^2*g30*g31
    - 4*g10*g12*g21*g22*g30^2 - 2*g11^2*g20*g21*g30*g32 +
      2*g11^2*g20*g22*g30*g31 - 4*g11*g12*g20^2*g30*g32 +
      4*g11*g12*g20*g22*g30^2)/(g10*g21*g32 - g10*g22*g31 - g11*g20*g32 +
      g11*g22*g30 + g12*g20*g31 - g12*g21*g30),
    (-2*g10*g11*g20*g22*g31*g32 + 2*g10*g11*g21*g22*g30*g32 +
2*g10*g12*g20*g21*g31*g32 - 2*g10*g12*g21*g22*g30*g31 -
2*g11*g12*g20*g21*g30*g32 + 2*g11*g12*g20*g22*g30*g31)/(g10*g21*g32
    - g10*g22*g31 - g11*g20*g32 + g11*g22*g30 + g12*g20*g31 - g12*g21*g30),
    (-4*g10*g11*g20*g22*g32^2 + 4*g10*g11*g22^2*g30*g32 +
4*g10*g12*g20*g21*g32^2 + 2*g10*g12*g21^2*g31*g32 - 2*g10*g12*g21*g22*g31^2 -
4*g10*g12*g22^2*g30*g31 - 2*g11^2*g20*g22*g31*g32 + 2*g11^2*g21*g22*g30*g32 +
2*g11*g12*g20*g22*g31^2 - 2*g11*g12*g21^2*g30*g32 - 4*g12^2*g20*g21*g30*g32 +
4*g12^2*g20*g22*g30*g31)/(g10*g21*g32 - g10*g22*g31 - g11*g20*g32 + g11*g22*g30
+ g12*g20*g31 - g12*g21*g30)];

li_b := li[1..3] cat [li[4] + bs[1] * li[1] + bs[2] * li[2] + bs[3] * li[3]];
time check_eqn := hom<Pk->Pk | li_b>(expected_kum_eqnd_transformed);
time check_eqn_reduced := ReduceModKummerEquation(check_eqn, kum_eqn);
assert check_eqn_reduced eq 0;

// Check all of this over specialisations.
Pt<t1,t2,t3,t4> := PolynomialRing(Rationals(), 4);
spec_hom := hom<Pk->Pt | hom<K->Rationals() | -1, 2, 3, 11, 5, 6,
    -5, -8, 9>, Pt.1, Pt.2, Pt.3, Pt.4>;
li_b_spec := [spec_hom(lli) : lli in li_b];

check_eqn_spec := ReduceModKummerEquation(hom<Pk->Pt |
    li_b_spec>(spec_hom(expected_kum_eqnd_transformed)), spec_hom(kum_eqn));
assert check_eqn_spec eq 0;