// In this file we run the computations accompanying the partial classification of (4, 4)-isogenies whose kernels are elementwise rational.
AttachSpec("spec");

K<a, b, c> := FunctionField(Rationals(), 3);
P<x> := PolynomialRing(K);
// Let C2 be the curve with splitting equal to splittingd.
splittingd := [x, (x-1) * (x-a), (x-b) * (x-c)];

// The Richelot isogeny via splittingd maps onto C1. We let splitting be the dual splitting to splittingd.
// Thus the Richelot isogeny via 'splitting' takes J1 to J2 (Ji being the Jacobian of Ci). This is the first
// Richelot isogeny in the composition that will be a (4, 4)-isogeny. The second Richelot isogeny is a different
// Richelot isogeny on J2 (not the one via splittingd).
splitting := ComputeRichelotIsogenousCurveNoDelta(splittingd);
f := Product(splitting);

// Let T1, T2, T3 be the 2-torsion points on J1 corresponding to the quadratics in splitting.
// Let W1, W2, W3 be the translation by T1, T2, T3 matrices, respectively.
W1, W2, W3 := ComputeAdditionByTwoTorsionOnKummer(splitting);

// Check that each Wi is diagonalisable over Q.
assert #Roots(MinimalPolynomial(W1)) eq 2;
assert #Roots(MinimalPolynomial(W2)) eq 2;
assert #Roots(MinimalPolynomial(W2)) eq 2;

// Compute the eigenspaces for each Wi.
discriminants := [];
for W in [W1, W2, W3] do
    eigenspaces := ComputeEigenspaces(W);

    // The roots of the following homogeneous equations give the solution for an eigenvector
    // of W to lie on the Kummer surface.
    eqn1 := ComputeHomogeneousEquationForLinearCombinationsOnTheKummer(eigenspaces[1], f);
    eqn2 := ComputeHomogeneousEquationForLinearCombinationsOnTheKummer(eigenspaces[2], f);

    // Factor each equation
    factors1 := [factor[1] : factor in Factorisation(eqn1)];
    factors2 := [factor[1] : factor in Factorisation(eqn2)];

    // Check they are both products of irreducible quadratics.
    assert [ Degree(factor) : factor in factors1 ] eq [2, 2];
    assert [ Degree(factor) : factor in factors2 ] eq [2, 2];

    // Compute the discriminants of the quadratics modulo squares.
    discs1 := [HomogeneousDiscriminant(factor) : factor in factors1];
    discs2 := [HomogeneousDiscriminant(factor) : factor in factors2];

    discs_mod_squares1 := [Product(FactorModSquares(NumeratorTimesDenominator(disc))) : disc in discs1];
    discs_mod_squares2 := [Product(FactorModSquares(NumeratorTimesDenominator(disc))) : disc in discs2];

    assert { IsSquare(discs_mod_squares1[i] / discs1[i]) : i in [1..#discs1] } eq { true };
    assert { IsSquare(discs_mod_squares2[i] / discs2[i]) : i in [1..#discs2] } eq { true };

    Append(~discriminants, discs_mod_squares1 cat discs_mod_squares2);
end for;

print "The discriminants for the factors are";
print discriminants;