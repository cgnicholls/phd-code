Important intrinsics:

'RichelotOnKummerMap' computes the Richelot map on Kummer surfaces, given a splitting. Example usage:
----------
AttachSpec("spec");
P<x> := PolynomialRing(Rationals());
splitting := [x, x^2 + 2, x^2 + x + 1];
richelot_map := RichelotOnKummerMap(splitting);

// Let Kum1 be the domain of this map
Kum1 := Domain(richelot_map);
// Kum1 contains the following 2-torsion points (which are just the kernel of the Richelot isogeny)
two_torsion := TwoTorsionOnKummer(Kum1);
print two_torsion;
// We can compute the image under the Richelot isogeny:
print [richelot_map(pt) : pt in two_torsion];

// We check that each point maps to the identity on Kum2.
Kum2 := Codomain(richelot_map);
assert richelot_map(two_torsion[1]) eq Kum2![0, 0, 0, 1];
assert richelot_map(two_torsion[2]) eq Kum2![0, 0, 0, 1];
assert richelot_map(two_torsion[3]) eq Kum2![0, 0, 0, 1];

// Kum1 also has the point [1, 1, 0, 2]. We compute its image under the Richelot isogeny, and check that
// applying the Richelot isogeny and then its dual gives the same as doubling the point on the Kummer.
pt := Kum1![1, 1, 0, 2];
dual_richelot_map := DualRichelotOnKummerMap(splitting);
assert dual_richelot_map(richelot_map(pt)) eq Double(pt);
----------




To derive the Richelot isogeny, run the program 'richelot/derive_richelot_on_kummer.m':
----------
AttachSpec("spec");
load "richelot/derive_richelot_on_kummer.m";
----------




To derive the Richelot isogeny using the addition by 2-torsion matrices W_T for any given Richelot splitting, run the intrinsic 'ComputeRichelotChangeOfBasis(splitting)':
----------
AttachSpec("spec");
P<x> := PolynomialRing(Rationals());
splitting := [x^2 + 1, x^2 + 5, x^2 + x + 1];
ComputeRichelotChangeOfBasis(splitting);
----------
The code for this is in 'richelot/derive_richelot_on_kummers_using_WT.m'