Author: Chris Nicholls

To run this, first follow the instructions in the README.txt file in the main directory to open MAGMA and attach the spec file.

To derive the Kummer coordinates in genus 3, see the intrinsic 'FindKummerCoordinatesGenus3'. You can run this by running 'FindKummerCoordinatesGenus3();' in MAGMA. This derives eta1, ..., eta8 as on page 83 of the thesis. To get the sigma1, ..., sigma8, use the intrinsic 'KummerCoordinatesGenus3Superelliptic'. For example, run the snippet between the dashed lines:
----------
// The general sigma:
sigma := KummerCoordinatesGenus3Superelliptic();
print sigma;

// The sigma for y^2 = x^4 + x + 1:
P<x> := PolynomialRing(Rationals());
f := x^4 + x + 1;
sigma_for_f := KummerCoordinatesGenus3Superelliptic(f);
print sigma_for_f;
----------


To verify the Kummer relations in genus 3, see the intrinsic 'CheckKummerCoordinatesSuperelliptic'. You can run this by running 'CheckKummerCoordinatesSuperelliptic(f);' for any polynomial f(x) of degree 4. For example, run the snippet between the dashed lines:
----------
P<x> := PolynomialRing(Rationals());
f := x^4 + x + 1;
CheckKummerCoordinatesSuperelliptic(f);
----------

