Author: Chris Nicholls
Date: 16/7/2018

The code in this folder accompanies my PhD thesis.

Instructions to run the code:
1. Open a command prompt and navigate to the directory containing this README file.
2. Launch MAGMA by typing 'magma'.
3. Attach the 'spec' file, by running 'AttachSpec("spec");' in MAGMA.
4. Now you can run any of the 'intrinsics' as if they are functions that already exist in MAGMA.

The individual files contain more detailed instructions in the README.txt files in their directory.

References to this code in the thesis.

Page 21: you can compute the characteristic polynomial of the Jacobian of y^2 = f(x) over the finite field with p elements by running 'ZetaFunctionOfJacobian(f, p);'.

Page 26: you can run the criterion to check if the Jacobian of y^2 = f(x) is geometrically simple by running 'IsGeometricallySimple(f);'. If the degree of f is 5 or 6 then you can run Leprevost's criterion using 'IsGeometricallySimpleLeprevost(f)'.

Page 74: the file 'vector_space_polynomials.m' contains many intrinsics for computing linear relations between polynomials.

Page 84: the intrinsic 'FindKummerCoordinatesGenus3' derives the eta1, ..., eta8 as on page 83 of the thesis. We then change basis as on page 83. To get the sigma1, ..., sigma8, use the intrinsic 'KummerCoordinatesGenus3Superelliptic'.

Page 85: The intrinsic 'CheckKummerCoordinatesSuperelliptic' checks the Kummer relations on y^2 = f(x) for any given polynomial f(x). See the kummer_coordinates/README.txt for more details.

Page 102: See richelot/derive_richelot_on_kummer.m to derive the Richelot isogeny as in section 5.7

Page 111: See richelot/derive_richelot_on_kummers_using_WT.m to derive the Richelot isogeny using the translation by 2-torsion matrices.

Page 119: See five_five/five_five_interpolation.m to derive the (5, 5)-isogeny.

Page 126: See four_four/four_four_classification.m for the proof of the quartic discriminants.

Page 170: See four_four/selmer_groups_general.m and four_four/four_four_descent.m.

Page 196: See torsion/found_torsion_curves.m for the curves in the tables.