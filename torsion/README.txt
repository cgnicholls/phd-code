Author: Chris Nicholls

This folder contains the curves we found with the methods described in Chapter 3. It also contains the programs to find them.

To see all the curves, see the file 'found_torsion_curves.m'. This contains one curve for each order of point that we found.
----------
// For example:
curves3 := TorsionCurvesGenus3();

// Print the torsion orders:
[HeuristicTorsionOrder(f) : f in curves3];

// We also have some 1-parameter families:
curves4t := TorsionCurves4Qt();
[HeuristicTorsionOrder(f) : f in curves4t];
----------


You can run the difference of squares method and difference_of_squares II method using:
----------
load "torsion/examples/difference_of_squares.m";

// Then you can run the difference of squares method in genus 2 using:
run_difference_of_squares(2);

// You can run the difference of squares II method in genus 3 using:
run_difference_of_squares_including_c(2);
----------