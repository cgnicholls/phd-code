intrinsic FiveFiveFamily() -> RngUPolElt
{ Computes the curve in the (5, 5)-family in the thesis. }
    Krt5<z> := QuadraticField(5);
    K<u> := FunctionField(Krt5);
    P<x> := PolynomialRing(K);

    G1 := x^2 + (1/25*(8*z + 20)*u^2 + 4/125*z)/(u^2 + 1/5*(z + 2));
    G2 := x^2 + (1/25*(8*z + 20)*u^2 - 4/125*z)/(u^2 + 1/5*(-z - 2));
    lambda1 := -((-10*z + 25)*u^4 + 2*z*u^2 + 1/5*(2*z + 5))/u^2;
    lambda2 := -((-10*z + 25)*u^4 - 2*z*u^2 + 1/5*(2*z + 5))/u^2;
    s1 := 2/5*z;
    s2 := -2/5*z;

    assert lambda1 * G1^2 - (x-s1)^5 eq lambda2 * G2^2 - (x-s2)^5;
    return lambda1 * G1^2 - (x - s1)^5;
end intrinsic;


intrinsic FiveFiveFamily(n::RngIntElt) -> RngUPolElt
{ Computes the curve in the (5, 5)-family in the thesis, for the integer n. }
    Krt5<z> := QuadraticField(5);
    eta := (1 - z) / 2;
    u := eta^n / z;
    Q<x> := PolynomialRing(Krt5);

    G1 := x^2 + (1/25*(8*z + 20)*u^2 + 4/125*z)/(u^2 + 1/5*(z + 2));
    G2 := x^2 + (1/25*(8*z + 20)*u^2 - 4/125*z)/(u^2 + 1/5*(-z - 2));
    lambda1 := -((-10*z + 25)*u^4 + 2*z*u^2 + 1/5*(2*z + 5))/u^2;
    lambda2 := -((-10*z + 25)*u^4 - 2*z*u^2 + 1/5*(2*z + 5))/u^2;
    s1 := 2/5*z;
    s2 := -2/5*z;

    assert lambda1 * G1^2 - (x-s1)^5 eq lambda2 * G2^2 - (x-s2)^5;

    f := lambda1 * G1^2 - (x - s1)^5;
    P<x> := PolynomialRing(Rationals());
    return ChangeRing(f, Rationals());
end intrinsic;