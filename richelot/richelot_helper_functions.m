
intrinsic ComputeRichelotIsogenousCurve(Gs::[ ]) -> Rng, [ ], RngUPolElt
    { Computes the quadratic twist delta and Ls such that y^2 = Gs[1] * Gs[2] *
    Gs[3] is Richelot-isogenous to y^2 = fd, where fd = delta * Ls[1] * Ls[2] *
    Ls[3]. Returns delta, Ls, fd. }
    delta := ComputeRichelotDelta(Gs);
    Ls := ComputeRichelotLs(Gs);
    return delta, Ls, delta * Ls[1] * Ls[2] * Ls[3];
end intrinsic;


intrinsic ComputeRichelotIsogenousCurveNoDelta(splitting::SeqEnum) -> SeqEnum,
    RngUPolElt
    { Computes the splitting such that y^2 = Product(splitting) is
    Richelot-isogenous to y^2 = fd, where fd = Product(splittingd). Returns
    splittingd, fd. This is related to ComputeRichelotIsogenousCurve by
    splittingd = [Ls[1] / delta, Ls[2] / delta, Ls[3] / delta]. }
    delta := ComputeRichelotDelta(splitting);
    Ls := ComputeRichelotLs(splitting);
    splittingd := [Li / delta : Li in Ls];
    return splittingd, Product(splittingd);
end intrinsic;


intrinsic ComputeRichelotDelta(Gs::[ ]) -> FldElt
    { Computes Delta for the Richelot isogeny. Let y^2 = G1 * G2 * G3 be a genus
    2 curve admitting a Richelot isogeny via the quadratics G1, G2, G3 (with
    possibly one of the Gi being linear). Let Gi = g_i0 + gi1 * x + gi2 * x^2.
    Then the Richelot-isogenous curve is y^2 = Delta * L1 * L2 * L3 where Delta
    = det(g_ij) (1 <= i <= 3, 0 <= j <= 2). }
    assert #Gs eq 3;
    delta_mat := Matrix([[Coefficient(Gi, j) : j in [0, 1, 2]] : Gi in Gs]);
    return Determinant(delta_mat);
end intrinsic;


intrinsic ComputeRichelotLs(Gs::[ ]) -> [ ]
    { Computes the quadratics L1, L2, L3 such that y^2 = G1 * G2 * G3 is
    Richelot-isogenous to y^2 = Delta * L1 * L2 * L3. Here L1 = Derivative(G2) *
    G3 - G2 * Derivative(G3) and so on cyclically. Delta is as in
    ComputeRichelotDelta. }
    assert #Gs eq 3;
    G1 := Gs[1];
    G2 := Gs[2];
    G3 := Gs[3];
    
    L1 := Derivative(G2) * G3 - G2 * Derivative(G3);
    L2 := Derivative(G3) * G1 - G3 * Derivative(G1);
    L3 := Derivative(G1) * G2 - G1 * Derivative(G2);
    return [L1, L2, L3];
end intrinsic;
