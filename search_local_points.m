intrinsic SearchLocalPointsOnKummer(f::RngUPolElt, Qp::FldPad : Bound := 10) ->
    SetIndx
    { Searches for local points on the Kummer of y^2 = f(x) over Qp. }
    p := Prime(Qp);
    Cp := ChangeRing(HyperellipticCurve(f), Qp);
    Jp := Jacobian(Cp);
    Kump := KummerSurface(Jp);

    starting_points := [[p^-1,a,b] : a, b in [0..Bound]];
    starting_points := [[1,a,b] : a, b in [-Bound..Bound]];
    starting_points := [[0,a,b] : a, b in [-Bound..Bound]];
    starting_points cat:= [[p,a,b] : a, b in [-Bound..Bound]];
    starting_points cat:= [[Random(p) : i in [1..3]] : j in [1..Bound]];
    starting_points cat:= [[p,Random(p),Random(p)] : j in [1..Bound]];

    // Also include 2-torsion points.
    if (p ne 2) then
        two_torsion := TwoTorsionOnKummer(ChangeRing(f, Qp));
        kummer_points := {Kump!pt : pt in two_torsion};
    else
        kummer_points := {};
    end if;

    for start in starting_points do
        try
            kummer_points join:= {pt : pt in Points(Kump, start)};
        catch e
            print "Trying to find point on Kummer with starting coords", start;
            print e;
        end try;
    end for;

    return {@ pt : pt in kummer_points @};
end intrinsic;


intrinsic SearchLocalPointsOnCurve(f::RngUPolElt, Qp::FldPad : Bound := 10) ->
    SetIndx
    { Searches for local points on the hyperelliptic curve y^2 = f(x) over the
    field Qp up to points with x-coordinates of height Bound. }
    
    p := Prime(Qp);
    x_coords := [i : i in [0..Max(p, Bound)]];
    //x_coords cat:= [x / p : x in x_coords];
    x_coords cat:= [-x : x in x_coords];
    Cp := ChangeRing(HyperellipticCurve(f), Qp);
    points := [];
    for x in x_coords do
        if IsSquare(Qp!Evaluate(f, x)) then
            _, y := IsSquare(Qp!Evaluate(f, x));
            Append(~points, Cp![x, y]);
        end if;
    end for;
    return {@ pt: pt in points | Precision(pt) gt 20 @};
    return points;
end intrinsic;


intrinsic SearchPointsOnKummerFromJacobian(f::RngUPolElt : Bound := 10)
    -> [ ]
    { Searches for points on the Kummer of the curve y^2 = f(x). }
    Kum := KummerSurface(f);

    return {@ Kum!pt : pt in SearchPointsOnJacobian(f : Bound := Bound) @};
end intrinsic;


intrinsic SearchPointsOnKummerFromJacobian(Kum::Srfc : Bound := 10)
    -> [ ]
    { Searches for points on the Kummer of the curve y^2 = f(x). }

    return SearchPointsOnKummerFromJacobian(KummerSurface(Kum));
end intrinsic;


intrinsic SearchPointsOnKummerFromJacobian(Kum::SrfKum : Bound := 10)
    -> [ ]
    { Searches for points on the Kummer of the curve y^2 = f(x). }
    J := Jacobian(Kum);

    return {@ Kum!pt : pt in Points(J : Bound := Bound) @};
end intrinsic;


intrinsic SearchLocalPointsOnJacobian(f::RngUPolElt, Qp::FldPad : Bound := 10)
    -> [ ]
    { Searches for local points on the Jacobian of the curve y^2 = f(x). }

    // First search for points on the Kummer.
    kummer_points := SearchLocalPointsOnKummer(f, Qp : Bound := Bound);

    // Now lift all the Kummer points to Jacobian points.
    Jp := BaseChange(Jacobian(HyperellipticCurve(f)), Qp);
    local_points := {Jp!0};

    num_errors := 0;
    for kum_point in kummer_points do
        try
            local_points join:= {pt : pt in Points(Jp, kum_point)};
        catch e
            num_errors +:= 1;
        end try;
    end for;
    if num_errors gt 0 then
        print "Num errors lifting Kummer points:", num_errors;
    end if;

    // Then look for points on the curve.
    curve_points := SearchLocalPointsOnCurve(f, Qp : Bound := 10*Bound);
    local_points join:= {pt - curve_points[1] : pt in curve_points};

    // Restrict to a minimum precision. A side-effect of this is that we won't
    // find the identity or any two-torsion points in this, since Precision(0) =
    // 0.
    local_points := {@ pt : pt in local_points | Precision(pt) gt 20 @};
    return local_points;
end intrinsic;


intrinsic SearchPointsOnJacobian(f::RngUPolElt : Bound := 10) -> SetIndx
    { Searches for points on the Jacobian of the curve y^2 = f(x). }
    
    J := Jacobian(HyperellipticCurve(f));

    return Points(J : Bound := Bound);
end intrinsic;


intrinsic SearchPointsOnKummerGlobal(f::RngUPolElt : Bound := 10) -> SetIndx
    { Searches for real points on the Kummer surface of y^2 = f(x). }
    // We actually just search for rational solutions to the Kummer equation.
    Kum := KummerSurface(f);
    pairs := RationalsUpToHeight(Bound, 2);
    starting_points := [[1] cat pair : pair in pairs];
    starting_points cat:= [[0] cat pair : pair in pairs];
    kum_points := {Points(Kum, starting_point) : starting_point in starting_points};
    kum_points := Union(kum_points);
    return {@ pt : pt in kum_points @};
end intrinsic;


intrinsic SearchPointsOnJacobianGlobal(f::RngUPolElt : Bound := 10) -> SetIndx
    { Searches for global points on the Jacobian of y^2 = f(x). }
    kum_pts := SearchPointsOnKummerGlobal(f : Bound := Bound);
    jac_pts := Union({Set(LiftToJacobian(pt)) : pt in kum_pts});
    torsion_pts := Set(ComputeTorsionPointsOnJacobian(f));
    jac_pts join:= torsion_pts;
    return {@ pt : pt in jac_pts @};
end intrinsic;


intrinsic SearchLocalPointsOnJacobianReals(f::RngUPolElt : Bound := 10) ->
SetIndx[SrfKumPt]
{ Searches for real points on the Jacobian of y^2 = f(x). Returns the
Kummer points that lift to the Jacobian, i.e. whose a9^2 term is square in R. }
    // We first search for rational solutions to the Kummer equation. Then we
    // know we can lift them if they have non-negative a9^2. We actually impose
    // that a9^2 > 0. If we have a9^2 = 0, then we may have to impose that some
    // other Jacobian coordinate is square.
    kum_points := SearchPointsOnKummerGlobal(f : Bound:= Bound);
    real_kum_points := {pt : pt in kum_points | Computea9Squared(pt) gt 0};
    Kum := KummerSurface(Jacobian(HyperellipticCurve(f)));
    torsion_pts := { Kum!pt : pt in ComputeTorsionPointsOnJacobian(f) };
    return SetToIndexedSet(real_kum_points join torsion_pts);
end intrinsic;
