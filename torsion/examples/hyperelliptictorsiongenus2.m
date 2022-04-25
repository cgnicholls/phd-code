num_points := 2;
num_polys := 2;
g := 2;
min := 5;
max := 5;
pqs := AllPQ(num_points, num_polys, min, max);

pqs := RandomOrder(pqs);

//pqs := [[[3,1,1],[1,5,0]]];
//pqs := [[[4,1],[1,4]]];
extra_relations := [];
extra_relations := [[4, 0], [9, 1]];
// extra_relations := [[4,1], [8,1], [12,1]];
// extra_relations := [[1,3],[2,1], [8,0], [6,0], [6,0]];
// extra_relations := [[1,2/5], [4,0], [11,16/15]];
print "Hypers", num_points, num_polys, min, max;
print "Searching with extra relations";
print extra_relations;
//print "Possible determinants", {Abs(Determinant(Matrix(pq))) : pq in pqs};

torsion_dict := AssociativeArray();
for i in [1..#pqs] do
    pq := pqs[i];
    print "Searching", i, "/", #pqs;
    print "pq", pq;
    try
        curves := CurvesForPQ(pq, g, num_points, num_polys, extra_relations, true);
        curves, orders := HeuristicTorsionOrder(curves);
        for i in [1..#curves] do
            if orders[i] gt 1 then
                InsertIntoTorsionDict(~torsion_dict, curves[i], orders[i]);
            end if;
        end for;
        print "Num torsion:", #torsion_dict;
        SummariseTorsion(torsion_dict);
    catch e
        print e;
    end try;
end for;

