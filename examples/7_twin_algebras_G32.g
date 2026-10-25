## https://github.com/AlisonWarman/AlgebrasTQD
#############################################################################
##
##  7_twin_algebras_G32.g                       AlgebrasTQD examples
##
##  Twin algebras of SmallGroup(32,43) 
##  Usage: Read("path/to/AlgebrasTQD/examples/7_twin_algebras_G32.g")
##
#############################################################################

Read(ReplacedString(INPUT_FILENAME(), "7_twin_algebras_G32.g", "../AlgebrasTQD.g"));

Section := function(title) Print("\n", title, "\n\n"); end;;
AskExample7 := function(question)
    local answer;
    Print("\n", question, "\n[no/yes]\n");
    answer := ReadLine(InputTextUser());
    while answer<>fail do
        answer := LowercaseString(Filtered(answer, ch -> not ch in "\r\n \t"));
        if answer in ["no","yes"] then return answer="yes"; fi;
        Print("Please answer no or yes:\n");
        answer := ReadLine(InputTextUser());
    od;
    return false;
end;;

# Group Generators 

Section("G_32 in the notation of the Twin Algebras paper arXiv:2605.31602");
G := MakeGroup([32,43]);;
gens := First(Cartesian(Elements(G),Elements(G),Elements(G)), t ->
    Order(t[1])=8 and Order(t[2])=2 and Order(t[3])=2 and t[2]*t[3]=t[3]*t[2] and
    t[2]*t[1]*t[2]^-1=t[1]^3 and t[3]*t[1]*t[3]^-1=t[1]^5 and Group(t)=G);;
RelabelGroup(G, ["g2","g3","g1"], [gens[2],gens[3],gens[1]]);;
ShowGroup(G);
g1 := GroupElement(G,"g1");; g2 := GroupElement(G,"g2");; g3 := GroupElement(G,"g3");;

# irrep labels

classWords := [ "1", "g1g2g3", "g2g3", "g3", "g1^2", "g1^4", "g1", "g1g2", "g2", "g3g1^2", "g1g3" ];;
classReps := List(classWords, w -> GroupElement(G,w));;
if Length(Set(classReps, g -> ConjugacyClass(G,g)))<>Length(ConjugacyClasses(G)) then
    ErrorNoReturn("The classes of the character table of G_32 in arXiv:2605.31602 are not all the conjugacy classes of G");
fi;
paperChars := [
    [ 1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1 ],
    [ 1, -1,  1,  1,  1,  1, -1, -1,  1,  1, -1 ],
    [ 1,  1, -1,  1,  1,  1, -1,  1, -1,  1, -1 ],
    [ 1, -1, -1,  1,  1,  1,  1, -1, -1,  1,  1 ],
    [ 1,  1,  1, -1,  1,  1,  1, -1, -1, -1, -1 ],
    [ 1, -1,  1, -1,  1,  1, -1,  1, -1, -1,  1 ],
    [ 1,  1, -1, -1,  1,  1, -1, -1,  1, -1,  1 ],
    [ 1, -1, -1, -1,  1,  1,  1,  1,  1, -1, -1 ],
    [ 2,  0,  0,  2, -2,  2,  0,  0,  0, -2,  0 ],
    [ 2,  0,  0, -2, -2,  2,  0,  0,  0,  2,  0 ],
    [ 4,  0,  0,  0,  0, -4,  0,  0,  0,  0,  0 ] ];;
paperLabels := Concatenation(["([1],1)"], List([1..9], n -> Concatenation("([1],r_",String(n),")")), ["([1],r_{10})"]);;

IrrepLabels := function(th, show)
    local labels, i, ch, n;
    labels := ShallowCopy(th.labels);
    for i in Filtered([1..Length(th.aG)], i -> IsOne(th.aG[i][1])) do
        ch := List(classReps, g -> LookupDictionary(th.aG[i][2], g));
        n := Position(paperChars, ch);
        if n=fail then ErrorNoReturn("The character ", ch, " of ", th.labels[i], " is not in the character table of G_32 in arXiv:2605.31602"); fi;
        if show then Print(String(th.labels[i], -26), " = ", paperLabels[n], "\n"); fi;
        labels[i] := paperLabels[n];
    od;
    if Length(Set(labels))<>Length(labels) then ErrorNoReturn("Two anyons have the same label"); fi;
    return labels;
end;;

ShowTwins := function(th, M)
    local k, i;
    Print(Length(M.classes), " algebra classes, ", Length(M.twins), " twin pairs\n");
    for k in [1..Length(M.twins)] do
        Print("\nTwin pair ", k, ", inequivalent since ",
              First(M.reasons, x -> Set(x[1]) = Set(M.twins[k]))[2], ":\n");
        for i in M.twins[k] do ShowAlgData(th, M.classes[i], rec(opP := "short"));; od;
    od;
end;;

Section("Irreps of G_32 matched to the character table of arXiv:2605.31602");
th := TQDTheory(G);;
th.labels := IrrepLabels(th, true);;

Section("All twin pairs in Z(Vec_G32)");
M := AlgebraClasses(th);;
ShowTwins(th, M);

# N-type twin pair

Section("The N-type twin pair of Z(Vec_G32)");
H3 := Group(g2, g3, g1^4);;
N := Group(g3);; Np := Group(g3*g1^4);;
NGH3 := Normalizer(G, H3);;
Print("H3 = ", StructureDescription(H3), ",  N_G(H3) = <", JoinStringsWithSeparator(List(GeneratorsOfGroup(NGH3), g -> GroupLabel(G,g)), ","),
      "> of order ", Size(NGH3), "\n");
Print("N' = g1 N g1^-1: ", Np = N^(g1^-1), ",  N, N' conjugate in N_G(H3): ", IsConjugate(NGH3, N, Np), "\n");
candidates := Filtered(M.twins, p -> ForAll(p, i -> M.classes[i].algebras[1][1] = H3));;
if Length(candidates)<>1 then ErrorNoReturn("Expected one N-type twin pair on H3"); fi;
twinsN := candidates[1];;
ShowEps := function(i)
    local A, n;
    A := M.classes[i].algebras[1];
    n := MinimalGeneratingSet(A[2])[1];
    Print("\n");
    ShowAlgData(th, M.classes[i], rec(opP := "short"));
    Print("  eps(h,", GroupLabel(G,n), ") on g2, g3, g1^4: ", List([g2,g3,g1^4], h -> A[4](h,n)), "\n");
end;;
for i in twinsN do ShowEps(i); od;
if not Set(List(twinsN, i -> M.classes[i].algebras[1][2])) = Set([N, Np]) then
    ErrorNoReturn("The N-type pair is not on N = <g3> and N' = <g3g1^4>");
fi;

# H-type Gassmann pair and its common subalgebra

Section("The H-type Gassmann pair:");
H1 := Group(g2, g3);; H2 := Group(g2*g3, g3*g1^4);;
Print("H1 and H2 conjugate in G: ", IsConjugate(G, H1, H2), "\n");
candidates := Filtered(M.twins, p -> ForAll(p, i -> IsTrivial(M.classes[i].algebras[1][2])));;
if Length(candidates)<>1 then ErrorNoReturn("Expected one H-type Klein-four twin pair"); fi;
twins := candidates[1];;
if not Set(List(twins, i -> M.classes[i].algebras[1][1]), H -> First([H1,H2], K -> IsConjugate(G,H,K))) = Set([H1,H2]) then
    ErrorNoReturn("The H-type pair is not on H1 and H2");
fi;
for i in twins do
    ShowAlgData(th, M.classes[i], rec(opP := "short"));;
od;

Section("Shared subalgebra of the H-type pair:");
Hs := Hasse(th, M);;
lower := Filtered([1..Length(M.classes)], i ->
    [i,twins[1]] in Hs.inclusions and [i,twins[2]] in Hs.inclusions);;
SortBy(lower, i -> [-M.classes[i].dim, i]);;
common := lower[1];;
Print("Largest common proper subalgebra: ", M.classes[common].name,
      " (dimension ", M.classes[common].dim, ")\n");
Print("Anyon decomposition: ", M.classes[common].decomposition, "\n");

if AskExample7("Compute twin algebras with non-trivial 3-cocycle omega?") then
    Section("The 3-cocycle omega of examples/G32-43-omega.g");
    Read(ReplacedString(INPUT_FILENAME(), "examples/7_twin_algebras_G32.g", "examples/G32-43-omega.g"));
    omEl := List(omlab, w -> GroupElement(G,w));;
    if Length(Set(omEl))<>Size(G) then ErrorNoReturn("The labels of examples/G32-43-omega.g are not the 32 elements of G"); fi;
    omPos := NewDictionary(omEl[1], true);;
    for i in [1..Length(omEl)] do AddDictionary(omPos, omEl[i], i); od;
    omega := rec(a := function(x,y,z)
        return omtab[LookupDictionary(omPos,x)][LookupDictionary(omPos,y)][LookupDictionary(omPos,z)];
    end, N := 16, G := G);;
    Print("omega is a normalized 3-cocycle: ", 3coctest([Elements(G),omega]), "\n");
    Print("omega(g1^4,g1^4,g1^4) = ", E(16)^omega.a(g1^4,g1^4,g1^4), "\n");

    thom := TQDTheory(G, omega);;
    thom.labels := IrrepLabels(thom, false);;
    Section("All twin pairs in Z(Vec_G32^omega)");
    Mom := AlgebraClasses(thom);;
    ShowTwins(thom, Mom);

    Section("The algebras on H3 = <g2,g3,g1^4> in Z(Vec_G32^omega)");
    onH3 := Filtered([1..Length(Mom.classes)], i -> IsConjugate(G, Mom.classes[i].algebras[1][1], H3));;
    Print(Length(onH3), " algebra classes on H3\n");
    for i in onH3 do ShowAlgData(thom, Mom.classes[i], rec(opP := "short"));; od;
    Print("\nomega restricted to N, N' is trivial in H^3: ", List([N, Np], K -> gammaf([K, omega]) <> fail), "\n");
    omMult := function(x,y,z) return E(omega.N)^omega.a(x,y,z); end;;
    Print("omega(h1,h2|n) on H3 is a coboundary for n = g3, g3g1^4: ",
          List([g3, g3*g1^4], n -> IsTrivial2coc([Elements(H3), function(h1,h2) return 3cocr(omMult,h1,h2,n); end]) <> fail), "\n");
    Print("The N-type pair remains a twin pair in Z(Vec_G32^omega): ",
          ForAny(Mom.twins, p -> ForAll(p, i -> i in onH3)), "\n");
fi;

if AskExample7("Run twin sweep?") then
    # Set fullSweep := true for all groups of order <= 48
    TwinType := function(G, A1, A2)
        local s, g, NGH, N2, gamma2, stab;
        if A1[1]=A1[2] then s := "Lag     "; else s := "Non-Lag "; fi;
        if not IsConjugate(G, A1[1], A2[1]) then return Concatenation(s, "H'!=gH"); fi;
        g := RepresentativeAction(G, A2[1], A1[1]);
        NGH := Normalizer(G, A1[1]);
        N2 := A2[2]^g;
        if not IsConjugate(NGH, A1[2], N2) then
            return Concatenation(s, "N'!=gN, g in N_G(H)  (N, N' conjugate in G: ", String(IsConjugate(G, A1[2], A2[2])), ")");
        fi;
        g := g*RepresentativeAction(NGH, N2, A1[2]);
        gamma2 := function(a,b) return A2[3](a^(g^-1), b^(g^-1)); end;
        stab := Normalizer(NGH, A1[2]);
        if ForAny(stab, k -> IsTrivial2coc([Elements(A1[2]), function(a,b) return A1[3](a,b)/gamma2(a^k,b^k); end]) <> fail) then
            return Concatenation(s, "eps'!=g eps");
        fi;
        return Concatenation(s, "gamma'!=g gamma");
    end;;

    if not IsBound(fullSweep) then fullSweep := false; fi;
    if fullSweep then
        sweepIds := Concatenation(List([1..48], n -> List([1..NrSmallGroups(n)], i -> [n,i])));;
    else
        sweepIds := [ [32,43], [32,44], [48,29], [48,31], [48,32], [48,33], [48,49] ];;
    fi;

    SweepGroup := function(id)
        local K, MK, t;
        K := MakeGroup(id);
        if IsAbelian(K) then return; fi;
        MK := AlgebraClasses(TQDTheory(K));
        if MK.twins = [] then return; fi;
        Print("G_{", id[1], ",", id[2], "} = ", StructureDescription(K), ": ", Length(MK.twins), " twin pairs\n");
        for t in Collected(List(MK.twins, p -> TwinType(K, MK.classes[p[1]].algebras[1], MK.classes[p[2]].algebras[1]))) do
            Print("  ", t[2], " x ", t[1], "\n");
        od;
    end;;

    Section("Twin algebras in Z(Vec_G), the sweep of the table of twins of arXiv:2605.31602");
    for id in sweepIds do SweepGroup(id); od;
fi;
