## https://github.com/AlisonWarman/AlgebrasTQD
#############################################################################
##
##  4_algebras.g                                     AlgebrasTQD examples
##
##  Condensable algebras A(H,N,gamma,eps) of the toric code, double semion, the type-II twisted double of C2 x C2, D(S3), the type-III twisted double of Z2^3 in the R, G, B labels, and D(D8) through its equivalence with the latter. Show their anyon content, algebra filters, selected algebras in detail, and LaTeX output. Usage, from any directory: Read("path/to/AlgebrasTQD/examples/4_algebras.g")
##
##  GAP does not fix the order of conjugacy classes, characters, anyons or subgroups, so algebras are found here by their properties, not by position
##
#############################################################################

# The loader sits one folder above this example file
Read(ReplacedString(INPUT_FILENAME(), "4_algebras.g", "../AlgebrasTQD.g"));

#Section: prints a heading with a blank line below it
#in: title a string
#out: prints the heading
Section := function(title) Print("\n", title, "\n\n"); end;;

#----------------------------------------------------------------------------
# 1. The algebras of D(Z2), the toric code

Section("The algebras of D(Z2) (toric code)");
C2 := MakeGroup("C2");;
thC2 := TQDTheory(C2);;
LC2 := AlgebrasWithAnyons(thC2);;
ShowAlgebrasWithAnyons(LC2);

#----------------------------------------------------------------------------
# 2. The nontrivial 3-cocycle of Z2 gives the double semion theory

Section("The algebras of the double semion theory");
thDS := TQDTheory(C2, [1]);;
LDS := AlgebrasWithAnyons(thDS);;
ShowAlgebrasWithAnyons(LDS);

#----------------------------------------------------------------------------
# 3. The type-II twisted Z2 x Z2 (see examples/1_Abelian.g) has fewer algebras because omega restricted to <ab> is not trivial. One reduced theory is itself twisted, Z(Vec_C2^alpha)

Section("The algebras of the type-II twisted Z2 x Z2");
K := MakeGroup("C2 x C2");;
a := GroupElement(K, "a");; b := GroupElement(K, "b");;
# omaut gives 4 twists up to automorphisms, trivial on 5, 3, 2, 1 subgroups:
# omega_II=(-1)^(x1*y2*y3) for g=a^x*b^y is the one trivial on 1, <a>, <b>
omII := First(omaut(K), om -> Length(GaugeableSubgroups(om)) = 3);;
thK := TQDTheory(K, omII);;
LK := AlgebrasWithAnyons(thK);;
for r in LK do
    ShowAlgData(thK, r.A);;
od;
# The long form also prints the nontrivial values of gamma, eps and of the 3-cocycle alpha of the reduced theory: here for H = <ab>, N = 1
Print("\nA(<ab>, 1, 1, 1) in the long form:\n");
r := First(LK, r -> r.H = Group(a*b) and IsTrivial(r.F));;
ShowAlgData(thK, r.A, rec(opP := "long"));;
Print("untwisted D(C2 x C2) has ", Length(TQDAlgebras(TQDTheory(K))), " algebras, ",
      "the type-II twist ", Length(TQDAlgebras(thK)), "\n");

#----------------------------------------------------------------------------
# 4. The algebras of D(S3): one line per algebra with its dimension, its name A(H, N, gamma, eps), the group K = H/N, and its anyons

Section("The algebras of D(S3)");
S3 := MakeGroup("S3");;
th := TQDTheory(S3);;
L := AlgebrasWithAnyons(th);;
ShowAlgebrasWithAnyons(L);

#----------------------------------------------------------------------------
# 5. Filters: the algebras of a given dimension, the Lagrangian ones (dimension |G|, the gapped boundaries), or those on given subgroups

Section("Filters for D(S3)");
Print("Lagrangian algebras of D(S3):\n");
for A in TQDAlgebras(th, rec(Lag := true)) do Print("  ", AlgebraName(A, th.glG), "\n"); od;
Print("algebras of dimension 3:\n");
for A in TQDAlgebras(th, rec(dim := 3)) do Print("  ", AlgebraName(A, th.glG), "\n"); od;
# The sign charge: trivial flux, dimension 1, a character that is not 1
sgn := th.labels[First([1..Length(th.aG)], i -> IsOne(th.aG[i][1]) and dima(th.aG[i], One(S3)) = 1 and
    ForAny(S3, g -> not LookupDictionary(th.aG[i][2], g) in [ 1, fail ]))];;
Print("algebras containing the anyon ", sgn, ":\n");
for r in FindAlgebras(L, rec(contains := sgn)) do Print("  ", r.name, "\n"); od;

#----------------------------------------------------------------------------
# 6. One algebra in detail: H = S3, N = C3. ShowAlgData prints the name, dimension, H/N, the reduced topological order and the anyons

Section("A(S3, C3, 1, 1) in detail");
r := First(L, r -> Size(r.H) = 6 and Size(r.F) = 3);;
ShowAlgData(th, r.A);;

#----------------------------------------------------------------------------
# 7. AlgebraDisplayData returns the strings of ShowAlgData, also in TeX

Section("LaTeX strings of A(S3, C3, 1, 1)");
r := AlgebraDisplayData(th, First(L, r -> Size(r.H) = 6 and Size(r.F) = 3).A);;
Print(r.nameTeX, "\n", r.decompositionTeX, "\n", r.reducedTOTeX, "\n");

#----------------------------------------------------------------------------
# 8. Z2^3 with the type-III 3-cocycle omega(g1,g2,g3) = (-1)^(r1 g2 b3), for g = R^r G^g B^b. Its anyons are labelled as in arXiv:2403.00905 and arXiv:2512.13777: 1 and the charges e_C, the fluxes m_C (bosons) and f_C (fermions), and the semions s_RGB, sbar_RGB, with C a set of colours R, G, B

Section("Z2^3 with the type-III 3-cocycle: anyons in the R, G, B labels");
Z2c := MakeGroup("C2 x C2 x C2");;
RelabelGroup(Z2c, ["R","G","B"], ["a","b","c"]);;
R := GroupElement(Z2c, "R");; G := GroupElement(Z2c, "G");; B := GroupElement(Z2c, "B");;
#rgb: the exponents [r,g,b] of an element R^r G^g B^b of Z2^3
rgb := x -> First(Cartesian([0,1],[0,1],[0,1]), e -> R^e[1]*G^e[2]*B^e[3] = x);;
omIII := rec(a := function(g1,g2,g3) return rgb(g1)[1]*rgb(g2)[2]*rgb(g3)[3] mod 2; end, N := 2);;
if 3coctest([Elements(Z2c), omIII]) <> true then
    ErrorNoReturn("omega_III is not a normalized 3-cocycle");
fi;
thIII := TQDTheory(Z2c, omIII, rec(ST := true));;
#RGBLabel: the label of an anyon of Z(Vec_{Z2^3}^omega_III): a charge by the colours on which its character is -1, a flux by its colours and its spin
#in: an anyon [g,character,class,label] of thIII.aG
#out: a string such as "e_RG", "m_B", "f_GB" or "s_RGB"
RGBLabel := function(an)
    local colours, spin;
    colours := v -> Concatenation(List(Filtered([1..3], i -> v[i] = 1), i -> ["R","G","B"][i]));
    if IsOne(an[1]) then
        if ForAll([R,G,B], g -> LookupDictionary(an[2], g) = 1) then return "1"; fi;
        return Concatenation("e_", colours(List([R,G,B], g -> (1 - LookupDictionary(an[2], g))/2)));
    fi;
    spin := LookupDictionary(an[2], an[1])/LookupDictionary(an[2], One(Z2c));
    if an[1] = R*G*B then
        if spin = E(4) then return "s_RGB"; fi;
        return "sbar_RGB";
    fi;
    if spin = 1 then return Concatenation("m_", colours(rgb(an[1]))); fi;
    return Concatenation("f_", colours(rgb(an[1])));
end;;
thIII.labels := List(thIII.aG, RGBLabel);;
if Length(Set(thIII.labels)) <> Length(thIII.labels) then
    ErrorNoReturn("the R, G, B labels are not distinct");
fi;
ShowAnyons(thIII);

#----------------------------------------------------------------------------
# 9. The algebras of Z(Vec_{Z2^3}^omega_III). AlgebraData gives several data for one algebra, related by the conjugation phases Omega_g of the twist, and AlgebraClasses sorts them into the 38 classes, 11 of them Lagrangian, of arXiv:2403.00905

Section("The algebras of Z(Vec_{Z2^3}^omega_III)");
MIII := AlgebraClasses(thIII);;
Print(Length(TQDAlgebras(thIII)), " algebra data, ", Length(MIII.classes), " classes, ",
      Number(MIII.classes, c -> c.dim = 8), " Lagrangian\n");
for c in MIII.classes do
    Print("dim=", c.dim, "  ", c.name, "  ", ShowAlg(c.na, thIII.labels), "\n");
od;

#----------------------------------------------------------------------------
# 10. The braided equivalence Z(Vec_{Z2^3}^omega_III) = D(D8): the Lagrangian algebra A(K,K,gamma,eps) of Z(Vec_{Z2^3}^omega_III) x bar D(D8), K = <G, RB r, R s, B rs>, decomposes as sum_a a x bar phi(a) with phi a permutation of the anyons, the dictionary of arXiv:2512.13777. D8 has the generators r of order 4 and s of order 2 of MakeGroup("D8"), as in that paper

Section("The equivalence Z(Vec_{Z2^3}^omega_III) = D(D8) and the anyons of D(D8) in R, G, B labels");
D8 := MakeGroup("D8");;
r := GroupElement(D8, "r");; s := GroupElement(D8, "s");;
if Order(r) <> 4 or Order(s) <> 2 or s*r*s <> r^-1 then
    ErrorNoReturn("r and s do not present D8 as expected");
fi;
thD8 := TQDTheory(D8, 0, rec(ST := true));;
ZD := DirectProduct(Z2c, D8);;
eZ := Embedding(ZD, 1);; eD := Embedding(ZD, 2);; pZ := Projection(ZD, 1);; pD := Projection(ZD, 2);;
K := Group(eZ(G), eZ(R*B)*eD(r), eZ(R)*eD(s), eZ(B)*eD(r*s));;
omZD := rec(a := function(g1,g2,g3) return omIII.a(pZ(g1),pZ(g2),pZ(g3)); end, N := 2);;
gammaK := gammaf([K, omZD])[1];;
epsK := epsf([K, K, gammaK, omZD])[1];;
res := AlgAnyonsProducts(rec(A := [K,K,gammaK,epsK,ZD], ps := [pZ,pD], es := [eZ,eD],
    aGs := [thIII.aG, thD8.aG], stars := ["","*"], om := omZD));;
#phi: one row per anyon of D(D8), with a 1 at its image in Z(Vec_{Z2^3}^omega_III)
phi := TransposedMat(Reshape(res[2], Length(thD8.aG)));;
if res[1] <> Size(Z2c)*Size(D8) or not ForAll(phi, row -> Sum(row) = 1) or not ForAll(TransposedMat(phi), col -> Sum(col) = 1) then
    ErrorNoReturn("A(K,K,gamma,eps) is not the Lagrangian algebra of an equivalence");
fi;
if phi*thIII.S <> thD8.S*phi or phi*thIII.T <> thD8.T*phi then
    ErrorNoReturn("the equivalence does not preserve S and T");
fi;
for i in [1..Length(phi)] do Print(thD8.labels[i], "  <->  ", ShowAlg(phi[i], thIII.labels), "\n"); od;
labD8 := List(phi, row -> thIII.labels[Position(row, 1)]);;

Section("The algebras of D(D8) in R, G, B labels");
LD8 := AlgebrasWithAnyons(thD8);;
for rr in LD8 do
    Print("dim=", rr.dim, "  ", rr.name, "  ", ShowAlg(rr.na, labD8), "\n");
od;
# the equivalence maps the algebras of D(D8) onto those of Z(Vec_{Z2^3}^omega_III)
if Set(List(LD8, rr -> rr.na*phi)) <> Set(List(MIII.classes, cl -> cl.na)) then
    ErrorNoReturn("the algebras of D(D8) and Z(Vec_{Z2^3}^omega_III) do not correspond");
fi;
Print("The ", Length(LD8), " algebras of D(D8) match the ", Length(MIII.classes), " classes of the type-III double\n");

Section("A D8 algebra with its central subgroup in detail");
rD8 := First(LD8, rr -> rr.H = D8 and rr.F = Center(D8));;
ShowAlgData(thD8, rD8.A);;
Print("in R, G, B labels: ", ShowAlg(rD8.na, labD8), "\n");

#----------------------------------------------------------------------------
# 11. The number of algebras for every twist of D8, one per orbit of H^3(D8,U(1)) under the automorphisms of D8 (sorted, since the orbits come in no fixed order)

Section("The number of algebras of every twisted double of D8");
Print(SortedList(List(omaut(D8), om -> Length(TQDAlgebras(TQDTheory(D8, om))))), "\n");
