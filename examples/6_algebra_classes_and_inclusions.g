## https://github.com/AlisonWarman/AlgebrasTQD
#############################################################################
##
##  6_algebra_classes_and_inclusions.g          AlgebrasTQD examples
##
##  Algebra isomorphism classes, inclusions, directed edges, Hasse diagrams and phase labels for the double of A4 and its twisted doubles Z(Vec_A4^omega_2) and Z(Vec_A4^omega_3), where omega_2 and omega_3 are 3-cocycles of order two and three, with the generators a = (1,2,3) and b = (1,2)(3,4) of the Hasse-diagram papers. For each theory a linked Hasse diagram and algebra table are written to examples/tex/, in the layout of Twin Algebras. Usage, from any directory: Read("path/to/AlgebrasTQD/examples/6_algebra_classes_and_inclusions.g")
##
#############################################################################

Read(ReplacedString(INPUT_FILENAME(), "6_algebra_classes_and_inclusions.g", "../AlgebrasTQD.g"));

#Section: prints a labelled section heading
#in: title a string
#out: prints the heading
Section := function(title) Print("\n", title, "\n\n"); end;;
texdir := ReplacedString(INPUT_FILENAME(), "6_algebra_classes_and_inclusions.g", "tex/");;
if not IsDirectoryPath(texdir) and CreateDir(texdir) = fail then
    ErrorNoReturn("Cannot create TeX output directory ", texdir);
fi;

#----------------------------------------------------------------------------
# 1. The group A4 with the generators a = (1,2,3) and b = (1,2)(3,4). MakeGroup labels a = (1,2,3) and b = (2,3,4), whose product ba is (1,2)(3,4)

Section("The group A4 = <a,b> with a = (1,2,3) and b = (1,2)(3,4)");
G := MakeGroup("A4");;
RelabelGroup(G, ["a","b"], ["a","ba"]);;
ShowGroup(G);
a := GroupElement(G, "a");; b := GroupElement(G, "b");;
F := Group(b, a*b*a^2);;    # the Klein four-group, normal in A4
if Order(a) <> 3 or Order(b) <> 2 or Size(F) <> 4 or not IsNormal(G, F) then
    ErrorNoReturn("The generators a, b do not present A4 as expected");
fi;

#----------------------------------------------------------------------------
# 2. The twists, named by the order of their class in H^3(A4,U(1)) = Z6. omega_2 is the class of order two, and omega_3 is the class of order three obtained by pulling back the 3-cocycle alpha(m^l,m^j,m^k) = exp(2 pi i l (j+k-<j+k>_3)/9) of the quotient Z3 = A4/F = <m> (Coste, Gannon, Ruelle), with m the image of a

Section("The 3-cocycles omega_2 and omega_3 of A4");
n := H3Invariants(G)[1];;
Print("H^3(A4,U(1)) = Z", n, "\n");
om2 := H3Cocycle(G, [ First([1..n-1], v -> n/Gcd(v, n) = 2) ]);;
p := NaturalHomomorphismByNormalSubgroup(G, F);;
m := Image(p, a);;
gn := g -> First([0..2], k -> Image(p, g) = m^k);;
om3 := rec(a := function(g1, g2, g3)
    return (gn(g1)*(gn(g2) + gn(g3) - ((gn(g2) + gn(g3)) mod 3))) mod 9;
end, N := 9);;
if 3coctest([Elements(G), om3]) <> true then
    ErrorNoReturn("omega_3 is not a normalized 3-cocycle");
fi;
Print("omega_2 has values in the ", om2.N, "th roots of unity, omega_3 is a normalized 3-cocycle with values in the 9th roots of unity\n");

#----------------------------------------------------------------------------
# 3. For each theory: the anyons, the algebra classes, the directed edges of the Hasse diagram, the phases of the A4 symmetry (relative to the Dirichlet boundary L(1,1) = A(1,1,1,1)), and the linked TikZ diagram and algebra table

#ShowTheory: anyons, algebra classes, Hasse diagram and phases of one theory, and its TeX fragments
#in: label a string (the prefix of the TeX labels and file names), name a string for the heading, v the cocycle as accepted by TQDTheory
#out: the record of Hasse, after printing the results and writing texdir/label_hasse.tex and texdir/label_algebras.tex
ShowTheory := function(label, name, v)
    local th, M, Hs, i, sym;
    Section(Concatenation("Anyons, algebra classes, Hasse diagram and phases of ", name));
    th := TQDTheory(G, v, rec(ST := true));
    ShowAnyons(th);
    M := AlgebraClasses(th);
    Hs := Hasse(th, M);
    Print("\n", Length(M.classes), " algebra classes, ", Length(M.twins), " twin pairs\n");
    for i in [1..Length(M.classes)] do
        Print(i, ": dimension ", M.classes[i].dim, ", ", M.classes[i].name, " = ", M.classes[i].decomposition, "\n");
    od;
    Print("\nDirected edges (smaller algebra, larger algebra): ", Hs.edges, "\n");
    # The Dirichlet boundary L(1,1) realizes the A4 symmetry, with its anomaly omega
    sym := First([1..Length(M.classes)], i -> IsTrivial(M.classes[i].algebras[1][1]));
    Print("Phase labels for the A4 symmetry, relative to class ", sym, " = L(1,1): ", PhaseLabels(th, sym, Hs), "\n");
    HasseTableTeX(th, Hs, rec(prefix := label,
        diagramFile := Concatenation(texdir, label, "_hasse.tex"),
        tableFile := Concatenation(texdir, label, "_algebras.tex")));
    Print("Wrote ", texdir, label, "_hasse.tex and ", texdir, label, "_algebras.tex\n");
    return Hs;
end;;

ShowTheory("A4", "D(A4)", 0);;
ShowTheory("A4om2", "Z(Vec_A4^omega_2)", om2);;
ShowTheory("A4om3", "Z(Vec_A4^omega_3)", om3);;
