## https://github.com/AlisonWarman/AlgebrasTQD
#############################################################################
##
##  5_interface_map.g                                AlgebrasTQD examples
##
##  The anyons and algebras of the toric code and the double semion, the e-m duality of the toric code, and the canonical interface maps of D(A4). With the generators a = (1,2,3) and b = (1,2)(3,4) of examples/6_algebra_classes_and_inclusions.g, InterfaceMap prints the canonical map of anyons of every non-Lagrangian algebra class. Usage, from any directory: Read("path/to/AlgebrasTQD/examples/5_interface_map.g")
##
##  GAP does not fix the order of conjugacy classes, characters, anyons or subgroups, so the order of the printed algebras can differ between sessions
##
#############################################################################

# The loader sits one folder above this example file
Read(ReplacedString(INPUT_FILENAME(), "5_interface_map.g", "../AlgebrasTQD.g"));

#Section: prints a heading with a blank line below it
#in: title a string
#out: prints the heading
Section := function(title) Print("\n", title, "\n\n"); end;;

#----------------------------------------------------------------------------
# 1. The anyons and algebras of the toric code D(C2), and its e-m duality. Every algebra is the identity algebra or Lagrangian, so the interfaces are the gapped boundaries and the invertible ones, the identity and the e-m duality found by AutomorphismsAnyons and checked with AutomorphismsDG

Section("Anyons, algebras and e-m duality of the toric code D(C2)");
C2 := MakeGroup("C2");;
thC2 := TQDTheory(C2);;
ShowAnyons(thC2);
ShowAlgebrasWithAnyons(AlgebrasWithAnyons(thC2));
idC2 := [1..Length(thC2.aG)];;
autC2 := AutomorphismsAnyons(thC2);;
if Set(List(autC2, r -> r.perm)) <> Set(List(AutomorphismsDG(thC2), r -> r.perm)) then
    ErrorNoReturn("D(C2): AutomorphismsAnyons and AutomorphismsDG disagree");
fi;
em := First(autC2, r -> r.perm <> idC2);;
if em = fail then ErrorNoReturn("D(C2): the e-m duality was not found"); fi;
Print("\ne-m duality: ", List(Filtered(idC2, i -> em.perm[i] <> i),
      i -> [thC2.labels[i], thC2.labels[em.perm[i]]]), "\n");

#----------------------------------------------------------------------------
# 2. The anyons and algebras of the double semion theory: the identity algebra and one gapped boundary

Section("Anyons and algebras of the double semion theory");
thDS := TQDTheory(C2, [1]);;
ShowAnyons(thDS);
ShowAlgebrasWithAnyons(AlgebrasWithAnyons(thDS));

#----------------------------------------------------------------------------
# 3. The canonical interface map of every non-Lagrangian algebra class of D(A4), in the order of AlgebraClasses, as in the table examples/tex/A4_algebras.tex written by example 6. The identity algebra gives the identity map, and the seven others reduce to D(C2 x C2), D(C3) or D(C2). The Lagrangian algebras are the gapped boundaries, whose map sends the vacuum to the algebra

Section("Canonical interface maps for D(A4)");
G := AlternatingGroup(4);;
MakeGroupLabels([G, [(1,2,3), (1,2)(3,4)], ["a","b"]]);;
thA4 := TQDTheory(G);;
M := AlgebraClasses(thA4);;
if Length(M.classes) <> 15 then
    ErrorNoReturn("D(A4) has ", Length(M.classes), " algebra classes instead of 15");
fi;
for c in Filtered(M.classes, c -> c.dim < Size(G)) do
    InterfaceMap(thA4, c.algebras[1]);;
od;
