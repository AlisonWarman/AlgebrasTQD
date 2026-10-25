## https://github.com/AlisonWarman/AlgebrasTQD
#############################################################################
##
##  1_Abelian.g                                      AlgebrasTQD examples
##
##  Anyons of the toric code, double semion, the type-II twisted double of
##  C2 x C2, and the untwisted double D(C4). Usage, from any directory:
##  Read("path/to/AlgebrasTQD/examples/1_Abelian.g"),
##
#############################################################################

Read(ReplacedString(INPUT_FILENAME(), "1_Abelian.g", "../AlgebrasTQD.g"));

#Section: prints a heading with a blank line below it
#in: title a string
#out: prints the heading
Section := function(title) Print("\n", title, "\n\n"); end;;

Section("Toric code D(C2)");
ShowAnyons(TQDTheory("C2"));

Section("Double semion");
ShowAnyons(TQDTheory("C2", [1]));

Section("Type-II twisted double of C2 x C2");
K := MakeGroup("C2 x C2");;
# omaut gives 4 twists up to automorphisms, trivial on 5, 3, 2, 1 subgroups:
# omega_II=(-1)^(x1*y2*y3) for g=a^x*b^y is the one trivial on 1, <a>, <b>
omII := First(omaut(K), om -> Length(GaugeableSubgroups(om)) = 3);;
ShowAnyons(TQDTheory(K, omII));

Section("Untwisted double D(C4)");
ShowAnyons(TQDTheory("C4"));
