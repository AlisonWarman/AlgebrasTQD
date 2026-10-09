#############################################################################
##
##  6_algebra_classes_and_inclusions.g          AlgebrasTQD examples
##
##  Algebra isomorphism classes, inclusions, directed edges and phase labels for D(S3). Generate a Hasse diagram and its linked algebra table using the same class selection and label prefix, as in Twin Algebras. Usage, from any directory: Read("path/to/AlgebrasTQD/examples/6_algebra_classes_and_inclusions.g"); TeX fragments are written to examples/tex/.
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

Section("Algebra Inclusions and directed edges in D(S3)");
G := MakeGroup("S3");;
th := TQDTheory(G);;
M := AlgebraClasses(th);;
Hs := Hasse(th,M);;
Print(Length(M.classes), " algebra classes, ", Length(M.twins), " twin pairs\n");
for i in [1..Length(M.classes)] do
    Print(i, ": dimension ", M.classes[i].dim, ", ", M.classes[i].name,
          " = ", M.classes[i].decomposition, "\n");
od;
Print("\nDirected edges (smaller algebra, larger algebra): ", Hs.edges, "\n");

# The symmetry boundary is L(G,G,gamma,eps). PhaseLabels returns one phase label per class, relative to this Lagrangian algebra.
sym := First([1..Length(M.classes)],i->M.classes[i].algebras[1][1]=G and
    M.classes[i].algebras[1][2]=G);;
Print("Phase labels relative to class ",sym,": ",PhaseLabels(th,sym,Hs),"\n");

Section("Linked TikZ diagram and algebra table");
tex := HasseTableTeX(th,Hs,rec(prefix:="s3alg",
    diagramFile:=Concatenation(texdir,"s3_hasse.tex"),
    tableFile:=Concatenation(texdir,"s3_algebras.tex")));;
Print("Wrote ",texdir,"s3_hasse.tex and ",texdir,"s3_algebras.tex\n");
Print("Node 1 is \\nameref{s3alg:1} and jumps to the matching \\xlabel in the table.\n");
