#############################################################################
##
##  7_twin_algebras_G32.g                       AlgebrasTQD examples
##
##  All twin pairs of the untwisted double of G = SmallGroup(32,43), with their short algebra data and anyon decompositions. Reprint the H-type pair and its largest common proper subalgebra. Usage, from any directory: Read("path/to/AlgebrasTQD/examples/7_twin_algebras_G32.g").
##
#############################################################################

Read(ReplacedString(INPUT_FILENAME(), "7_twin_algebras_G32.g", "../AlgebrasTQD.g"));

#Section: prints a labelled section heading
#in: title a string
#out: prints the heading
Section := function(title) Print("\n", title, "\n\n"); end;;
Section("All twin pairs in D(SmallGroup(32,43))");
G := MakeGroup([32,43]);;
th := TQDTheory(G);;
M := AlgebraClasses(th);;
Hs := Hasse(th,M);;
Print(Length(M.classes)," algebra classes, ",Length(M.twins)," twin pairs\n");
for pair in M.twins do
    Print("\nTwin pair:\n");
    for i in pair do
        ShowAlgData(th, M.classes[i], rec(opP := "short"));;
    od;
od;

Section("The H-type Gassmann pair:");
# Both H are Klein four groups, F=1, and the algebra dimension is 8.
candidates := Filtered(M.twins,p->ForAll(p,i->
    Size(M.classes[i].algebras[1][1])=4 and IsTrivial(M.classes[i].algebras[1][2])));;
if Length(candidates)<>1 then ErrorNoReturn("Expected one H-type Klein-four twin pair"); fi;
twins := candidates[1];;
A1 := M.classes[twins[1]].algebras[1];;
A2 := M.classes[twins[2]].algebras[1];;
if M.classes[twins[1]].na<>M.classes[twins[2]].na or IsConjugate(G,A1[1],A2[1]) then
    ErrorNoReturn("The selected classes are not inequivalent Gassmann twins");
fi;
for i in twins do
    ShowAlgData(th, M.classes[i], rec(opP := "short"));;
od;

Section("Shared subalgebra of the H-type pair:");
lower := Filtered([1..Length(M.classes)],i->
    [i,twins[1]] in Hs.inclusions and [i,twins[2]] in Hs.inclusions);;
SortBy(lower,i->[-M.classes[i].dim,i]);;
common := lower[1];;
Print("Largest common proper subalgebra: ",M.classes[common].name,
      " (dimension ",M.classes[common].dim,")\n");
Print("Anyon decomposition: ",M.classes[common].decomposition,"\n");
