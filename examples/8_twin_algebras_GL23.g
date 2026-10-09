#############################################################################
##
##  8_twin_algebras_GL23.g                      AlgebrasTQD examples
##
##  Twin Lagrangian Algebras of D(GL(2,3)) on the two non-conjugate S3 subgroups, their shared non-Lagrangian subalgebra and the phase labels. Usage, from any directory: Read("path/to/AlgebrasTQD/examples/8_twin_algebras_GL23.g").
##
#############################################################################

Read(ReplacedString(INPUT_FILENAME(), "8_twin_algebras_GL23.g", "../AlgebrasTQD.g"));

#Section: prints a labelled section heading
#in: title a string
#out: prints the heading
Section := function(title) Print("\n", title, "\n\n"); end;;
Section("Twin Lagrangian Algebras in D(GL(2,3))");
G := MakeGroup([48,29]);;
th := TQDTheory(G);;
M := AlgebraClasses(th);;
Hs := Hasse(th,M);;
# The paper's two twin Lagrangian algebras have H=F of order 6 and dimension |G|.
candidates := Filtered(M.twins,p->ForAll(p,i->
    M.classes[i].dim=Size(G) and
    Size(M.classes[i].algebras[1][1])=6 and
    M.classes[i].algebras[1][1]=M.classes[i].algebras[1][2]));;
if Length(candidates)<>1 then ErrorNoReturn("Expected one S3 Lagrangian twin pair"); fi;
twins := candidates[1];;
A1 := M.classes[twins[1]].algebras[1];;
A2 := M.classes[twins[2]].algebras[1];;
if M.classes[twins[1]].na<>M.classes[twins[2]].na or IsConjugate(G,A1[1],A2[1]) then
    ErrorNoReturn("The selected classes are not inequivalent Gassmann twins");
fi;
Print(Length(M.classes)," algebra classes, ",Length(M.twins)," twin pairs\n");
Print("\nTwin Lagrangian Algebras:\n");
for i in twins do Print(M.classes[i].name," = ",M.classes[i].decomposition,"\n"); od;
Print("\nTheir H subgroups are not conjugate, so the algebras as inqeuivalent, but their anyon decompositions are the same.\n");

Section("Shared interface and phase labels");
lower := Filtered([1..Length(M.classes)],i->
    [i,twins[1]] in Hs.inclusions and [i,twins[2]] in Hs.inclusions);;
SortBy(lower,i->[-M.classes[i].dim,i]);;
common := lower[1];;
Print("Largest common proper subalgebra: ",M.classes[common].name,
      " (dimension ",M.classes[common].dim,")\n");
Print("Its reduced theory: ",AlgebraDisplayData(th,M.classes[common]).reducedTOTeX,"\n");
sym := First([1..Length(M.classes)],i->M.classes[i].algebras[1][1]=G and
    M.classes[i].algebras[1][2]=G);;
phases := PhaseLabels(th,sym,Hs);;
Print("\nRelative to the symmetry boundary, the twins have phase labels ",
      List(twins,i->phases[i])," and their common subalgebra has ",phases[common],".\n");
