#############################################################################
##
##  2_non-Abelian.g		AlgebrasTQD examples
##
##  Build S3 and D8 with labelled generators, then print the anyons and fusion rules of their quantum doubles. Relabel the generators of D8 before constructing its double.
##
##  Note: GAP does not fix the order of conjugacy classes, characters or anyons, so the order of the printed lines can change from one session to another.
##
##  Usage, from any directory: Read("path/to/AlgebrasTQD/examples/2_non-Abelian.g");
## 
#############################################################################

# The loader sits one folder above this example file.
Read(ReplacedString(INPUT_FILENAME(), "2_non-Abelian.g", "../AlgebrasTQD.g"));

# Section: prints a heading with a blank line below it
Section := function(title) Print("\n", title, "\n\n"); end;;

#----------------------------------------------------------------------------
# 1. A group with labelled generators. MakeGroup("S3") labels the rotation r (order 3) and the reflection s (order 2). ShowGroup prints the relations and the label of every element.

Section("The group S3");
G := MakeGroup("S3");;
ShowGroup(G);

#----------------------------------------------------------------------------
# 2. The Drinfeld double D(S3) = Z(Vec_S3). ShowTQDTheory computes the anyons and modular data once, then prints the anyons and all fusion rules.

Section("The anyons and fusion rules of D(S3)");
# One line per anyon: index, label ([flux class], irrep of the centralizer), dimension d, spin theta.
th := ShowTQDTheory("S3");;
# GAP prints H^3 as the orders of its cyclic Abelian group factors, so [6] means Z6.
Print("\nH^3(S3,U(1)) = ", th.H3, " (Abelian group factors)\n");
Print("number of anyons: ", Length(th.aG), "\n");

Section("The S and T matrices of D(S3)");
Display(th.S);
Display(th.T);

Section("A fusion rule of D(S3) by index");
# Fusion takes two anyons by label or by index. Here, the anyon of dimension 3 of spin 1:
n := Length(th.aG);;
d := List(th.aG, a -> dima(a, One(G)));;
k := First([1..n], i -> d[i] = 3 and th.T[i][i] = 1);;
Print(th.labels[k], " x ", th.labels[k], " = ", Fusion(th, k, k), "\n\n");

#----------------------------------------------------------------------------
# 3. D8 relabelled as in arXiv:2412.15024: D8 = (Z2^a x Z2^b) : Z2^c = {1,a,b,ab,c,ca,cb,cab}, cac = b, cbc = a. From MakeGroup's r, s: c = s, a = sr, b = sr^3 = cac (c first, so it is written on the left).

Section("D8 with the generators c, a, b");
D8 := MakeGroup("D8", ["c","a","b"], ["s","sr","sr^3"]);;
ShowGroup(D8);
# The elements can be typed in the new labels:
c := GroupElement(D8, "c");; a := GroupElement(D8, "a");; b := GroupElement(D8, "b");;
Print("cac = ", GroupLabel(D8, c*a*c), ",  cbc = ", GroupLabel(D8, c*b*c), "\n");

Section("The anyons and fusion rules of D(D8)");
thD8 := ShowTQDTheory(D8);;
