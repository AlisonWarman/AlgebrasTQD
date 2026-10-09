#############################################################################
##
##  9_quantum_computing_D4N.g               AlgebrasTQD examples
##
##  Quantum computing gates for D4, D8, and D16. Run from any directory with
##  Read("path/to/9_quantum_computing_D4N.g").
##
#############################################################################

Read(ReplacedString(INPUT_FILENAME(), "9_quantum_computing_D4N.g", "../AlgebrasTQD.g"));

# The three groups D_{4N} have N = 1, 2, 4, respectively.
# The surgery eigenphases give its logical gate in the computed basis.
# D4NPhaseGate gives the counterterm circuit and its SPT-stacking logical gate.
trivial := function(g) return 1; end;;

for N in [1,2,4] do
    Print("\n\nD",4*N," quantum computing gates\n\n");

    surgery := D4NSurgeryGate(N);;
    Print("Hybrid lattice surgery logical gate: diag",surgery.eigenphases,"\n\n");

    coc := D4NCocycle(N);;
    data := coc.data;;
    r := data.r;; s := data.s;;
    stacked := SPTStackingGate(rec(alpha:=coc.alpha,
        beta:=[trivial,trivial,coc.beta],
        K:=[Group(r*s),Group(s),Group(r)],g:=[r*s,s]));;
    phase := D4NPhaseGate(coc);;
    if stacked <> phase.U then
        ErrorNoReturn("The counterterm circuit must encode the SPT-stacking gate");
    fi;
    Print("SPT-stacking logical gate (constant depth): diag",DiagonalOfMat(stacked),"\n\n");
    Print("Boundary gate: diag",DiagonalOfMat(phase.Mbeta),"\n\n");
    Print("Clifford hierarchy level: ",phase.level,"\n");
od;
