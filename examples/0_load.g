#############################################################################
##
##  0_load.g		AlgebrasTQD examples
##
##  Read the package and list the main user-level functions. 
##  Usage, from its directory:  Read("0_load.g");
##
#############################################################################

# The loader sits one folder above this example file.
Read(ReplacedString(INPUT_FILENAME(), "0_load.g", "../AlgebrasTQD.g"));

functions := [ "MakeGroup", "MakeGroupLabels", "RelabelGroup", "GroupElement",
               "GroupLabel", "ShowGroup", "TQDTheory", "Fusion", "ShowFusion", "ShowAnyons",
               "AlgebrasWithAnyons", "ShowAlgebrasWithAnyons", "AlgebraClasses",
               "Hasse", "PhaseLabels", "InterfaceMap", "RoughMergeSplitStep",
               "RoughMergeSplit", "SPTStackingGate" ];;

missing := Filtered(functions, f -> not IsBoundGlobal(f));;

if missing = [] then
    Print("AlgebrasTQD loaded. Main functions:\n");
    for f in functions do Print("  ", f, "\n"); od;
else
    Print("AlgebrasTQD: these functions are missing: ", missing, "\n");
fi;
