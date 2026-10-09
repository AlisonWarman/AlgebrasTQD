#############################################################################
##
##  AlgebrasTQD.g		AlgebrasTQD
##
##  Global package source loader.
##  Usage, from its directory:  Read("AlgebrasTQD.g");
##
#############################################################################

# Check that the required GAP packages are available before reading the source files.
for pkg in [ "HAP", "CTblLib", "IO" ] do
    if LoadPackage(pkg) = fail then
        ErrorNoReturn("AlgebrasTQD requires the GAP package ", pkg);
    fi;
od;

# Declare cross-file names so GAP can read the seven numbered files without forward-
# reference warnings. The function definitions remain in their subject files.
DeclareGlobalName("RelabelGroup");
DeclareGlobalName("AlgAnyonsV");
DeclareGlobalName("AlgAnyonsG1G2V");
DeclareGlobalName("alphaf");
DeclareGlobalName("AlgebraClassesG");
DeclareGlobalName("IsSubalgebra");
DeclareGlobalName("AlgebraData");
DeclareGlobalName("AnyonLabelStrings");
DeclareGlobalName("IsNormalizedCocycle");
DeclareGlobalName("HasseEntryTeX");

# The folder of this loader, e.g. "../" when read as Read("../AlgebrasTQD.g").
AlgebrasTQDRoot := ReplacedString(INPUT_FILENAME(), "AlgebrasTQD.g", "");

# File 0 is the preliminary Gruen-Morrison code, kept intact.
for file in [ "0_Modular_Data_Mignard-Schauenburg-Gruen-Morrison.g",
              "1_preliminaries.g",
              "2_anyons.g",
              "3_cocycles.g",
              "4_algebra_data.g",
              "5_interface_map.g",
              "6_algebra_classes_and_inclusions.g",
              "7_quantum_information.g" ] do
    Read(Concatenation(AlgebrasTQDRoot, "source/", file));
od;
