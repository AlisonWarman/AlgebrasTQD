## Functions in this file (each with the first sentence of the comment above it):
## - Posinlist(list, el): returns Position in list (i.e. first occurrence or fail)
## - ComplementIntMatWithTransforms(matBasis, matSub)
## - UniversalCoefficientsTheorem(K, n)
## - GroupCohomologyFunctor(K1, K2, phi, n)
## - AutomorphismOrbits(G, R, K, UCT)
## - ThreeCocyclesUpToAutomorphism(G): This takes a group G and returns a list of three-cocycle representatives of the set of orbits of H^3(G) under Aut(G).
## - TwoCocycleOnCentralizer(omega, g): This takes a three-cocycle and a group element and returns a two-cocycle on the centralizer of g.
## - ListGenToElement(word, G, gens): This takes a list of positive and negative integers corresponding to generators and their inverses, a group and a list of generators for that group and returns the element formed by multiplying the generators in the order referenced in the list.
## - GroupExtension(Cg, exponent, beta): This takes a group (Cg), a cyclic group (A) and a 2-cocycle beta : Cg x Cg -> A.
## - GroupExtensionOfCentralizer(G, g, omega, val, exponent): This takes a group G, an element g in G, a cyclic group (A) and a 3-cocycle omega : G x G x G -> A.
## - ProjectiveCharacters(CgExtGens, CgExtPc, iso): This takes a central extension of a group (CgExt) and computes the irreducible representations which correspond to irreducible projective representations of the initial group with 2-cocycle it was extended by.
## - GenerateSimpleObjects(Gin, omega, val, exponent): We want to do something more clever in the case that G is cyclic as in this case all irreps are one dimensional and we can easily compute them without passing to the (much) more complicated group extension.
## - CoefficientSSum(exponent, val, beta, a, b, h, l, xh, yl): This gives the coefficients for the sum over the characters.
## - sVal(G, exponent, val, beta, gData, hData): This computes a single cell of the S matrix corresponding to two pairs of a conjugacy class of G with an identified element and a projective representation of the centralizer of that element.
## - GenerateModularData(G, omega, val, exponent, simples): This produces the modular data of Vec^{omega} G from the simple objects.
## - ComputeModularData(G, omega, val, exponent): This produces the modular data of Vec^{omega} G.
## - VerlindeFormula(sMatrix, a, b, c): Implementing the Verlinde formula.
## - ValidModularData(data): This checks if a given pair (sMatrix, tMatrix) could possibly be the modular data for something.
## - SaveModularDataParallel(n, m, N, j, detailed): One of the two main functions to be used to compute and store modular data.
## - SaveAllDataForGivenOrder(n): Save modular data for a given group order
## - ComputeDataForever(): Compute a lot of modular data
## - ComputeDataForeverParallel(start, finish, N, i, detailed): This function allows for data to be computed in a parallel manner with each thread computing a different group.
## - ComputeNonAbelianDataForeverParallel(start, finish, N, i, detailed)
## - LoadModularData(n, m, i): Load some modular data.
## - LoadTMatrix(n, m, i): If we only want to use the T matrix, it is much quicker to load it by itself and not with the S matrix.
## - TestData(i, j): Run a simple sanity test on the modular data.
## - SaveModularDataTimed(n, m, maxtime, currenttime, lasttime)
## - ComputeDataFor48HoursParallel(m, N, i)
## - ComputeALittleData(l, m, n): Compute modular data for the n'th cocycle orbit of the m'th group of order l.
## - FindRanksOfCenter(order): The following collects some data on the ranks of the centers
## - BasicEquivalentModularDataTests(data1, data2): The following runs a couple of basic tests to see if the two sets of modular data could be equivalent.
## - OrbitsOfTMatrix(order): Find the equivalence classes of the T matrices.
## - ComputeTOrbitsBetween(lower, upper): The minimal value of lower is 2.
##

LoadPackage("hap");
LoadPackage("IO");

#returns Position in list (i.e. first occurrence or fail)
Posinlist:=function(list,el)
	local k;
	for k in [1..Length(list)] do
		if el in list[k] then
			return k;
		fi;
	od;
	return fail;
end;

# The first four functions were written by Mignard and Schauenburg:
# https://arxiv.org/abs/1708.06538
# The rest by Gruen and Morrison:
# http://arxiv.org/abs/1808.05060

##########################################################################
ComplementIntMatWithTransforms := function(matBasis, matSub)
    local data, newSub, newBas, mods, fulltrans, subtrans, i;

    data := ComplementIntMat(matBasis, matSub);
    newSub := data.sub;
    newBas := [];
    mods := data.moduli;
    
    fulltrans := [];
    subtrans := [];

    for i in [1..Size(mods)] do
        Add(newBas, newSub[i]/mods[i]);
        Add(fulltrans, SolutionMat(matBasis, newBas[i]));
        Add(subtrans, SolutionMat(matSub, newSub[i]));
    od;

    for i in data.complement do
        Add(fulltrans, SolutionMat(matBasis, i));
    od;

    return rec( fulltrans   := fulltrans,
                subtrans    := subtrans,
                moduli      := mods);
end;

UniversalCoefficientsTheorem := function(K,n)
    local   ZZ,             # a basis for Z_n(K)
            B,              # a basis for B_n(K)
            r,              # the ABT for Z_n(K) and B_n(K)
            C,              # the matrix C
            D,              # the list of the invariant factors
            m,              # the exponent of the H_n(K)
            homlist,        # a "basis" for Hom(H_n(K) ,Z/mZ)
            r2, R1, C1,     # the different variables implicated in the ABT for K_n and Z_n(K)
            I,              # the matrix I
            cocyclelist,    # a "basis" for H^n(K,C^*)
            hom, i;    

    ZZ := NullspaceIntMat(TransposedMat(BoundaryMatrix(K,n)));

    if not Size (ZZ)>0 then
        return rec( complex      := K,
                    cyclebasis   := ZZ,
                    cycletrans   := [],
                    hombasis     := [],
                    cocyclebasis := [],
                    torsion      := [1],
                    exponent     := 1,
                    lift         := []);
    fi;

    B       := BaseIntMat(TransposedMat(BoundaryMatrix(K,n+1)));
    r       := ComplementIntMatWithTransforms(ZZ,B);
    C       := r!.fulltrans;
    D       := r!.moduli;
    m       := D[Size(D)];
    homlist := [];

    for i in [1..Size(D)] do
        if D[i] = 1 then
            continue;
        fi;
        hom     := ListWithIdenticalEntries(Size(ZZ),0);
        hom[i]  := m/D[i];
        Add(homlist, hom);
    od;

    homlist:= List(homlist, x -> ((C^(-1))*x) mod m);

#;  r2 := ComplementIntMatWithTransforms(IdentityMat(K!.dimension(3)), ZZ);
    r2 := ComplementIntMatWithTransforms(IdentityMat(K!.dimension(n)), ZZ);
    C1 := r2!.subtrans;
    R1 := r2!.fulltrans;

    I := Concatenation(IdentityMat(Size(ZZ)), NullMat(K!.dimension(n) - Size(ZZ), Size (ZZ)));

    cocyclelist := List(homlist, x -> (R1^(-1)*(I*(C1*x))) mod m);

    return( rec(    complex      := K,
                    cyclebasis   := ZZ,
                    cycletrans   := C,
                    hombasis     := homlist,
                    cocyclebasis := cocyclelist,
                    torsion      := Filtered (D,x->not x=1),
                    exponent     := m,
                    lift := R1^(-1)*I*C1));
end;

GroupCohomologyFunctor := function(K1,K2, phi ,n)
    local   UCT1,       # UCT for K1
            m1,         # the exponent of H_n(K1)
            Z1,         # the adapted basis of Z_n(K1)
            UCT2,       # UCT for K2
            m2,         # the exponent of H_n(K2)
            Z2,         # the adapted basis of Z_n(K2)
            p,          # p=lcm(m1,m2)
            F,          # the matrix F
            hphi,       # the morphism H_n( phi )
            s;

    UCT1    := UniversalCoefficientsTheorem(K1, n);
    m1      := UCT1!.exponent;
    Z1      := UCT1!.cyclebasis;
    s       := NormalFormIntMat(Z1, 13);
    UCT2    := UniversalCoefficientsTheorem(K2, n);
    m2      := UCT2!.exponent;
    Z2      := UCT2!.cyclebasis;
    F       := List(Z1, x -> SolutionIntMat(Z2 , phi!.mapping(x, n))); 
    p       :=Lcm(m1,m2);

    hphi    := function(f)
        return ((F*(m1*f ))/m2) mod m1;
    end;

    return rec( matrix:=F,
                mapping:=hphi,
                p:=p,
                m1:=m1,
                m2:=m2);
end;


AutomorphismOrbits := function(G, R, K, UCT)
    local rcv, coho, aut, gens, autmat, orbits;
    rcv := function (x ,n)
        return List (x ,y->ZmodnZObj(y ,n ));
    end;

    coho    := NearAdditiveGroup(List(UCT!.hombasis, x->rcv(x,UCT!.exponent)));
    aut     := AutomorphismGroup(G);
    gens    := GeneratorsOfGroup(aut);
    autmat  := List(gens, phi -> TransposedMat(GroupCohomologyFunctor(K, K, TensorWithIntegers( EquivariantChainMap(R, R, phi)), 3)!.matrix));

    autmat  := List(autmat , x->List ( x , y->rcv (y, UCT!.exponent)));
    orbits  := OrbitsDomain(aut , coho , gens , autmat);

    return List(orbits, x -> List(x, y -> List(y, z -> Int(z))));
end;
##########################################################################

# This takes a group G and returns a list of three-cocycle representatives 
# of the set of orbits of H^3(G) under Aut(G).

ThreeCocyclesUpToAutomorphism := function(G)
    local R, K, UCT, orbits, cocycles;

    R           := ResolutionFiniteGroup(G,4);
    K           := TensorWithIntegers(R);
    UCT         := UniversalCoefficientsTheorem(K, 3);
    orbits      := AutomorphismOrbits(G, R, K, UCT);

    cocycles    := List(orbits, orbit -> rec(vec := UCT.lift*orbit[1], exp := UCT.exponent));
    return [R, cocycles];
end;

# This takes a three-cocycle and a group element and returns a two-cocycle on the centralizer of g.
# Note though that technically, the function returned is defined on the entire group though it is
# not in general a two-cocycle on the rest of the group.

TwoCocycleOnCentralizer := function(omega, g)
    local beta;

    beta := function(h, k)
        return omega(g, h, k) + omega(h, k, g) - omega(h, g, k);
    end;

    return beta;
end;

# This takes a list of positive and negative integers corresponding to generators and their inverses,
# a group and a list of generators for that group and returns the element formed by multiplying the
# generators in the order referenced in the list.

ListGenToElement := function(word, G, gens)
    local v, i;
    v := Identity(G);

    for i in word do
        if i > 0 then
            v := v*gens[i];
        else
            v := v*((gens[-i])^-1);
        fi;
    od;

    return v;
end;

# This takes a group (Cg), a cyclic group (A) and a 2-cocycle beta : Cg x Cg -> A.
# It assumes that A is expressed as a finitely presented group generated by a single element.
# It produces the group with elements in Cg x A and multiplication defined as 
# (g, a) * (h, b) = (g*h, beta(g, h)*a*b).

GroupExtension := function(Cg, exponent, beta)
    local gens, rels, m, n, RelationTwist, Embedding, relations, i, rel, F, gensF, iso, EmbedIntoGroupExtension;

    gens    := GeneratorsOfGroup(Cg);
    rels    := RelatorsOfFpGroup(Cg);
    m       := Length(gens);
    n       := m + 1;


    RelationTwist := function(word)
        local start, i, val;
        start   := Identity(Cg);
        val     := 0;
        for i in word do
            if i > 0 then
                val     := val + beta(start, gens[i]);
                start   := start*gens[i];
            else
                val     := val + beta(start, gens[-i]^-1);
                start   := start*(gens[-i]^-1);
                val     := val - beta(gens[-i]^-1, gens[-i]);
            fi;
        od;
        return (-val) mod exponent;
    end;

    Embedding := function(h)
        local word;
        word := LetterRepAssocWord(h);
        return Concatenation(word, ListWithIdenticalEntries(RelationTwist(word), n));
    end;

    relations := [ListWithIdenticalEntries(exponent, n)];

    for i in [1..m] do
        Add(relations, [i, n, -i, -n]);
    od;

    for rel in rels do
        Add(relations, Embedding(rel));
    od;

    F := FreeGroup(n);
    gensF := GeneratorsOfGroup(F);

    relations := List(relations, x -> ListGenToElement(x, F, gensF));
    F := F / relations;
    gensF := GeneratorsOfGroup(F);

    if IsSolvableGroup(Cg) then
        iso := IsomorphismPcGroup(F);
    else
        iso := IsomorphismPermGroup(F);
    fi;

    EmbedIntoGroupExtension := function(word)
        local lst, ginChExt;
        lst         := Factorization(Cg, word);
        ginChExt    := ListGenToElement(Embedding(lst), F, gensF);
        return ginChExt^iso;
    end;


    return rec(CgExtGens := gensF, CgExtPc := Image(iso), CgExtIso := iso, embedding := EmbedIntoGroupExtension);
end;

# This takes a group G, an element g in G, a cyclic group (A) and a 3-cocycle
# omega : G x G x G -> A. It produces the centralizer of g as a finitely presented group,
# an isomorphism from the centralizer of g as a subgroup of G to the previously mentioned group.
# Finally it outputs the central extension of the centralizer computed in the previous function
# with 2-cocycle as computed by TwoCocycleOnCentralizer.
# Note that in the ordering of the output, the isomorphism is first, followed by the centralizer 
# and then the central extension.

GroupExtensionOfCentralizer := function(G, g, omega, val, exponent)
    local centralizer, iso, beta, bbeta;
    centralizer := Centralizer(G, g);
    #iso         := IsomorphismFpGroup(centralizer);
    iso         := IsomorphismFpGroupByGeneratorsNC(centralizer,GeneratorsOfGroup(centralizer));
    beta        := TwoCocycleOnCentralizer(omega, g);

    bbeta       := function(h, k)
        return beta(PreImage(iso, h), PreImage(iso, k))/val;
    end;

    return [iso, centralizer, GroupExtension(Image(iso), exponent, bbeta)];
end;

# This takes a central extension of a group (CgExt) and computes the irreducible representations 
# which correspond to irreducible projective representations of the initial group with 2-cocycle
# it was extended by. The function implicitly assumes that when the central extension was 
# computed, the cyclic group that the 2-cocycle mapped into was represented by a group generated
# by a single generator.

ProjectiveCharacters := function(CgExtGens, CgExtPc, iso)
    local irr, elm, exp, ident;
    irr         := Irr(CgExtPc);
    elm         := CgExtGens[Length(CgExtGens)]^iso;
    exp         := Order(elm);
    ident       := Identity(CgExtPc);

    return Filtered(irr, i -> elm^i = (ident^i)*E(exp));
end;

# This outputs several things. The first item returned is a list of the conjugacy classes of
# CgExt. The second is a list of irreducible representations of CgExt which correspond to
# beta-projective representations on Cg. Finally, the third item returned, id, is an identification that
# links the positions of the conjugacy classes in conjClass with their respective columns in
# projectChar.

###########################################################
# We want to do something more clever in the case that G is cyclic as in this case all irreps are one dimensional and we can easily compute them without passing to the (much) more complicated group extension.
###########################################################

GenerateSimpleObjects := function(Gin, omega, val, exponent)
    local G, ccin, cc, ncc, simples, conjClass, induction, irrold, irrlist, irr, n1, In, info_iso, info, ord, cyc_Grp, gen, i, g, induction_row, beta, cycbeta, j, k, rep_coeff, rep, dict, h, reps, extensionData, iso, Cg, projCharData, EmbedIntoPCGroupExtCg;

	if IsGroup(Gin) then 
		G:=Gin;
		conjClass   := ConjugacyClasses(G); #the class of the identity is in the first position (https://docs.gap-system.org/doc/ref/chap39.html)
		ncc:=Length(conjClass);
	else
		G:=Gin[1];
		conjClass   := ConjugacyClasses(G); #the class of the identity is in the first position (https://docs.gap-system.org/doc/ref/chap39.html)
		ncc:=Length(conjClass);
		ccin:=Gin[2];
		cc:=ShallowCopy(ccin);
		SortBy(cc,k->Posinlist(conjClass,k));
		if not (IsEqualSet(Union(List(cc,k->Elements(k^G))),Elements(G)) and Length(cc)=ncc) then ErrorNoReturn("Error in cc"); fi;
	fi;
    simples     := [];
	induction   := [];

	In := function(g, h)
	        if g in h then
	            return 1;
	        else
	            return 0;
	        fi;
	    end;

	info_iso    := IsomorphismFpGroupByGeneratorsNC(G,GeneratorsOfGroup(G));

	info        := Concatenation("# Generators: ", String(GeneratorsOfGroup(Image(info_iso))), " Relations: ", String(RelatorsOfFpGroup(Image(info_iso))), "\n");

#;    if IsCyclic(G) then
#;    	ord := Order(G);
#;
#;    	cyc_Grp := CyclicGroup(IsPermGroup, ord);
#;    	iso := IsomorphismGroups(cyc_Grp, G);
#;
#;    	#gen := (GeneratorsOfGroup(cyc_Grp)[1])^iso;
#;	gen := (IndependentGeneratorsOfAbelianGroup(cyc_Grp)[1])^iso;
#;
#;    	reps := List(G, x -> [x, Identity(G)]);
#;
#;    	for i in conjClass do
#;    		g := Representative(i);
#;
#;	        induction_row := List(G, x -> In(x, i));
#;	        beta := TwoCocycleOnCentralizer(omega, g);
#;
#;	        rep_coeff := [0];
#;
#;	        for j in [1..(ord-1)] do
#;
#;	        	rep_coeff[j+1] := rep_coeff[j] + beta(gen, gen^j);
#;
#;	        od;
#;
#;	        for j in [0..(ord-1)] do
#;
#;	        	info := Concatenation(info, "# Simple Object: ", String(Length(simples) + 1), ", Element: ", String(g), " Characters: ");
#;
#;	        	Add(induction, induction_row);
#;
#;	        	rep := E(ord*exponent)^(rep_coeff[ord]/val + j*exponent);
#;
#;	        	dict := NewDictionary(false, true, G);
#;
#;	        	for k in [0..(ord-1)] do 
#;
#;	        		AddDictionary(dict, gen^k, (rep^k)*E(exponent)^(rep_coeff[k+1]/val)); 
#;
#;	        		info := Concatenation(info, " ", String(gen^k), " = ", String((rep^k)*E(exponent)^(rep_coeff[k+1]/val)), " ");
#;	        	od;
#;
#;	        	Add(simples, rec(representative := g, character := dict, conjugacyClass := reps, dimension := 1));
#;
#;	        	info := Concatenation(info, "\n");
#;
#;	        od;
#;	    od;
#;    else
	    for i in conjClass do
			  if not IsBound(cc) then
	  				g := Representative(i);
				else
					g := cc[Position(conjClass,i)];
					if not g in i then ErrorNoReturn("g not in conjClass i"); fi;
				fi;

	        induction_row := List(G, x -> In(x, i));

	        if g = Identity(G) then
					#Put the identity irrep first so that the identity anyon is the first
					irrold:=ShallowCopy(Irr(G));
					irrlist:=List(irrold,irrch->List(irrch));
					n1:=Position(irrlist,List([1..Length(irrlist)],num->1));
					irr:=[irrold[n1]];
					Remove(irrold,n1);
					irr:=Concatenation(irr,irrold);
					if not IsEqualSet(irr,Irr(G)) then ErrorNoReturn("error in irr"); fi;

	            for j in irr do

	                info := Concatenation(info, "# Simple Object: ", String(Length(simples) + 1), ", Element: ", String(g), " Characters: ");

	                Add(induction, induction_row*j[1]);

	                dict := NewDictionary(false, true, G);

	                for h in G do
	                    AddDictionary(dict, h, h^j);
	                    info := Concatenation(info, " ", String(h^info_iso), " = ", String(h^j), " ");
	                od;

	                Add(simples, rec(representative := g, character := dict, conjugacyClass := [[g, g]], dimension := j[1]));
	                info := Concatenation(info, "\n");
	            od;
	        else
	            reps := [];
	            for j in i do
	                Add(reps, [j, RepresentativeAction(G, g, j)]);
	            od;

	            extensionData           := GroupExtensionOfCentralizer(G, g, omega, val, exponent);
	            iso                     := extensionData[1];
	            Cg                      := extensionData[2];
	            projCharData            := ProjectiveCharacters(extensionData[3].CgExtGens, extensionData[3].CgExtPc, extensionData[3].CgExtIso);
	            EmbedIntoPCGroupExtCg   := extensionData[3].embedding;

	            for j in projCharData do

	                info := Concatenation(info, "# Simple Object: ", String(Length(simples) + 1), ", Element: ", String(g), " Characters: ");

	                Add(induction, induction_row*j[1]);

	                dict := NewDictionary(false, true, Cg);

	                for h in Cg do
	                    AddDictionary(dict, h, EmbedIntoPCGroupExtCg(h^iso)^j);
	                    info := Concatenation(info, " ", String(h^info_iso), " = ", String(EmbedIntoPCGroupExtCg(h^iso)^j), " ");
	                od;

	                Add(simples, rec(representative := g, character := dict, conjugacyClass := reps, dimension := j[1]));

	                info := Concatenation(info, "\n");
	            od;
	        fi;
	    od;
#;	fi;
    return rec(Simp := simples, I := induction, info := info);
end;

# This gives the coefficients for the sum over the characters.

CoefficientSSum := function(exponent, val, beta, a, b, h, l, xh, yl)
    local int;

    int := beta(a, xh, l) + beta(a, xh*l, xh^-1) + beta(b, yl, h) + beta(b, yl*h, yl^-1) - beta(h, xh^-1, xh) - beta(l, yl^-1, yl);

    return E(exponent)^(int/val);
end;

# This computes a single cell of the S matrix corresponding to two pairs of a conjugacy class
# of G with an identified element and a projective representation of the centralizer of
# that element. It will produce a number in some cyclotomic field.
# Specifically the inputs are the groups G and A, and the three-cocycle omega: GxGxG -> A.
# Additionally it takes gData and hData where gData is the list:
# [g, dict, Reps, dim]
# g is the representative from the conjugacy class.
# dict is a dictionary relating elements of the centralizer to their projective characters.
# Reps is a list of elements in the conjugacy class of g together with an element of the group that observes this fact.
# In other words, if a pair (x, h) is in Reps then g = hxh^-1.
# dim is the dimension of the representation.

sVal := function(G, exponent, val, beta, gData, hData)
    local num, ggg, hhh, iii, jjj, coeff, charVal;

    num         := 0;
    ggg         := gData.representative;
    hhh         := hData.representative;

    for iii in gData.conjugacyClass do for jjj in hData.conjugacyClass do
        if iii[1]*jjj[1] = jjj[1]*iii[1] then
            coeff   := CoefficientSSum(exponent, val, beta, ggg, hhh, iii[1], jjj[1], iii[2], jjj[2]);
            charVal := LookupDictionary(gData.character, iii[2]*jjj[1]*(iii[2]^-1))*LookupDictionary(hData.character, jjj[2]*iii[1]*(jjj[2]^-1));
            num     := num + coeff*charVal;
        fi;
    od; od;

    return ComplexConjugate(num) / Order(G);


end;

# This produces the modular data of Vec^{omega} G from the simple objects.

GenerateModularData := function(G, omega, val, exponent, simples)
    local i, j, k, numSimples, tMatrixDiagonal, cyclotomicDegree, galoisGroup, beta, sMatrix, rowsToCompute, justComputed, mysteryRows, mysteryRowPlacing, nextRow, entry, newRow, galoisConjugates, conjugateRow, possible, stillMystery, foundPlacing, mystery, possiblePlacings, stillPossible, rowsComputed;

    numSimples          := Length(simples);
    tMatrixDiagonal     := List(simples, simple -> LookupDictionary(simple.character, simple.representative)/simple.dimension);

    beta := function(g, h, k)
        return omega(g, h, k) + omega(h, k, (k^-1)*(h^-1)*g*h*k) - omega(h, (h^-1)*g*h, k);
    end;

    sMatrix             := NullMat(numSimples, numSimples);

    if IsAbelian(G) then
        for i in [1..numSimples] do for j in [i..numSimples] do
            entry := ComplexConjugate(LookupDictionary(simples[j].character, simples[i].representative)*LookupDictionary(simples[i].character, simples[j].representative)/Order(G));
            sMatrix[i][j] := entry;
            sMatrix[j][i] := entry;
        od; od;
    else
        cyclotomicDegree    := Conductor(tMatrixDiagonal);
        galoisGroup         := PrimeResidues(cyclotomicDegree);
        rowsToCompute       := [1..numSimples];
        rowsComputed        := [];
        justComputed        := [];
        mysteryRows         := [];
        mysteryRowPlacing   := [];

        while not rowsToCompute = [] do

            if justComputed = [] then

                nextRow := Remove(rowsToCompute, Random(1, Length(rowsToCompute)));
                Add(rowsComputed, nextRow);

                sMatrix[nextRow][nextRow] := sVal(G, exponent, val, beta, simples[nextRow], simples[nextRow]);
                for i in rowsToCompute do 
                    entry := sVal(G, exponent, val, beta, simples[nextRow], simples[i]);
                    sMatrix[i][nextRow] := entry;
                    sMatrix[nextRow][i] := entry;
                od;

                justComputed := [nextRow];
                newRow := sMatrix[nextRow];

                if newRow in mysteryRows then
                    i := Position(mysteryRows, newRow);
                    Remove(mysteryRows, i);
                    Remove(mysteryRowPlacing, i);
                else
                    galoisConjugates := [newRow];
                    for i in galoisGroup do
                        conjugateRow := GaloisCyc(newRow, i);
                        if not conjugateRow in galoisConjugates then
                            Add(galoisConjugates, conjugateRow);
                            Add(mysteryRows, conjugateRow);
                            possiblePlacings := [];
                            for j in rowsToCompute do
                                if ForAll(rowsComputed, k -> conjugateRow[k] = sMatrix[j][k]) then
                                    Add(possiblePlacings, j);
                                fi;
                            od;
                            Add(mysteryRowPlacing, possiblePlacings);
                        fi;
                    od;                
                fi;
            fi;

            stillMystery := [];
            foundPlacing := [];

            for i in [1..Length(mysteryRows)] do
                mystery             := mysteryRows[i];
                possiblePlacings    := mysteryRowPlacing[i];
                stillPossible       := [];
                for j in possiblePlacings do
                    if ForAll(justComputed, k -> (not j = k) and (mystery[k] = sMatrix[k][j])) then
                        Add(stillPossible, j);
                    fi;
                od;
                
                if Length(stillPossible) = 1 then
                    Add(foundPlacing, [i, stillPossible[1]]);
                else
                    mysteryRowPlacing[i] := stillPossible;
                    Add(stillMystery, i);
                fi;
            od;

            justComputed := [];

            for i in foundPlacing do
                for j in rowsToCompute do
                    sMatrix[i[2]][j] := mysteryRows[i[1]][j];
                    sMatrix[j][i[2]] := mysteryRows[i[1]][j];
                od;

                Add(justComputed, i[2]);
                Add(rowsComputed, Remove(rowsToCompute, Position(rowsToCompute, i[2])));

            od;
            
            mysteryRows         := mysteryRows{stillMystery};
            mysteryRowPlacing   := mysteryRowPlacing{stillMystery};

        od;
    fi;

    return rec(S := sMatrix, T := DiagonalMat(tMatrixDiagonal));
end;

# This produces the modular data of Vec^{omega} G.

ComputeModularData := function(G, omega, val, exponent)
    local simples_and_induction, S_and_T;

    simples_and_induction := GenerateSimpleObjects(G, omega, val, exponent);

    S_and_T := GenerateModularData(G, omega, val, exponent, simples_and_induction.Simp);

    return rec(S := S_and_T.S, T := S_and_T.T, I := simples_and_induction.I, info := simples_and_induction.info);
end;

# Implementing the Verlinde formula. This will allow us a sanity check for the Modular Data we produce.
# If the S matrix is correct then the Verlinde formula will only produce non-negative integers.
# Note that this is slow.

VerlindeFormula := function(sMatrix, a, b, c)
    local num, d;
    num := 0;
    for d in [1..DimensionsMat(sMatrix)[1]] do
        num := num + sMatrix[a][d]*sMatrix[b][d]*ComplexConjugate(sMatrix[c][d])/sMatrix[1][d];
    od;
    return num;
end;

# This checks if a given pair (sMatrix, tMatrix) could possibly be the modular data for something.
# It checks that S^2 = (ST)^3 and that the Verlinde formula only produces non-negative integers.
# Note that this is slow.

ValidModularData := function(data)
    local sMatrix, tMatrix, valid, size;
    sMatrix := data.S;
    tMatrix := data.T;

    valid   := sMatrix^2 = (sMatrix*tMatrix)^3;
    size    := DimensionsMat(sMatrix)[1];

    valid   := valid and ForAll(ListX([1..size], [1..size], [1..size], function(i, j, k) return VerlindeFormula(sMatrix, i, j, k); end), x -> (IsPosInt(x) or x = 0));

    return valid;
end;

# One of the two main functions to be used to compute and store modular data.

SaveModularDataParallel := function(n, m, N, j, detailed)
    local tme1, G, R, K, UCT, subfolder, cocyclespath, timepath, timefile, AlreadyExists, orbits, tme2, cocyclesfile, notfirst, i, fpA, datapath, datafile, vector, omega, val, exp, SandT, row;

    tme1        := Runtime();
    G           := SmallGroup(n, m);
    R           := ResolutionFiniteGroup(G,4);
    K           := TensorWithIntegers(R);
    UCT         := UniversalCoefficientsTheorem(K, 3);

    subfolder       := Concatenation("Modular_Data/", String(n), "/", String(m), "/");
    cocyclespath    := Concatenation(subfolder, "3-cocycles.txt");
    timepath        := Concatenation(subfolder, "timing.txt");

    AlreadyExists := function(path)
        local str;
        if IsExistingFile(path) then
            str := StringFile(path);
            if Length(str) < 2 then
                return false;
            fi;
            return str{[Length(str) - 1, Length(str)]} = ";;";
        fi;
        return false;
    end;

    if AlreadyExists(cocyclespath) then
        orbits      := ReadAsFunction(cocyclespath)();
    else
        orbits      := AutomorphismOrbits(G, R, K, UCT);
        orbits      := List(orbits, orbit -> UCT.lift*orbit[1]);

        tme2        := Runtime() - tme1;

        timefile    := IO_File(timepath, "w");
        IO_Write(timefile, "Computing the 3-cocycles took ", Floor(tme2/1000.), " seconds.\n");
        IO_Close(timefile);

        cocyclesfile    := IO_File(cocyclespath, "w");
        IO_Write(cocyclesfile, "return [");

        notfirst := false;
        for i in orbits do

            if notfirst then
                IO_Write(cocyclesfile, ",\n");
            fi;

            IO_Write(cocyclesfile, i);
            notfirst := true;
        od;

        IO_Write(cocyclesfile, "];;");
        IO_Close(cocyclesfile);
    fi;

    for i in [1..Length(orbits)] do
        if i mod N = j then
            datapath := Concatenation(subfolder, String(i), ".txt");

            if not AlreadyExists(datapath) then
                
                tme1    := Runtime();

                vector  := orbits[i];
                omega   := StandardCocycle(R, vector, 3, UCT.exponent);
                val     := Gcd(Gcd(vector), UCT.exponent);
                exp     := UCT.exponent/val;
                SandT   := ComputeModularData(G, omega, val, exp);

                tme2    := Runtime() - tme1;

                timefile    := IO_File(timepath, "a");
                IO_Write(timefile, "Computing the modular data for cocycle number ", i, "/", Length(orbits), " took ", Floor(tme2/1000.), " seconds.\n");
                IO_Close(timefile);

                datafile    := IO_File(datapath, "w", (2^4)*(Order(G)^2));

                if detailed then
                    IO_Write(datafile, SandT.info);
                fi;

                IO_Write(datafile, "local S, T;\nS := [");
                notfirst := false;
                for row in SandT.S do
                    if notfirst then
                        IO_Write(datafile, ", ");
                    fi;
                    IO_Write(datafile, row);
                    IO_Flush(datafile);
                    notfirst := true;
                od;
                IO_Write(datafile, "];\nT := ", DiagonalOfMat(SandT.T), ";\nreturn rec(S := S, T := T);;");
                IO_Close(datafile);
            fi;
        fi;
    od;
end;

# Save modular data for a given group order

SaveAllDataForGivenOrder := function(n)
    local num, i;

    num := NumberSmallGroups(n);

    for i in [1..num] do
        SaveModularDataParallel(n, i, 1, 0, false);
    od;
end;

# Compute a lot of modular data

ComputeDataForever := function()
    local i;

    for i in [2..100] do
        SaveAllDataForGivenOrder(i);
    od;
end;

# This function allows for data to be computed in a parallel manner with each thread computing a different group.
# The reason that the parallelisation splits according to groups as opposed to using the numbering of cocycles within
# groups is to prevent issues where multiple threads try and construct the same 3-cocycles file.

ComputeDataForeverParallel := function(start, finish, N, i, detailed)
    local j, k;

    for j in [start..finish] do
        for k in [1..NumberSmallGroups(j)] do
            if (j + k) mod N = i then
                SaveModularDataParallel(j, k, 1, 0, detailed);
            fi;
        od;
    od;
end;

ComputeNonAbelianDataForeverParallel := function(start, finish, N, i, detailed)
    local j, k;

    for j in [start..finish] do
        for k in [1..NumberSmallGroups(j)] do
            if (j + k) mod N = i then
                if not IsAbelian(SmallGroup(j, k)) then
                    SaveModularDataParallel(j, k, 1, 0, detailed);
                fi;
            fi;
        od;
    od;
end;


# Load some modular data.

LoadModularData := function(n, m, i)
    local filename, data;

    filename := Concatenation("Modular_Data/", String(n), "/", String(m), "/", String(i), ".txt");

    if IsExistingFile(filename) then
        data := ReadAsFunction(filename)();
        return rec(S := data.S, T := DiagonalMat(data.T));

    else
        Print("Error: There is no stored modular data for cocycle ", i, " for SmallGroup(", m, ", ", n, ")");
    fi;
end;

# If we only want to use the T matrix, it is much quicker to load it by itself and not with 
# the S matrix. This function returns the diagonal of the T matrix as a vector. You need to 
# have created the _T files but this is easy to do with a simple Python script.
# In the script replace "local S, T;" with "local T;" and 
# "return rec(S := S, T := T);;" with "return T;;"

LoadTMatrix := function(n, m, i)
    local filename, data;

    filename := Concatenation("Modular_Data/", String(n), "/", String(m), "/", String(i), "_T.txt");

    if IsExistingFile(filename) then
        return ReadAsFunction(filename)();
    else
        Print("Error: There is no stored T Matrix for cocycle ", i, " for SmallGroup(", m, ", ", n, "). Have you created these files yet?");
    fi;
end;

# Run a simple sanity test on the modular data.

TestData := function(i, j)
    local allValid, cocyclesfile, cocycles, k, data;

    cocyclesfile := Concatenation("Modular_Data/", String(i), "/", String(j), "/3-cocycles.txt");

    cocycles := ReadAsFunction(cocyclesfile)();

    for k in [1..Length(cocycles)] do
        data := LoadModularData(i, j, k);
        Print(data.S^2 = (data.S*data.T)^3, " ");
        Print(IsDiagonalMat(data.S^4), "\n");
    od;
end;

SaveModularDataTimed := function(n, m, maxtime, currenttime, lasttime)
    local tme1, G, R, K, UCT, subfolder, cocyclespath, timepath, timefile, AlreadyExists, orbits, tme2, cocyclesfile, notfirst, i, fpA, datapath, datafile, vector, omega, val, exp, SandT, newcurrenttime, newlasttime, row;

    tme1        := Runtime();
    G           := SmallGroup(n, m);
    R           := ResolutionFiniteGroup(G,4);
    K           := TensorWithIntegers(R);
    UCT         := UniversalCoefficientsTheorem(K, 3);

    subfolder       := Concatenation("Modular_Data/", String(n), "/", String(m), "/");
    cocyclespath    := Concatenation(subfolder, "3-cocycles.txt");
    timepath         := Concatenation(subfolder, "timing.txt");

    AlreadyExists := function(path)
        local str;
        if IsExistingFile(path) then
            str := StringFile(path);
            if Length(str) < 2 then
                return false;
            fi;
            return str{[Length(str) - 1, Length(str)]} = ";;";
        fi;
        return false;
    end;


    if AlreadyExists(cocyclespath) then
        orbits      := ReadAsFunction(cocyclespath)();
    else
        orbits      := AutomorphismOrbits(G, R, K, UCT);
        orbits      := List(orbits, orbit -> UCT.lift*orbit[1]);
        tme2        := Runtime() - tme1;

        timefile    := IO_File(timepath, "w");
        IO_Write(timefile, "Computing the 3-cocycles took ", Floor(tme2/1000.), " seconds.\n");
        IO_Close(timefile);

        cocyclesfile    := IO_File(cocyclespath, "w");
        IO_Write(cocyclesfile, "return [");

        notfirst := false;
        for i in orbits do

            if notfirst then
                IO_Write(cocyclesfile, ",\n");
            fi;

            IO_Write(cocyclesfile, i);
            notfirst := true;
        od;

        IO_Write(cocyclesfile, "];;");
        IO_Close(cocyclesfile);
    fi;

    newlasttime := lasttime;
    newcurrenttime := currenttime + Runtime() - tme1;

    for i in [1..Length(orbits)] do
        datapath := Concatenation(subfolder, String(i), ".txt");

        if newcurrenttime + 10*newlasttime < maxtime then
            if not AlreadyExists(datapath) then
                tme1    := Runtime();

                vector  := orbits[i];
                omega   := StandardCocycle(R, vector, 3, UCT.exponent);
                val     := Gcd(Gcd(vector), UCT.exponent);
                exp     := UCT.exponent/val;
                SandT   := ComputeModularData(G, omega, val, exp);

                tme2    := Runtime() - tme1;

                timefile := IO_File(timepath, "a");
                IO_Write(timefile, "Computing the modular data for cocycle number ", i, "/", Length(orbits), " took ", Floor(tme2/1000.), " seconds.\n");
                IO_Close(timefile);
                
                datafile    := IO_File(datapath, "w", (2^4)*(Order(G)^2));

                IO_Write(datafile, "local S, T;\nS := [");
                notfirst := false;
                for row in SandT.S do
                    if notfirst then
                        IO_Write(datafile, ", ");
                    fi;
                    IO_Write(datafile, row);
                    IO_Flush(datafile);
                    notfirst := true;
                od;
                IO_Write(datafile, "];\nT := ", DiagonalOfMat(SandT.T), ";\nreturn rec(S := S, T := T);;");
                IO_Close(datafile);

                newlasttime := Runtime() - tme1;
                newcurrenttime := newcurrenttime + Runtime() - tme1;
            fi;
        fi;          
    od;
    return [newlasttime, newcurrenttime, newcurrenttime + 10*lasttime < maxtime];

end;


ComputeDataFor48HoursParallel := function(m, N, i)
    local j, k, maxtime, currenttime, lasttime, timeleft, data;

    maxtime     := 172800000;
    currenttime := 0;
    lasttime    := 0;
    timeleft    := true;

    for j in [m..100] do
        for k in [1..NumberSmallGroups(j)] do
            if (j + k) mod N = i and timeleft then
                data        := SaveModularDataTimed(j, k, maxtime, currenttime, lasttime);
                lasttime    := data[1];
                currenttime := data[2];
                timeleft    := data[3];
            fi;
        od;
    od;
end;

# Compute modular data for the n'th cocycle orbit of the m'th group of order l.

ComputeALittleData := function(l, m, n)
    local G, data, cocycle, omega, val, exponent, SandT;

    G           := SmallGroup(l, m);
    data        := ThreeCocyclesUpToAutomorphism(G);
    cocycle     := data[2][n];
    omega       := StandardCocycle(data[1], cocycle.vec, 3, cocycle.exp);
    val         := Gcd(Gcd(cocycle.vec), cocycle.exp);
    exponent    := cocycle.exp/val;
    SandT       := ComputeModularData(G, omega, val, exponent);
    return SandT;
end;

# The following collects some data on the ranks of the centers:

FindRanksOfCenter := function(order)
    local num, ranks, multiplicitely, pair, i, subdir, cocyclesfilePath, cocycles, f, tList, rank1, groupranks, groupmultiplicitely, k, data, rank, pos, str, multiplicitelyOrbits, grp;

    num             := NumberSmallGroups(order);
    ranks           := [];
    multiplicitely  := [];

    pair := function(x, y)
        return [x, y];
    end;

    for i in [1..num] do

        subdir := Concatenation("Modular_Data/", String(order), "/", String(i), "/");


        cocyclesfilePath := Concatenation(subdir, "3-cocycles.txt");


        cocycles := ReadAsFunction(cocyclesfilePath)();

        f := IO_File(Concatenation(subdir, "1.txt"));
        tList := IO_ReadLines(f, 3)[3];
        IO_Close(f);
        rank1 := Number(tList, x -> x = ',') + 1;
        groupranks := [rank1];
        groupmultiplicitely  := [1];
        if rank1 in ranks then
                pos := Position(ranks, rank1);
                multiplicitely[pos] := multiplicitely[pos] + 1;
        else
                Add(ranks, rank1);
                Add(multiplicitely, 1);
        fi;

        for k in [2..Length(cocycles)] do
            f := IO_File(Concatenation(subdir, String(k), ".txt"));
            tList := IO_ReadLines(f, 3)[3];
            IO_Close(f);
            rank := Number(tList, x -> x = ',') + 1;
            if rank in ranks then
                pos := Position(ranks, rank);
                multiplicitely[pos] := multiplicitely[pos] + 1;
            else
                Add(ranks, rank);
                Add(multiplicitely, 1);
            fi;
            if rank in groupranks then
                pos := Position(groupranks, rank);
                groupmultiplicitely[pos] := groupmultiplicitely[pos] + 1;
            else
                Add(groupranks, rank);
                Add(groupmultiplicitely, 1);
            fi;
        od;
        Print("SmallGroup(", order, ", ", i, ")  Abelian:  ", IsAbelian(SmallGroup(order, i)), "   ",rank1, "   ", ListN(groupranks, groupmultiplicitely, pair), "\n");
    od;

    f := IO_File(Concatenation("Modular_Data/Orbits/", String(order), "/Orbits.txt"));
    str := List(IO_ReadLines(f), x -> EvalString(StripLineBreakCharacters(x)));
    IO_Close(f);
    multiplicitelyOrbits  := ListWithIdenticalEntries(Length(ranks), 0);
    for i in str do
        grp := i[1];
        f := IO_File(Concatenation("Modular_Data/", String(order), "/", String(grp[1]), "/", String(grp[2]), ".txt"));
        tList := IO_ReadLines(f, 3)[3];
        IO_Close(f);
        rank := Number(tList, x -> x = ',') + 1;
        pos := Position(ranks, rank);
        multiplicitelyOrbits[pos] := multiplicitelyOrbits[pos] + 1;
    od;

    return [ranks, multiplicitely, multiplicitelyOrbits];
end;


# The following runs a couple of basic tests to see if the two sets of 
# modular data could be equivalent. It checks to make sure the ranks are the same
# and the sorted T matrix is the same. Additionally checks the S matrix diagonals
# and the rows of the S matrices.
# I would not recommend using this for any order above 8, it is very slow.

BasicEquivalentModularDataTests := function(data1, data2)
    local t1, t2, s1, s2, perm1, perm2, rank, RLE, multiplicities, perms1, perms2, perm1Mat, perm2Mat, sMatrix1, sMatrix2, perms1Mat, perms2Mat, innerAut1, groups, mats1, mats2, i, j, start, finish, test;

    if data1.S = data2.S and data1.T = data2.T then
        return true;
    fi;

    t1 := DiagonalOfMat(data1.T);
    t2 := DiagonalOfMat(data2.T);

    s1 := DiagonalOfMat(data1.S);
    s2 := DiagonalOfMat(data2.S);

    # Print(t1, "\n", t2, "\n");

    perm1 := Sortex(t1);
    perm2 := Sortex(t2);

    # Print(t1, "\n", t2, "\n");

    if t1 = t2 then

        rank := Length(t1);

        RLE := function(lst)
            local encoding, previous, i, j;

            encoding := [rec(value := lst[1], start := 1)];
            previous := lst[1];
            i := 1;
            for j in [1..Length(lst)] do
                if not lst[j] = previous then
                    encoding[i].finish := j - 1;
                    encoding[i + 1] := rec(value := lst[j], start := j);
                    previous := lst[j];
                    i := i + 1;
                fi;
            od;
            encoding[Length(encoding)].finish := j;
            return encoding;
        end;

        # Print(s1, "\n", s2, "\n");

        s1 := Permuted(s1, perm1);
        s2 := Permuted(s2, perm2);

        multiplicities := RLE(t1);
        # Print(multiplicities);

        # Print(s1, "\n", s2, "\n");

        s1 := List(multiplicities, x -> s1{[x.start..x.finish]});
        s2 := List(multiplicities, x -> s2{[x.start..x.finish]});

        perms1 := List(s1, x -> ListPerm(Sortex(x), Length(x)));
        perms2 := List(s2, x -> ListPerm(Sortex(x), Length(x)));

        # Print(s1, "\n", s2, "\n");

        if s1 = s2 then

            perm1Mat := PermutationMat(perm1, rank);
            perm2Mat := PermutationMat(perm2, rank);

            sMatrix1 := (perm1Mat^-1)*data1.S*perm1Mat;
            sMatrix2 := (perm2Mat^-1)*data2.S*perm2Mat;

            for i in [1..Length(multiplicities)] do
                perms1[i] := perms1[i] + multiplicities[i].start - 1;
                perms2[i] := perms2[i] + multiplicities[i].start - 1;
            od;

            perms1Mat   := PermutationMat(PermList(Flat(perms1)), rank);
            perms2Mat   := PermutationMat(PermList(Flat(perms2)), rank);

            sMatrix1 := (perms1Mat^-1)*sMatrix1*perms1Mat;
            sMatrix2 := (perms2Mat^-1)*sMatrix2*perms2Mat;

            # Display(sMatrix1);
            # Display(sMatrix2);

            innerAut1 := List(s1, x -> RLE(x));

            # Print(innerAut1, "\n");

            mats1   := [];
            mats2   := [];

            for i in [1..Length(innerAut1)] do
                for j in innerAut1[i] do
                    start   := j.start + multiplicities[i].start - 1;
                    finish  := j.finish + multiplicities[i].start - 1;
                    Add(mats1, sMatrix1{[start..finish]});
                    Add(mats2, sMatrix2{[start..finish]});
            od; od;

            test := function(mat1, mat2)
                local i;

                for i in mat1 do
                    Sort(i);
                od;
                Sort(mat1);

                for i in mat2 do
                    Sort(i);
                od;
                Sort(mat2);

                return mat1 = mat2;
            end;

            return ForAll([1..Length(mats1)], i -> test(mats1[i], mats2[i]));
        fi;
    fi;

    return false;
end;

# Find the equivalence classes of the T matrices.
# In order to run this you need to write a Python file to create _T.txt 
# files containing just the T matrix not the S matrix.
# In the script replace "local S, T;" with "local T;" and 
# "return rec(S := S, T := T);;" with "return T;;"

OrbitsOfTMatrix := function(order)
    local data, reference, ranks, multiplicitely, orbits, i, cocyclesfile, cocycles, modular_data, tdiag, rank, pos, k, vals, current, orbit, orbitsfile;

    data            := [];
    reference       := [];
    ranks           := [];
    multiplicitely  := [];
    orbits          := [];

    for i in [1..NumberSmallGroups(order)] do

        cocyclesfile := Concatenation("Modular_Data/", String(order), "/", String(i), "/3-cocycles.txt");

        cocycles := ReadAsFunction(cocyclesfile)();

        for k in [1..Length(cocycles)] do
            tdiag := LoadTMatrix(order, i, k);
            Sort(tdiag);
            rank := Length(tdiag);
            if rank in ranks then
                pos := Position(ranks, rank);
                Add(data[pos], tdiag);
                Add(reference[pos], [i, k]);
            else
                Add(ranks, rank);
                Add(data, [tdiag]);
                Add(reference, [[i, k]]);
            fi;
        od;
    od;

    for i in [1..Length(data)] do

        vals := [1..Length(data[i])];
        multiplicitely[i] := 0;

        while not vals = [] do
            multiplicitely[i] := multiplicitely[i] + 1;
            current := data[i][vals[1]];
            orbit   := Filtered(vals, x -> current = data[i][x]);
            vals    := Filtered(vals, x -> not x in orbit);
            Add(orbits, [orbit, i]);
        od;
    od;

    orbits := List(orbits, orbit -> List(orbit[1], x -> reference[orbit[2]][x]));

    orbitsfile := IO_File(Concatenation("Modular_Data/", String(order), "/TMatrixOrbits.txt"), "w");
   
    for i in orbits do
        IO_Write(orbitsfile, i);
        IO_Write(orbitsfile, "\n");
    od;

    IO_Close(orbitsfile);
    return [ranks, multiplicitely];
end;

# The minimal value of lower is 2.

ComputeTOrbitsBetween := function(lower, upper)
    local i, acc, perm;

    for i in [lower..upper] do
        acc     := OrbitsOfTMatrix(i);
        perm    := Sortex(acc[1]);
        acc[2]   := Permuted(acc[2], perm);
        Print(i, " ", acc, "\n");
    od;
end;
