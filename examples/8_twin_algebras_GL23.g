## https://github.com/AlisonWarman/AlgebrasTQD
#############################################################################
##
##  8_twin_algebras_GL23.g                      AlgebrasTQD examples
##
##  Analytic GL(2,3) twin phases of arXiv:2605.31601
##  Usage: Read("path/to/AlgebrasTQD/examples/8_twin_algebras_GL23.g")
##
#############################################################################

Read(ReplacedString(INPUT_FILENAME(),"8_twin_algebras_GL23.g","../AlgebrasTQD.g"));
Section := function(title) Print("\n",title,"\n\n"); end;;

# Generators from arXiv:2605.31601
Section("GL(2,3) in the notation of the Twin Phases paper arXiv:2605.31601");
Had := [[1,1],[1,-1]]/Sqrt(2);;
Phase := DiagonalMat([1,E(4)]);;
x := [[0,1],[1,0]];; z := DiagonalMat([1,-1]);;
Mcliff := Group([Had,(Had*Phase)^8]);;
isoMG := IsomorphismPcGroup(Mcliff);;
G := MakeGroup(Image(isoMG));;
h := Image(isoMG,Had);;
c := Image(isoMG,-IdentityMat(2));;
a := Image(isoMG,E(8)^3*Had*Phase*x);;
xz := Image(isoMG,x*z);;
iz := Image(isoMG,E(4)*z);;
RelabelGroup(G,["h","c","a","xz","iz"],[h,c,a,xz,iz]);;
if IdGroup(G)<>[48,29] or c<>xz^2 or c<>iz^2 then
    ErrorNoReturn("The Clifford generators do not give the paper's GL(2,3)");
fi;
S31 := Group(a,h);; S32 := Group(a,h*c);;
Q8 := Group(xz,iz);; D12 := Group(a,h,c);; Z3 := Group(a);;
if Size(S31)<>6 or Size(S32)<>6 or IsConjugate(G,S31,S32) or
   Size(Q8)<>8 or Size(D12)<>12 or Intersection(S31,S32)<>Z3 then
    ErrorNoReturn("The named subgroups disagree with arXiv:2605.31601");
fi;
Print("G = ",IdGroup(G),", S3^(1) = <a,h>, S3^(2) = <a,hc>, Q8 = <xz,iz>, D12 = <a,h,c>\n");

# Paper charge and flux labels
classWords := ["1","c","a","ca","h","iz","hiz","hiz^3"];;
classReps := List(classWords,w->GroupElement(G,w));;
if Length(Set(List(classReps,g->ConjugacyClass(G,g))))<>8 then
    ErrorNoReturn("The character-table representatives are incomplete");
fi;
paperChars := [
    [1,1,1,1,1,1,1,1],
    [1,1,1,1,-1,1,-1,-1],
    [2,2,-1,-1,0,2,0,0],
    [2,-2,-1,1,0,0,E(8)+E(8)^3,-E(8)-E(8)^3],
    [2,-2,-1,1,0,0,-E(8)-E(8)^3,E(8)+E(8)^3],
    [3,3,0,0,1,-1,-1,-1],
    [3,3,0,0,-1,-1,1,1],
    [4,-4,1,-1,0,0,0,0] ];;
chargeLabels := ["1","rho_{1-}","rho_2","rho_{2+}","rho_{2-}","rho_3","rho_{3-}","rho_4"];;

PaperLabels := function(th)
    local labels,i,g,ch,n,sign;
    labels := ShallowCopy(th.labels);
    for i in [1..Length(th.aG)] do
        g := th.aG[i][1];
        if IsOne(g) then
            ch := List(classReps,t->LookupDictionary(th.aG[i][2],t));
            n := Position(paperChars,ch);
            if n=fail then ErrorNoReturn("An irrep does not match Table chGL23: ",ch); fi;
            labels[i] := chargeLabels[n];
        elif g=h then
            ch := List([h,c],t->LookupDictionary(th.aG[i][2],t));
            if not ForAll(ch,t->t in [-1,1]) then ErrorNoReturn("Unexpected h-flux character: ",ch); fi;
            labels[i] := Concatenation("[h]_{",List(ch,function(t) if t=1 then return '+'; else return '-'; fi; end),"}");
        elif g=a then
            ch := List([a,c],t->LookupDictionary(th.aG[i][2],t));
            if not ch[1] in [1,E(3),E(3)^2] or not ch[2] in [-1,1] then
                ErrorNoReturn("Unexpected a-flux character: ",ch);
            fi;
            if ch[2]=1 then sign := "+"; else sign := "-"; fi;
            if ch[1]=1 then labels[i] := Concatenation("[a]_{+",sign,"}");
            else labels[i] := Concatenation("[a]_{",String(Position([1,E(3),E(3)^2],ch[1])-1),sign,"}"); fi;
        fi;
    od;
    if Length(Set(labels))<>Length(labels) then ErrorNoReturn("The paper anyon labels are not distinct"); fi;
    return labels;
end;;

ClassOn := function(M,H,F)
    local matches;
    matches := Filtered([1..Length(M.classes)],i->ForAny(M.classes[i].algebras,A->ForAny(G,g->A[1]^g=H and A[2]^g=F)));
    if Length(matches)<>1 then ErrorNoReturn("Expected one algebra class on ",H,", ",F,", found ",matches); fi;
    return matches[1];
end;;

CheckAnyons := function(th,cl,expected)
    local actual;
    actual := List(Filtered([1..Length(cl.na)],i->cl.na[i]<>0),i->[th.labels[i],cl.na[i]]);
    if Set(actual)<>Set(List(expected,s->[s,1])) then
        ErrorNoReturn("Anyon decomposition differs from arXiv:2605.31601: ",actual);
    fi;
    Print(cl.decomposition,"\n");
end;;

twinAnyons := ["1","rho_3","rho_4","[h]_{++}","[h]_{+-}","[a]_{++}","[a]_{+-}"];;
commonAnyons := ["1","rho_3","[a]_{++}"];;
omega := fail;;

ShowPaperAlgebras := function(th,withOmega)
    local classes,lag1,lag2,mid,Hs,lower,k,j,small1,small2,charge1,charge2,phases;
    classes := AlgebraClasses(th);
    lag1 := ClassOn(classes,S31,S31);
    lag2 := ClassOn(classes,S32,S32);
    if not Set([lag1,lag2]) in List(classes.twins,Set) then
        ErrorNoReturn("The two S3 Lagrangians are not a twin pair");
    fi;
    Print(Length(classes.classes)," algebra classes, ",Length(classes.twins)," twin pairs\n");
    Print("L_{S3^(1)} = "); CheckAnyons(th,classes.classes[lag1],twinAnyons);
    Print("L_{S3^(2)} = "); CheckAnyons(th,classes.classes[lag2],twinAnyons);
    mid := ClassOn(classes,D12,Z3);
    Print("A(D12,Z3) = "); CheckAnyons(th,classes.classes[mid],commonAnyons);
    Hs := Hasse(th,classes);
    if not ([mid,lag1] in Hs.inclusions and [mid,lag2] in Hs.inclusions) then
        ErrorNoReturn("A(D12,Z3) is not contained in both twins");
    fi;
    lower := Filtered([1..Length(classes.classes)],i->
        [i,lag1] in Hs.inclusions and [i,lag2] in Hs.inclusions);
    if Maximum(List(lower,i->classes.classes[i].dim))<>classes.classes[mid].dim then
        ErrorNoReturn("A(D12,Z3) is not a largest common proper subalgebra");
    fi;
    Print("Largest common proper algebra: A(D12,Z3), dimension ",classes.classes[mid].dim,"\n");
    if withOmega then
        if gammaf([D12,omega])<>fail then ErrorNoReturn("D12 unexpectedly admits a gapped boundary"); fi;
        if gammaf([Q8,omega])<>fail then ErrorNoReturn("Q8 unexpectedly admits a gauging boundary"); fi;
        if Length(classes.twins)<>3 then ErrorNoReturn("Expected the three twin pairs in Table Galg-short"); fi;
        charge1 := ClassOn(classes,S31,TrivialSubgroup(G));
        charge2 := ClassOn(classes,S32,TrivialSubgroup(G));
        small1 := ClassOn(classes,S31,Z3);
        small2 := ClassOn(classes,S32,Z3);
        if not Set([charge1,charge2]) in List(classes.twins,Set) or
           not Set([small1,small2]) in List(classes.twins,Set) then
            ErrorNoReturn("The two non-Lagrangian twin pairs of the paper are missing");
        fi;
        Print("A(S3^(1),1) = "); CheckAnyons(th,classes.classes[charge1],["1","rho_3","rho_4"]);
        Print("A(S3^(2),1) = "); CheckAnyons(th,classes.classes[charge2],["1","rho_3","rho_4"]);
        Print("A(S3^(1),Z3) = "); CheckAnyons(th,classes.classes[small1],["1","rho_3","rho_4","[a]_{++}","[a]_{+-}"]);
        Print("A(S3^(2),Z3) = "); CheckAnyons(th,classes.classes[small2],["1","rho_3","rho_4","[a]_{++}","[a]_{+-}"]);
        phases := PhaseLabels(th,lag1,Hs);
        if List([lag1,lag2],i->phases[i])<>["SSB","SSB"] then
            ErrorNoReturn("The twins are not both SSB phases for C(G,S3^(1))");
        fi;
        Print("Both twins are full SSB phases for C(G,S3^(1))\n");
        Print("D12 is anomalous, while A(D12,Z3) has reduced D^omega_II(Z2 x Z2)\n");
    else
        if gammaf(D12)=fail then ErrorNoReturn("The untwisted D12 gapped boundary is missing"); fi;
        Print("Untwisted D12 admits a gapped boundary L_{D12}\n");
    fi;
    for k in [1..Length(classes.twins)] do
        Print("Twin pair ",k,", inequivalent since ",classes.reasons[k][2],":\n");
        for j in classes.twins[k] do
            Print("  ",classes.classes[j].name," = ",classes.classes[j].decomposition,"\n");
        od;
    od;
    return rec(classes:=classes,Hs:=Hs,twins:=[lag1,lag2],common:=mid);
end;;

Section("Trivial omega: twin algebras and their common interface");
th := TQDTheory(G);;
th.labels := PaperLabels(th);;
untwisted := ShowPaperAlgebras(th,false);;

Print("\nCompute twin algebras with non-trivial 3-cocycle omega?\n[yes/no]\n");
computeOmega := ReadLine(InputTextUser());;
if computeOmega=fail then
    computeOmega := "no";
else
    computeOmega := LowercaseString(Filtered(computeOmega,ch->not ch in "\r\n \t"));
fi;
while not computeOmega in ["yes","no"] do
    Print("Please answer yes or no:\n");
    computeOmega := ReadLine(InputTextUser());
    if computeOmega=fail then
        computeOmega := "no";
    else
        computeOmega := LowercaseString(Filtered(computeOmega,ch->not ch in "\r\n \t"));
    fi;
od;

if computeOmega="yes" then
# Cocycle data in the paper's group-element order
Section("Nontrivial omega: the mixed anomaly and the twin phases");
Read(ReplacedString(INPUT_FILENAME(),"examples/8_twin_algebras_GL23.g","examples/GL23-om-data.g"));
omEl := List(omlab,w->GroupElement(G,w));;
if Length(omEl)<>Size(G) or Length(Set(omEl))<>Size(G) then
    ErrorNoReturn("The omega table does not label each group element exactly once");
fi;
omPos := NewDictionary(omEl[1],true);;
for i in [1..Length(omEl)] do AddDictionary(omPos,omEl[i],i); od;
omega := rec(a:=function(u,v,w)
    return omtab[LookupDictionary(omPos,u)][LookupDictionary(omPos,v)][LookupDictionary(omPos,w)];
end,N:=16,G:=G);;
if not 3coctest([Elements(G),omega]) then ErrorNoReturn("omega is not a normalized 3-cocycle"); fi;
if not ForAll([S31,S32],H->ForAll(Elements(H),u->ForAll(Elements(H),v->
    ForAll(Elements(H),w->omega.a(u,v,w) mod omega.N=0)))) then
    ErrorNoReturn("omega is not identically trivial on both S3 subgroups");
fi;
K := AbelianGroup([2,2]);;
m1 := Elements(K)[2];; m2 := Elements(K)[3];;
coords := function(g)
    if g=One(K) then return [0,0]; elif g=m1 then return [1,0];
    elif g=m2 then return [0,1]; else return [1,1]; fi;
end;;
omegaII := function(u,v,w)
    local b1,b2,b3;
    b1:=coords(u); b2:=coords(v); b3:=coords(w);
    return 8*b1[1]*b2[1]*b3[2];
end;;
quotient := GroupHomomorphismByImages(D12,K,[h,h*c,a],[m1,m2,One(K)]);;
if quotient=fail or Size(Image(quotient))<>4 or Kernel(quotient)<>Z3 or
   not ForAll(Elements(D12),u->ForAll(Elements(D12),v->ForAll(Elements(D12),w->
       (omega.a(u,v,w)-omegaII(Image(quotient,u),Image(quotient,v),Image(quotient,w))) mod 16=0))) then
    ErrorNoReturn("omega|D12 is not the paper's pullback of omega_II");
fi;
Print("omega|S3^(1) = omega|S3^(2) = 1, omega|D12 = pullback of omega_II\n");
thom := TQDTheory(G,omega);;
thom.labels := PaperLabels(thom);;
twisted := ShowPaperAlgebras(thom,true);;

# Check (InterfaceMap)
Section("Interface: the analytic anyon map");
Aint := First(twisted.classes.classes[twisted.common].algebras,A->A[1]=D12 and A[2]=Z3);;
mapth := ShallowCopy(thom);;
mapth.aG := List(thom.aG,ShallowCopy);;
for i in [1..Length(mapth.aG)] do mapth.aG[i][4] := thom.labels[i]; od;
I := InterfaceMap(mapth,Aint,rec(gen:=[h,h*c]));;
RowSupport := function(row)
    if ForAny(row,n->n>1) then ErrorNoReturn("Unexpected multiplicity in the interface map"); fi;
    return Set(List(Filtered([1..Length(row)],i->row[i]<>0),i->thom.labels[i]));
end;;
supports := List(I.m,RowSupport);;
expectedRows := [
    [["1","rho_3","[a]_{++}"],1],
    [["rho_{1-}","rho_{3-}","[a]_{++}"],1],
    [["rho_4","[a]_{+-}"],2],
    [["[h]_{++}"],2],
    [["[h]_{+-}"],2],
    [["[h]_{-+}"],2],
    [["[h]_{--}"],2] ];
if Length(I.aK)<>16 or not ForAll(expectedRows,p->Number(supports,s->s=Set(p[1]))=p[2]) then
    ErrorNoReturn("The vacuum, electric or single-flux rows disagree with (InterfaceMap)");
fi;
diagonalRows := Filtered([1..Length(I.m)],r->ForAny([1..Length(I.m[r])],j->
    I.m[r][j]<>0 and thom.aG[j][1] in [c,c*a]));;
if Length(diagonalRows)<>4 or
   not ForAll(diagonalRows,r->ForAll(Filtered([1..Length(I.m[r])],j->I.m[r][j]<>0),
       j->thom.aG[j][1] in [c,c*a])) then
    ErrorNoReturn("The four diagonal-flux rows disagree with (InterfaceMap)");
fi;
diagonalSpins := List(diagonalRows,r->ComplexConjugate(
    LookupDictionary(I.aK[r][2],I.aK[r][1])/LookupDictionary(I.aK[r][2],One(I.K))));;
if Number(diagonalSpins,s->s=E(4))<>2 or Number(diagonalSpins,s->s=-E(4))<>2 then
    ErrorNoReturn("The diagonal-flux topological spins are not two +i and two -i");
fi;
RowIndices := r->Filtered([1..Length(I.m[r])],j->I.m[r][j]<>0);;
minusRows := Filtered(diagonalRows,r->diagonalSpins[Position(diagonalRows,r)]=-E(4));;
plusRows := Filtered(diagonalRows,r->diagonalSpins[Position(diagonalRows,r)]=E(4));;
acMinus := Filtered(Intersection(RowIndices(minusRows[1]),RowIndices(minusRows[2])),
    j->thom.aG[j][1]=c*a);;
acPlus := Filtered(Intersection(RowIndices(plusRows[1]),RowIndices(plusRows[2])),
    j->thom.aG[j][1]=c*a);;
if Length(acMinus)<>1 or Length(acPlus)<>1 or
   LookupDictionary(thom.aG[acMinus[1]][2],c*a)<>-E(4) or
   LookupDictionary(thom.aG[acPlus[1]][2],c*a)<>E(4) then
    ErrorNoReturn("The [ac] anyons in the diagonal-flux rows disagree with (InterfaceMap)");
fi;
cAnyons := Filtered([1..Length(thom.aG)],j->thom.aG[j][1]=c);;
# Projective c-flux tensor products
TensorC := function(p,label)
    local q,matches;
    q := Position(thom.labels,label);
    matches := Filtered(cAnyons,j->ForAll(Elements(G),g->
        LookupDictionary(thom.aG[j][2],g)=
        LookupDictionary(thom.aG[p][2],g)*LookupDictionary(thom.aG[q][2],g)));
    if Length(matches)<>1 then ErrorNoReturn("The projective tensor product is not a unique c-flux anyon"); fi;
    return matches[1];
end;;
baseCandidates := Filtered(Union(RowIndices(minusRows[1]),RowIndices(minusRows[2])),
    j->thom.aG[j][1]=c and dima(thom.aG[j],One(G))=1);;
if not ForAny(baseCandidates,b->
    Set(List(minusRows,RowIndices))=
        Set([Set([b,TensorC(b,"rho_3"),acMinus[1]]),
             Set([TensorC(b,"rho_{1-}"),TensorC(b,"rho_{3-}"),acMinus[1]])]) and
    ForAll(plusRows,r->RowIndices(r)=Set([TensorC(b,"rho_4"),acPlus[1]]))) then
    ErrorNoReturn("The [c] projective tensor products in (InterfaceMap) disagree with the interface map");
fi;
Print("All 16 anyon-map rows match (InterfaceMap), including [c]_{-i} times the G-irreps and the [ac]_{+-i}, [ac]_{++i} terms.\n");
# Reduced phase labels
reducedTh := TQDTheory(K,rec(a:=omegaII,N:=16,G:=K));;
ClassOnK := function(M,H,F)
    local matches;
    matches := Filtered([1..Length(M.classes)],i->ForAny(M.classes[i].algebras,A->ForAny(K,g->A[1]^g=H and A[2]^g=F)));
    if Length(matches)<>1 then ErrorNoReturn("Expected one algebra class on ",H,", ",F,", found ",matches); fi;
    return matches[1];
end;;
reducedClasses := AlgebraClasses(reducedTh);;
redLag1 := ClassOnK(reducedClasses,Group(m1),Group(m1));;
redLag2 := ClassOnK(reducedClasses,Group(m2),Group(m2));;
reducedHs := Hasse(reducedTh,reducedClasses);;
redElectric := ClassOnK(reducedClasses,TrivialSubgroup(K),TrivialSubgroup(K));;
electricPhases := PhaseLabels(reducedTh,redElectric,reducedHs);;
if [electricPhases[redLag1],electricPhases[redLag2]]<>["SSB","SSB"] then
    ErrorNoReturn("The two (Z2 x Z2)^omega_II phases are not partial SSB phases");
fi;
Print("(Z2 x Z2)^omega_II: P_<m1> and P_<m2> are partial SSB phases mapping to P_S3^(1) and P_S3^(2).\n");
reducedPhases := PhaseLabels(reducedTh,redLag1,reducedHs);;
if [reducedPhases[redLag1],reducedPhases[redLag2]]<>["SSB","SPT"] then
    ErrorNoReturn("The reduced Z4 phases are not SSB and trivial, respectively");
fi;
Print("Z4 SSB (L_<m1>) maps to twin full SSB 1 (L_S3^(1)); Z4 trivial (L_<m2>) maps to twin full SSB 2 (L_S3^(2)).\n");
Print("The results of the Twin Phases paper are confirmed.\n");
fi;
