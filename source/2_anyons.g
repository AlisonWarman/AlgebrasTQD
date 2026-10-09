#############################################################################
##
## source/2_anyons.g                  AlgebrasTQD
##
## Anyon labels, display helpers, and fusion rules.
##
## Functions in this file (the first line of each header):
## - ShowAlg: writes a multiplicity vector as a sum of labels
## - ShowChars: prints the character of an anyon on the centralizer of its flux
## - AbelianLabels: anyons of an abelian group in the magnetic/electric (m,e) labelling
## - Anyons: simple objects of the twisted Drinfeld double D^omega(G)
## - dima: quantum dimension of an anyon
## - AnyonLabelStrings: the anyon labels as strings, in the order of aG
## - AnyonPosition: the index of an anyon in aG, given by its label
## - ShowAnyons: prints one line per anyon: index, label, quantum dimension, topological spin
## - CustomAnyonLabels: asks for a new label for each anyon, showing its index, label, dimension, spin, boson test and characters
## - Fusion: the fusion product a x b of two anyons, from S by the Verlinde formula (no fusion array is stored)
## - ShowFusion: prints the fusion rules of a theory
##
#############################################################################

#ShowAlg: writes a multiplicity vector as a sum of labels
#in: na a vector of multiplicities, labin the matching list of label strings, or a list of anyons (written by AnyonLabelStrings)
#out: the string "n1 lab1+lab3+..." of its nonzero terms, e.g. "([1],1)+2([r],1)", or "0" for the zero vector
ShowAlg:=function(na,labin)
	local lab,terms,i;
	if Length(na)<>Length(labin) then
		ErrorNoReturn("ShowAlg: ",Length(na)," multiplicities for ",Length(labin)," labels");
	fi;
	if IsList(labin[1]) and Length(labin[1])>=2 and IsDictionary(labin[1][2]) then
		lab:=AnyonLabelStrings(labin);
	else
		lab:=List(labin,String);
	fi;
	terms:=[];
	for i in [1..Length(na)] do
		if na[i]=1 then
			Add(terms,lab[i]);
		elif na[i]<>0 then
			Add(terms,Concatenation(String(na[i]),lab[i]));
		fi;
	od;
	if terms=[] then return "0"; fi;
	return JoinStringsWithSeparator(terms,"+");
end;

#ShowChars: prints the character of an anyon on the centralizer of its flux
#in: a an anyon [g,character dictionary,class,label], ElG a group (its labels from MakeGroup or RelabelGroup are used), or its element list, or [elements,labels]
#out: prints the character on the centralizer of g, one line label=value per element, returns nothing
ShowChars:=function(a,ElG)
	local El,G,Ca,lab,gl,g;
	if IsGroup(ElG) then
		G:=ElG;
		lab:=MakeGroupLabels([G]);
		El:=lab[1]; lab:=lab[2];
	elif IsList(ElG) and Length(ElG)=2 and IsList(ElG[1]) and IsList(ElG[2]) then
		El:=ElG[1]; lab:=ElG[2]; #custom labels
		#the identity is not a generator (MakeGroupLabels would report it as a duplicate of 1)
		G:=Group(Filtered(El,g->not IsOne(g)),One(El[1]));
	elif IsList(ElG) then
		G:=Group(Filtered(ElG,g->not IsOne(g)),One(ElG[1]));
		lab:=MakeGroupLabels([G,ElG]);
		El:=lab[1]; lab:=lab[2];
	else
		ErrorNoReturn("ShowChars: give a group, its elements, or [elements,labels]");
	fi;
	Print("characters for ",AnyonLabelStrings([a])[1],"\n");
	gl:=function(h)
		return lab[Position(El,h)];
	end;
	Ca:=Centralizer(G,a[1]);
	for g in Ca do
		Print(gl(g),"=",LookupDictionary(a[2],g),"\n");
	od;
end;

#AbelianLabels: anyons of an abelian group in the magnetic/electric (m,e) labelling
#in: an abelian group G, or rec(G:=G,[gen:=independent generators],[opA:="*" for labels conjugate to the characters]); without gen the labelled generators a, b, ... of G stored by MakeGroup are used (MakeGroup(G) is called if G has none), so that m1, m2, ... are their fluxes; they must be independent
#out: [ElG,Elm,Ele,aG] with the elements of G, of its magnetic and electric copies, and aG the anyons [g,character dictionary,class,label]; a cyclic group has the flux m and the charge e, otherwise m1, m2, ... and e1, e2, ...
AbelianLabels:=function(inp)
	local
G,gen,opA,ords,names,copy,isomi,isoei,gem,gee,lm,le,ElG,Elm,Ele,g,gm,ge,k,chsM,dicts,dict,chs,e,l,Gch,hom,GG,pm,pe,em,ee,ElGG,aG,a,max,h,c,str,f1;
	if IsGroup(inp) then 
		G:=inp;
		opA:="";
	else
		G:=inp.G;
		if "gen" in RecNames(inp) then
			gen:=inp.gen;
			#keep the input group object: the classes of aG must belong to the user's G gen must be independent: it generates G and the product of the orders is |G|, so G is the direct product of the <g>
			if (IsEmpty(gen) and not IsTrivial(G)) or
			   (not IsEmpty(gen) and not (G=Group(gen) and Product(List(gen,Order))=Size(G))) then
				Print("#I  AbelianLabels: gen are not independent generators of G, the labelled generators of G are used instead\n");
				Unbind(gen);
			fi;
		fi;
		if "opA" in RecNames(inp) then
			opA:=inp.opA;
		else
			opA:="";
		fi;
	fi;
	if not IsAbelian(G) then ErrorNoReturn("AbelianLabels: G is not abelian"); fi;
	#the generators stored by MakeGroup: m1, m2, ... are their fluxes, in their order
	if not IsBound(gen) then
		#a group without labels is labelled by MakeGroup (a labelled group with the same elements)
		if HasGroupData(G) then gen:=GroupData(G).gens; else gen:=GroupData(MakeGroup(G)).gens; fi;
		if (IsEmpty(gen) and not IsTrivial(G)) or
		   (not IsEmpty(gen) and not (G=Group(gen) and Product(List(gen,Order))=Size(G))) then
			ErrorNoReturn("AbelianLabels: the labelled generators of G are not independent",
				" (their orders must multiply to |G|), so m1, m2, ... cannot follow them; relabel G, e.g. MakeGroup(\"C4 x C2\")");
		fi;
	fi;
	#the magnetic and electric copies of G: the abelian group presented on m1, m2, ... (e1, e2, ...) with the orders of gen and commuting generators, written down directly (no coset enumeration), named m, e for one generator; isomi, isoei map them to G by evaluating words (m_k -> gen[k])
	ords:=List(gen,Order);
	if Length(gen)=1 then
		names:=[["m"],["e"]];
	else
		names:=[List([1..Length(gen)],k->Concatenation("m",String(k))),List([1..Length(gen)],k->Concatenation("e",String(k)))];
	fi;
	copy:=function(nam)
		local F,x,rels,i,j;
		F:=FreeGroup(nam);
		x:=GeneratorsOfGroup(F);
		rels:=List([1..Length(x)],i->x[i]^ords[i]);
		for i in [1..Length(x)] do for j in [i+1..Length(x)] do Add(rels,Comm(x[i],x[j])); od; od;
		return F/rels;
	end;
	gem:=GeneratorsOfGroup(copy(names[1]));
	gee:=GeneratorsOfGroup(copy(names[2]));
	isomi:=GroupHomomorphismByImagesNC(Group(gem),G,gem,gen);
	isoei:=GroupHomomorphismByImagesNC(Group(gee),G,gee,gen);

	lm:=Cartesian(List([1..Length(gem)],k->List([0..ords[k]-1],j->gem[k]^j)));
	le:=Cartesian(List([1..Length(gee)],k->List([0..ords[k]-1],j->gee[k]^j)));

	ElG:=[];
	Elm:=[];
	Ele:=[];
	for k in [1..Length(lm)] do 
		gm:=Product(lm[k]);
		ge:=Product(le[k]);
		g:=isomi(gm);
		if not isoei(ge)=g then ErrorNoReturn("isoei(ge) not g"); fi;
		Add(ElG,g);
		Add(Elm,gm);
		Add(Ele,ge);
	od;
	chsM:=[];
	for e in gee do
		l:=List([1..Length(gen)],g->1);
		l[Position(gee,e)]:=E(ords[Position(gee,e)]);
		Add(chsM,DiagonalMat(l));
	od;
	Gch:=Group(chsM);
	hom:=GroupHomomorphismByImagesNC(Group(gee),Gch,gee,chsM);
	chs:=List(Elements(Image(hom)),x->DiagonalOfMatrix(x));
	max:=List(gen,x->Order(x)-1);
	dicts:=[];
	for h in chs do
		c:=List(gen,x->0);
		dict:=NewDictionary(false,true,G);
		AddDictionary(dict,One(G),Product(List([1..Length(gen)],n->h[n]^c[n])));
		while not c=max do
			c:=add1(c,max);
			AddDictionary(dict,Product(List([1..Length(gen)],n->gen[n]^c[n])), Product(List([1..Length(gen)],n->h[n]^c[n])));
		od;
		Add(dicts,dict);
	od;
	ElGG:=Cartesian(Elm,Ele);
	aG:=[];
	f1:=function(a)
		local a1,a2;
		if IsOne(a[1]) then a1:=1; else a1:=a[1]; fi;
		if IsOne(a[2]) then a2:=1; else a2:=a[2]; fi;
		return [a1,a2];
	end;
	for a in ElGG do
		if opA="*" then
			Add(aG,[isomi(a[1]),dicts[Position(chs,DiagonalOfMatrix(hom(a[2]^-1)))],isomi(a[1])^G,a]);
		else
			Add(aG,[isomi(a[1]),dicts[Position(chs,DiagonalOfMatrix(hom(a[2])))],isomi(a[1])^G,a]);
		fi;
	od;
	return [ElG,Elm,Ele,aG];
end;

#Anyons: simple objects of the twisted Drinfeld double D^omega(G)
#in: a group G, or rec(G:=G or [G,classes], om:=rec(a,N) a 3-cocycle, glG:=[elements,labels], gen:=independent generators of an abelian G (untwisted abelian path only, default the labelled generators of G), bos:=true for bosons only, opA:="data" for the modular data, opA:="*" for conjugate labels)
#out: the list of anyons [representative,character dictionary,class,label], or rec(aG,S,T) when opA="data" (S, T indexed like aG); with opA="*" the label of every anyon is the conjugate of its character data (untwisted abelian groups: in label order; otherwise in the order without "*")
Anyons:=function(inp)
	local G,ElG,labG,labPos,ccin,omega,N,val,exp,trivialOmega,opA,gen,bos,g1,g2,g3,x,vacd,objs,simp,cc,data,aba,
		gl,value,root,valueString,labelOf,separate,ce,Uce,Ugs,lab,aG,shortest;
	#--- the input: group, labels, cocycle and options, with their defaults
	ccin:=fail;
	labG:=fail;
	opA:="";
	bos:=false;
	if IsGroup(inp) then
		G:=inp;
		ElG:=Elements(G);
		labG:=MakeGroupLabels([G,ElG])[2];
	elif IsRecord(inp) then
		if not IsBound(inp.G) then ErrorNoReturn("Anyons: record input requires G"); fi;
		if IsGroup(inp.G) then G:=inp.G; else G:=inp.G[1]; ccin:=inp.G[2]; fi;
		if IsBound(inp.glG) then
			ElG:=inp.glG[1];
			if Length(inp.glG[2])=Length(ElG) then labG:=inp.glG[2]; else labG:=MakeGroupLabels([G,ElG])[2]; fi;
		else
			ElG:=Elements(G);
			labG:=MakeGroupLabels([G,ElG])[2];
		fi;
		if IsBound(inp.opA) then opA:=inp.opA; fi;
		if IsBound(inp.gen) then gen:=inp.gen; fi;
		if IsBound(inp.bos) then
			if not IsBool(inp.bos) then ErrorNoReturn("Anyons: bos must be true or false"); fi;
			bos:=inp.bos;
		fi;
	else
		ErrorNoReturn("Anyons: give a group or a record rec(G:=...)");
	fi;
	#the cocycle: val = gcd of its values and N, exp = N/val; the loop stops once val=1 and a nonzero value is seen
	if IsRecord(inp) and IsBound(inp.om) then
		N:=inp.om.N;
		omega:=function(g1,g2,g3) return inp.om.a(g1,g2,g3); end;
		val:=N;
		trivialOmega:=true;
		for g1 in ElG do
			for g2 in ElG do
				for g3 in ElG do
					x:=omega(g1,g2,g3);
					if x<>0 then trivialOmega:=false; fi;
					val:=Gcd(val,x);
					if val=1 and not trivialOmega then break; fi;
				od;
				if val=1 and not trivialOmega then break; fi;
			od;
			if val=1 and not trivialOmega then break; fi;
		od;
		exp:=N/val;
	else
		omega:=function(g1,g2,g3) return 0; end;
		trivialOmega:=true;
		val:=1;
		exp:=1;
	fi;

	#--- the trivial group: the vacuum is the only anyon, with S = T = (1)
	if IsTrivial(G) then
		vacd:=NewDictionary(One(G),true,G);
		AddDictionary(vacd,One(G),1);
		aG:=[[One(G),vacd,ConjugacyClass(G,One(G)),"1"]];
		if opA="data" then return rec(aG:=aG,S:=[[1]],T:=[[1]]); fi;
		return aG;
	fi;

	#--- untwisted abelian groups: the (m,e) labels of AbelianLabels, m1, m2, ... the fluxes of the labelled generators, and S, T by their closed formulas for a = (g,chi), b = (h,psi) (no simple objects of Gruen-Morrison needed): S_ab = conj(chi(h) psi(g))/|G|, T_aa = chi(g); with opA="*" the stored characters are already conjugated
	if IsAbelian(G) and trivialOmega and not bos then
		if IsBound(gen) then aba:=AbelianLabels(rec(G:=G,opA:=opA,gen:=gen)); else aba:=AbelianLabels(rec(G:=G,opA:=opA)); fi;
		aG:=aba[4];
		if opA<>"data" then return aG; fi;
		return rec(aG:=aG,
			S:=List(aG,a->List(aG,b->ComplexConjugate(LookupDictionary(a[2],b[1])*LookupDictionary(b[2],a[1]))/Size(G))),
			T:=DiagonalMat(List(aG,a->LookupDictionary(a[2],a[1]))));
	fi;

	#--- the simple objects (Gruen-Morrison), optionally only the bosons (chi(g)>0 rational), and the modular data
	#Convention: GenerateSimpleObjects (source/00) labels the simple objects by theta_x-projective representations of C_G(x), theta_x the Gruen-Morrison 2-cocycle; GM call this category Z(Vec_G^{omega^{-1}}), TwinAlgebras.tex calls it Z(Vec_G^omega) and labels it by omega(.,.|x)^{-1}-projective representations, and omega(x,y|a)=1/theta_a(x,y) on C_G(a). Both labellings coincide, so the anyons below are those of Z(Vec_G^omega) in the paper's naming.
	#shortest: the position in ElG of the element of a class with the shortest label (the first in ElG on ties). It gives the default classes (GAP's class order) and the centralizer elements of the labels below, so that the labels do not depend on the representatives GAP happens to choose (they change with earlier computations)
	labPos:=NewDictionary(ElG[1],true,G);
	for x in [1..Length(ElG)] do AddDictionary(labPos,ElG[x],x); od;
	shortest:=function(c)
		local pos;
		pos:=List(Elements(c),e->LookupDictionary(labPos,e));
		SortBy(pos,i->[Length(labG[i]),i]);
		return pos[1];
	end;
	if ccin=fail then ccin:=List(ConjugacyClasses(G),c->ElG[shortest(c)]); fi;
	objs:=GenerateSimpleObjects([G,ccin],omega,val,exp);
	simp:=objs.Simp;
	if bos then
		simp:=Filtered(simp,t->IsRat(LookupDictionary(t.character,t.representative)) and
			LookupDictionary(t.character,t.representative)>0);
	fi;
	cc:=List(simp,t->ConjugacyClass(G,t.representative));
	if opA="data" then data:=GenerateModularData(G,omega,val,exp,simp); fi;

	#--- the labels ([g],chi(g) k=chi(k) ...) of all other theories
	#gl: the label of a group element (looked up in a dictionary), or as GAP prints it
	if labG<>fail then
		labPos:=NewDictionary(ElG[1],true,G);
		for x in [1..Length(ElG)] do AddDictionary(labPos,ElG[x],x); od;
		gl:=h->labG[LookupDictionary(labPos,h)];
	else
		gl:=h->String(h);
	fi;
	#value: the character value of ch at k, conjugated for opA="*"
	value:=function(ch,k)
		if opA="*" then return ComplexConjugate(LookupDictionary(ch,k)); fi;
		return LookupDictionary(ch,k);
	end;
	#root: a root of unity written E(n) or E(n)^m
	root:=function(v)
		local r;
		r:=DescriptionOfRootOfUnity(v);
		if r[2]=1 then return Concatenation("E(",String(r[1]),")"); fi;
		return Concatenation("E(",String(r[1]),")^",String(r[2]));
	end;
	#valueString: " k=value" (a root of unity of a one-dimensional character written E(n)^m)
	valueString:=function(ch,k)
		local v;
		v:=value(ch,k);
		if LookupDictionary(ch,One(G))=1 and not IsRat(v) then return Concatenation(" ",gl(k),"=",root(v)); fi;
		return Concatenation(" ",gl(k),"=",String(v));
	end;
	#labelOf: the label of the simple object simp[n], without the closing bracket: the flux class, chi(g), and the values on the class representatives of the centralizer that are not in the subgroup generated so far (a one-dimensional
	#character: a root of unity or -1; otherwise a value other than chi(1) and 0)
	labelOf:=function(n)
		local g,ch,s,v,H,k;
		g:=simp[n].representative;
		ch:=simp[n].character;
		if g=One(G) then s:="([1],"; else s:=Concatenation("([",gl(g),"],"); fi;
		v:=value(ch,g);
		if LookupDictionary(ch,One(G))=1 and not IsRat(v) then Append(s,root(v)); else Append(s,String(v)); fi;
		H:=Group([g,One(G)]);
		for k in Ugs[Position(Uce,ce[n])] do
			if not k in H then
				H:=ClosureGroup(H,k);
				v:=value(ch,k);
				if LookupDictionary(ch,One(G))=1 then
					if not IsRat(v) or v=-1 then Append(s,valueString(ch,k)); fi;
				elif not (v=LookupDictionary(ch,One(G)) or v=0) then
					Append(s,valueString(ch,k));
				fi;
			fi;
		od;
		return s;
	end;
	#separate: makes equal labels distinct. First, for every set of anyons with the same label, each gets the values at the centralizer elements where its character differs from all the others (or, if there are none, from each of them); then, while two labels are still equal, every anyon of that set gets its value at the first element of the centralizer where the characters of the set are not all equal (two simple objects with the same flux have different characters, so this ends)
	separate:=function(lab)
		local l,pos,Cg,chs,n,ch,post,diff,gs,once,s,k,i,kk;
		for l in Set(lab) do
			pos:=Positions(lab,l);
			if Length(pos)>1 then
				Cg:=Elements(Centralizer(G,simp[pos[1]].representative));
				#chs[1][1] below is the dimension chi(1), so the identity must come first
				if Order(Cg[1])<>1 then Cg:=Concatenation([One(G)],Filtered(Cg,k->not IsOne(k))); fi;
				chs:=List(pos,p->List(Cg,k->LookupDictionary(simp[p].character,k)));
				for n in pos do
					ch:=simp[n].character;
					post:=Filtered(pos,p->p<>n);
					diff:=List(post,c->chs[Position(pos,n)]-chs[Position(pos,c)]);
					gs:=List(PosNonZero(List(TransposedMat(diff),d->Product(d))),k->Cg[k]);
					once:=true;
					if gs=[] then once:=false; gs:=List(Set(List(diff,d->PosNonZero(d)[1])),k->Cg[k]); fi;
					s:=lab[n];
					for k in gs do
						i:=Position(Cg,k);
						if not (chs[Position(pos,n)][i]=0 or chs[Position(pos,n)][i]=chs[1][1]) then
							Append(s,valueString(ch,k));
							if once then break; fi;
						fi;
					od;
					lab[n]:=s;
				od;
			fi;
		od;
		#still equal: the first centralizer element where the characters differ
		while Length(Set(lab))<Length(lab) do
			for l in Set(lab) do
				pos:=Positions(lab,l);
				if Length(pos)>1 then
					Cg:=Elements(Centralizer(G,simp[pos[1]].representative));
					kk:=First(Cg,k->Length(Set(pos,p->LookupDictionary(simp[p].character,k)))>1);
					if kk=fail then ErrorNoReturn("Anyons: two simple objects have the same flux and character"); fi;
					for n in pos do lab[n]:=Concatenation(lab[n],valueString(simp[n].character,kk)); od;
				fi;
			od;
		od;
		return lab;
	end;
	#one element per class of each distinct centralizer (one group object per centralizer, as in the labels so far): the one with the shortest label, in the order of label length, then position in ElG
	ce:=List(cc,Centralizer);
	Uce:=Set(ce);
	Ugs:=List(Uce,function(C)
		local pos;
		pos:=List(ConjugacyClasses(C),shortest);
		SortBy(pos,i->[Length(labG[i]),i]);
		return ElG{pos};
	end);
	lab:=separate(List([1..Length(simp)],labelOf));
	aG:=List([1..Length(simp)],n->[simp[n].representative,simp[n].character,cc[n],Concatenation(lab[n],")")]);
	if opA="data" then return rec(aG:=aG,S:=data.S,T:=data.T); fi;
	return aG;
end;

#dima: quantum dimension of an anyon
#in: a an anyon [g,character dictionary,class,label], one the identity of the group
#out: its quantum dimension chi(1)*|class| as a cyclotomic
dima:=function(a,one)
	return LookupDictionary(a[2],one)*Size(a[3]);
end;

#AnyonLabelStrings: the anyon labels as strings, in the order of aG
#in: aG a list of anyons as returned by Anyons (labels strings ([g],R), or [m,e] pairs on the abelian path)
#out: the list of label strings: ([g],R) labels as they are, the vacuum ([1],1); an abelian label joins flux and charge without trivial parts, e.g. "m1e2", "m2", "e1^2" (m, e for a cyclic group, as named by AbelianLabels), the vacuum 1
AnyonLabelStrings:=function(aG)
	local lab;
	lab:=List(aG,function(a)
		local parts;
		if IsString(a[4]) then return a[4]; fi;
		parts:=Filtered(a[4],g->not IsOne(g));
		if parts=[] then return "1"; fi;
		return JoinStringsWithSeparator(List(parts,String),"");
	end);
	return lab;
end;

#AnyonPosition: the index of an anyon in aG, given by its label
#in: aG a list of anyons (or a record with a field aG, e.g. from TQDTheory) and lab a label string as printed by AnyonLabelStrings
#out: the index of the anyon in aG, or fail
AnyonPosition:=function(aG,lab)
	if IsRecord(aG) then aG:=aG.aG; fi;
	return Position(AnyonLabelStrings(aG),lab);
end;

#ShowAnyons: prints one line per anyon: index, label, quantum dimension, topological spin
#in: a record with fields G and aG (e.g. TQDTheory(...)), optionally labels
#out: prints the table, the spin theta=chi(g)/chi(1) read off the character at the flux g, returns nothing
ShowAnyons:=function(th)
	local lab,n,a;
	if IsBound(th.labels) then lab:=th.labels; else lab:=AnyonLabelStrings(th.aG); fi;
	for n in [1..Length(th.aG)] do
		a:=th.aG[n];
		Print(n,"\t",lab[n],"\t\td=",dima(a,One(th.G)),"\t\ttheta=",
			LookupDictionary(a[2],a[1])/LookupDictionary(a[2],One(th.G)),"\n");
	od;
end;

#CustomAnyonLabels: asks for a new label for each anyon, showing its index, label, dimension, spin, boson test and characters
#in: (th[,opts]) with th a record from TQDTheory; opts optional bosons:=true (only the bosons), chars:=false (no characters), input:=list of answers (instead of the keyboard); Enter keeps a label, "q" keeps all remaining, a used label is refused
#out: the list of labels, indexed like th.aG (use th.labels:=CustomAnyonLabels(th))
CustomAnyonLabels:=function(arg)
	local th,opts,lab,n,a,g,spin,isbos,ans,stream,answers,next,El,stop;
	th:=arg[1];
	if Length(arg)>1 then opts:=arg[2]; else opts:=rec(); fi;
	if not (IsRecord(th) and IsBound(th.G) and IsBound(th.aG)) then
		ErrorNoReturn("CustomAnyonLabels: give a record with fields G and aG, e.g. TQDTheory(G)");
	fi;
	if IsBound(th.labels) then lab:=ShallowCopy(th.labels); else lab:=AnyonLabelStrings(th.aG); fi;
	if IsBound(th.glG) then El:=th.glG{[1,2]}; else El:=th.G; fi;
	if IsBound(opts.input) then
		answers:=ShallowCopy(opts.input);
		next:=function()
			if answers=[] then return "q"; fi;
			return Remove(answers,1);
		end;
	else
		stream:=InputTextUser();
		next:=function()
			local line;
			line:=ReadLine(stream);
			if line=fail then return "q"; fi;
			return Filtered(line,c->not c in "\n\r");
		end;
	fi;
	stop:=false;
	for n in [1..Length(th.aG)] do
		a:=th.aG[n];
		g:=a[1];
		#topological spin from the character at the flux; boson iff spin 1
		spin:=LookupDictionary(a[2],g)/LookupDictionary(a[2],One(th.G));
		isbos:=spin=1;
		if stop or (IsBound(opts.bosons) and opts.bosons=true and not isbos) then continue; fi;
		Print("\n",n,"\t",lab[n],"\t\td=",dima(a,One(th.G)),"\t\ttheta=",spin,"\tboson: ",isbos,"\n");
		if not (IsBound(opts.chars) and opts.chars=false) then ShowChars(a,El); fi;
		repeat
			Print("new label for ",lab[n]," (Enter: keep, q: keep all remaining): ");
			ans:=next();
			if not IsBound(opts.input) then Print("\n"); else Print(ans,"\n"); fi;
			#"q" ends the loop even when q is a current label (with opts.input, next() returns "q" once the answers run out)
			if ans<>"q" and ans in lab and ans<>lab[n] then Print("label ",ans," is already used, choose another\n"); fi;
		until ans="q" or not (ans in lab and ans<>lab[n]);
		if ans="q" then
			stop:=true;
		elif ans<>"" then
			lab[n]:=ans;
		fi;
	od;
	return lab;
end;

#Fusion: the fusion product a x b of two anyons, from S by the Verlinde formula (no fusion array is stored)
#in: (th,a,b) with th a record from TQDTheory(G,v,rec(ST:=true)), a and b anyons given by their labels (th.labels) or indices
#out: the decomposition of a x b as a string of labels, e.g. "1+([1],2 r=-1)+([r],1)"; N_ab^c = sum_x S_ax S_bx conj(S_cx)/S_0x
Fusion:=function(th,a,b)
	local S,n,i,j,v,mult,pos;
	if not (IsRecord(th) and IsBound(th.S) and IsBound(th.labels)) then
		ErrorNoReturn("Fusion: the theory has no S matrix; build it with TQDTheory(G,v,rec(ST:=true))");
	fi;
	S:=th.S;
	n:=Length(S);
	pos:=function(x)
		local k;
		if IsPosInt(x) and x<=n then return x; fi;
		k:=Position(th.labels,x);
		if k=fail then ErrorNoReturn("Fusion: ",x," is not an anyon label of the theory (see th.labels)"); fi;
		return k;
	end;
	i:=pos(a);
	j:=pos(b);
	#one row of the Verlinde formula: v_x = S_ix S_jx / S_0x, then N_ij^c = sum_x v_x conj(S_cx)
	v:=List([1..n],x->S[i][x]*S[j][x]/S[1][x]);
	mult:=List([1..n],c->Sum([1..n],x->v[x]*ComplexConjugate(S[c][x])));
	if not ForAll(mult,m->IsInt(m) and m>=0) then
		ErrorNoReturn("Fusion: the Verlinde formula gives non-integer multiplicities, S is not a modular S matrix");
	fi;
	return ShowAlg(mult,th.labels);
end;

#ShowFusion: prints the fusion rules of a theory
#in: (th[,keep]) with th a record from TQDTheory(G,v,rec(ST:=true)), keep an optional list of anyon labels to print
#out: prints a x b = ... for the pairs of non-vacuum anyons (in keep), computed one by one with Fusion, returns nothing
ShowFusion:=function(arg)
	local th,lab,ks,i,j;
	th:=arg[1];
	if not (IsRecord(th) and IsBound(th.S) and IsBound(th.labels)) then
		ErrorNoReturn("ShowFusion: the theory has no S matrix; build it with TQDTheory(G,v,rec(ST:=true))");
	fi;
	lab:=th.labels;
	ks:=[2..Length(lab)];
	if Length(arg)>1 then ks:=Filtered(ks,k->lab[k] in arg[2]); fi;
	for i in ks do
		for j in Filtered(ks,j->j>=i) do
			Print(lab[i]," x ",lab[j]," = ",Fusion(th,i,j),"\n");
		od;
	od;
end;
