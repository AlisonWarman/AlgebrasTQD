#############################################################################
##
## source/6_algebra_classes_and_inclusions.g AlgebrasTQD
##
## Algebra classes, inclusions, Hasse diagrams, phase labels, order-parameter algebras and topological sectors.
##
## Functions in this file (the first line of each header):
## - AlgebraClassesG: sorts the algebras of a theory into algebra classes and finds the twin pairs
## - IsSubalgebra: tests whether one algebra includes into a strictly larger one
## - HasseDataG: builds the Hasse diagram of inclusions between algebra classes
## - HassePhases: names the gapped phase of each algebra from the Hasse diagram
## - OperatorAlgebra: the algebra of order parameters of an algebra of a theory, as an explicit ordered-basis model
## - TopologicalSectors: the topological sectors of the gapped boundary of a Lagrangian algebra
## - AlgebraClasses: the algebra classes and twin pairs of a theory, each class with its anyon decomposition
## - Hasse: the Hasse diagram of inclusions between the algebra classes of a theory
## - DisplayClasses: the classes shown by AlgebraTableTeX and HasseTikz, in display order
## - TeXOutput: returns a LaTeX string, after writing it to opts.file when that is given
## - AlgebraTableTeX: the table of algebras of a theory in the layout of TwinAlgebras.tex (Table tab:G_om)
## - TwinTableTeX: the table of twin algebras of a theory in the layout of TwinAlgebras.tex (Table tab:twinsG32-43)
## - HasseTikz: the Hasse diagram of a theory as a tikz picture in the layout of TwinAlgebras.tex (Figure fig:Hasse3243_om)
## - HasseTableTeX: the linked Hasse diagram and algebra table from one class selection
## - HasseEntryTeX: the LaTeX entry of one algebra of a Hasse diagram, as in the table of AlgebraTableTeX
## - PhaseLabels: the gapped-phase name of every algebra class, relative to a chosen symmetry boundary
##
#############################################################################

#AlgebraClassesG: sorts the algebras of a theory into algebra classes and finds the twin pairs
#in: rec(G:=G, [om:=rec(a,N)], [aG:=anyons], [glG:=[elements,labels]], [HFtot:=subgroup pairs], op:=""/"equiv"/"twins"), and with HFtot only the algebras on those pairs are classified
#out: for op="" [classes as algebras,twin pairs,reasons,anyon vectors] with twin pairs and reasons by class index and the anyon vector of the first algebra of each class, for op="twins" [[twin algebras,reasons],aG,glG], for op="equiv" [classes as algebras,equivalence data of equivalent pairs,reasons for inequivalent pairs] (pairs as indices into AlgebraData)
AlgebraClassesG:=function(data)
	local op,G,Uom,om,aG,CAG,glG,gl,f,g,h,gammaok,As,A,nA,poss,p,A1,A2,Om,Omg,gamma,f1,f2,F,ElF,t,v,sol,c,eps,chtabF,clF,chF,irr,classes,equivclasses,twins,equiv,reason,reasonseq,reasonsineq,ps,l,twinsrepr,ntoclass,n,toret;
	G:=data.G;
	if "om" in RecNames(data) then
		om:=data.om;
		Uom:="not nec 1";
	else
		om:=rec(a:=function(f,g,h) return 0; end,N:=1);
		Uom:=[1];
	fi;
	if "op" in RecNames(data) then
		op:=data.op;
	else
		op:="";
	fi;
	if "aG" in RecNames(data) then
		aG:=data.aG;
	else
		aG:=Anyons(data);
	fi;
	#op selects the output of this function, not a subgroup filter of AlgSubgroups
	if "HFtot" in RecNames(data) then
		CAG:=AlgebraData(rec(G:=G,om:=om,HFtot:=data.HFtot));
	else
		CAG:=AlgebraData(rec(G:=G,om:=om));
	fi;

	if "glG" in RecNames(data) then 
		glG:=data.glG;
	else
		glG:=MakeGroupLabels([G]);
	fi; 
	gl:=function(g)
		return glG[2][Position(glG[1],g)];
	end;

	As:=[];
	for A in CAG do 
		Add(As,AlgAnyonsV([A,aG,om]));
	od;

	classes:=[];
	poss:=[]; 
	for nA in As do
		p:=Positions(As,nA);
		if Length(p)=1 then Add(classes,p);
		elif Length(p)=2 then Add(poss,p);
		elif Length(p)>2 then poss:=Concatenation(poss,Combinations(p,2));
		fi;
	od;
	poss:=Union([poss]);

	if not Uom=[1] then
		Om:=function(f,g,h)
			return 3cocl(function(f,g,h) return E(om.N)^om.a(f,g,h); end, f,g,h);
		end;
	fi;

	equiv:=[];
	reasonseq:=[];
	twins:=[];
	reasonsineq:=[];
	for p in poss do
		t:=false;
		reason:="";
		A1:=CAG[p[1]];
		A2:=CAG[p[2]];
		F:=A1[2];
		ElF:=Elements(F);
		if not IsConjugate(G,A2[1],A1[1])  then t:=false; reason:="H'\\neq{}^g\\!H"; 
		elif not IsConjugate(G,A2[2],A1[2])  then t:=false; reason:="N'\\neq{}^g\\!N";
		#H and N can each be conjugate to H' and N' with no single g mapping (H,N) to (H',N')
		elif ForAll(Elements(G),g->not (A2[1]=A1[1]^g and A2[2]=A1[2]^g)) then t:=false; reason:="(H',N')\\neq{}^g\\!(H,N)";
		else
		#the linear characters of F, which give every gauge c*chi with chi linear, once per pair
		chtabF:=CharacterTable(F);
		clF:=ConjugacyClasses(chtabF);
		chF:=LinearCharacters(chtabF);
		#gammaok: some g with ^g(H,N)=(H',N') solves the gamma equation
		gammaok:=false;
		for g in Elements(G) do
			if (A2[1]=A1[1]^g and A2[2]=A1[2]^g) then
				#gamma is the ratio of gammas with Om that need g^-1 because for gap ^g means g^-1...g
				if Uom=[1] then
					gamma:=function(f1,f2) return (A2[3](f1^g,f2^g)/A1[3](f1,f2)); end;
				else
					gamma:=function(f1,f2) return (A2[3](f1^g,f2^g)/A1[3](f1,f2))*Om(g^-1,f1,f2); end;
				fi;
				sol:=IsTrivial2coc([ElF,gamma]);
				if sol=fail then 
					t:=false; 
				else
					gammaok:=true;
					c:=sol;
					#eps is the ratio of epsilons with Om and c here f1 in H and f2 in ElF
					if Uom=[1] then
						eps:=function(h,f)
							return (A2[4](h^g,f^g)/A1[4](h,f))*(c[Position(ElF,f)]/c[Position(ElF,h*f*Inverse(h))]);
						end;
					else
						eps:=function(h,f)
							return (A2[4](h^g,f^g)/A1[4](h,f))*(Om(g^-1,h,f)/Om(g^-1,h*f*Inverse(h),h))*(c[Position(ElF,f)]/c[Position(ElF,h*f*Inverse(h))]);
						end;
					fi;
					#now test if eps is equiv to trivial by F-irreps
					for irr in chF do
						t:=true;
						for h in A1[1] do
							for f in ElF do
								t:=(eps(h,f)=(irr[Posinlist(clF,h*f*Inverse(h))]/irr[Posinlist(clF,f)]));
								if t=false then break; fi;
							od;
							if t=false then break; fi;
						od;
						if t=true then break; fi;
					od;
					if t=true then 
						#reasons has p (two pos that are equivalent), g^-1 (aka g in file), F (=N) and irr (=c), Omg	
						Add(equiv,p);
						if Uom=[1] then Add(reasonseq,[p,gl(g^-1),List(ElF,k->gl(k)),List(irr,r->r)]);
						else
							Omg:=[];
							for h in A1[1] do
								for f in ElF do
									if not Om(g^-1,h,f)=1 then Add(Omg,[[gl(h),gl(f)],Om(g^-1,h,f)]); fi;
								od;
							od;
							Add(reasonseq,[p,gl(g^-1),List(ElF,k->gl(k)),List(irr,r->r),Omg]);
						fi;
					fi;
					if t=true then break; fi;
				fi;
			fi;
		od;
		#no g gives an isomorphism: the eps reason if the gamma equation is solvable for some g, the gamma reason if for none
		if t=false then
			if gammaok then
				if Uom=[1] then reason:="\\eps^{\\prime g}\\neq\\eps";
				else reason:="\\epsilon^{\\prime g} \\Omega_g \\neq \\Omega_g'\\epsilon";
				fi;
			else
				if Uom=[1] then reason:="\\gamma^{\\prime g}\\neq\\gamma";
				else reason:="\\gamma^{\\prime g} \\Omega_g \\neq \\gamma";
				fi;
			fi;
		fi;
		fi;
		if t=false then 
			Add(twins,p);
			Add(reasonsineq,[p,reason]);
		fi;
	od;

	#create equivclasses
	equivclasses:=[];
	for p in equiv do
		if not p[1] in Union(equivclasses) then
			if not p[2] in Union(equivclasses) then
				ps:=Union([Concatenation(Union(List(Possinlist(equiv,p[1]),x->equiv[x])),Union(List(Possinlist(equiv,p[2]),x->equiv[x])))]);
				Add(equivclasses,ps);
			else
				if not Length(Possinlist(equivclasses,p[2]))=1 then ErrorNoReturn("error in equivclasses"); 
				else equivclasses[Posinlist(equivclasses,p[2])]:=Union([Concatenation(equivclasses[Posinlist(equivclasses,p[2])],Concatenation(Union(List(Possinlist(equiv,p[1]),x->equiv[x])),Union(List(Possinlist(equiv,p[2]),x->equiv[x]))))]);
				fi;
			fi;
		else
			if not Length(Possinlist(equivclasses,p[1]))=1 then ErrorNoReturn("error in equivclasses"); 
			else
equivclasses[Posinlist(equivclasses,p[1])]:=Union([Concatenation(equivclasses[Posinlist(equivclasses,p[1])],Concatenation(Union(List(Possinlist(equiv,p[1]),x->equiv[x])),Union(List(Possinlist(equiv,p[2]),x->equiv[x]))))]);
			fi;
		fi;
	od;
	if not Union(equiv)=Union(equivclasses) then ErrorNoReturn("error in equiv vs equiclasses"); fi;

	#twins are inequivalent algebras so each p[1] and p[2] should go in different classes unless they are equivalent to other algs
	for p in twins do
		if not p[1] in Union(equivclasses) then
			Add(equivclasses,[p[1]]);
		fi; 
		if not p[2] in Union(equivclasses) then
			Add(equivclasses,[p[2]]);
		fi; 
	od;
	classes:=Concatenation(classes,equivclasses);
	Sort(classes);
	l:=Flat(classes);
	Sort(l);
	if l<>[1..Length(CAG)] then
		ErrorNoReturn("AlgebraClassesG: classes are not a partition");
	fi;

	#op="equiv" returns the classes as algebras, then the equivalence data of the equivalent pairs and the reasons of the inequivalent ones (indices into CAG)
	if op="equiv" then
		return [List(classes,c->List(c,x->CAG[x])),reasonseq,reasonsineq];
	fi;
	#op="twins" returns only twin algebras with reasons to print table and data
	if op in ["twins",""] then 
		ntoclass:=function(n)
			return classes[Posinlist(classes,n)];
		end;
		#each class pair is sorted before the union: algebra pairs (i,j) and (k,l) of interleaved classes can give [C1,C2] and [C2,C1]
		twins:=Set(List(twins,x->Set([ntoclass(x[1]),ntoclass(x[2])])));
		twinsrepr:=[];
			for p in twins do
			v:=[p[1][1],p[2][1]];
			Sort(v);
			Add(twinsrepr,v);
			od;
		toret:=[List(twinsrepr,c->List(c,x->CAG[x])),List(List(twinsrepr,c->Position(List(reasonsineq,x->x[1]),c)),y->reasonsineq[y][2])];
		if op="twins" then return [toret,aG,glG]; fi;
		#op="" return algebra classes with no reasons (e.g. for IsSubalgebra)
		if op="" then return [List(classes,c->List(c,x->CAG[x])),List(twinsrepr,x->[Posinlist(classes,x[1]),Posinlist(classes,x[2])]),DuplicateFreeList(List(reasonsineq,x->[[Posinlist(classes,x[1][1]),Posinlist(classes,x[1][2])],x[2]])),List(classes,c->Last(As[c[1]]))]; fi;
	fi;
end;


#IsSubalgebra: tests whether one algebra includes into a strictly larger one
#in: rec(A1:=A1, A2:=A2, [om:=om], [na1:=na(A1), na2:=na(A2)])
#out: [Elements(F1),c,g2] or a reason string; c relates A1 to transported A2.
#A failed conjugator reduction check raises an error.
IsSubalgebra:=function(inp)
	local lg,A1,A2,om,Om,makeFData,inclusiondata,H1in,H2in,F1in,F2in,g1,g2,g,gamma1in,gamma2in,eps1in,eps2in,G1,G2,G,d1,d2,relative,identityFData,FData,sol,reduced;
	if not (IsRecord(inp) and IsBound(inp.A1) and IsBound(inp.A2)) then
		ErrorNoReturn("IsSubalgebra: the input must be rec(A1:=A1, A2:=A2, [om:=om], [na1:=na(A1), na2:=na(A2)])");
	fi;
	A2:=inp.A2;
	A1:=inp.A1;
	if IsBound(inp.om) then
		om:=inp.om;
		Om:=function(f,g,h)
			return 3cocl(function(f,g,h) return E(om.N)^om.a(f,g,h); end, f,g,h);
		end;
	fi;
	H1in:=A1[1];
	H2in:=A2[1];
	F1in:=A1[2];
	F2in:=A2[2];
	gamma1in:=A1[3];
	gamma2in:=A2[3];
	eps1in:=A1[4];
	eps2in:=A2[4];
	G1:=A1[5];
	G2:=A2[5];
	if not G1=G2 then ErrorNoReturn("G1 not G2"); fi;
	G:=G1;
	d1:=Order(G1)*Order(F1in)/Order(H1in);
	d2:=Order(G2)*Order(F2in)/Order(H2in);
	if d1>=d2 then return "false dims"; fi;
	#a subalgebra is a subobject: na(A1)<=na(A2) for every anyon
	if IsBound(inp.na1) and IsBound(inp.na2) and ForAny([1..Length(inp.na1)],a->inp.na1[a]>inp.na2[a]) then
		return "false anyons";
	fi;
	if Order(H1in) mod Order(H2in)<>0 or Order(F2in) mod Order(F1in)<>0 then
		return "false subgroups";
	fi;
	#Subgroup conditions depend only on g=g1^-1*g2.
	relative:=Filtered(Elements(G),g->IsSubset(H1in,H2in^(g^-1)) and IsSubset(F2in^(g^-1),F1in));
	if relative=[] then return "false subgroups"; fi;
	lg:=function(z) local d; d:=DescriptionOfRootOfUnity(z); return d[2]/d[1]; end;
	makeFData:=function(gg1)
		local ElF,posF,i;
		ElF:=Elements(F1in^(gg1^-1));
		posF:=NewDictionary(ElF[1],true);
		for i in [1..Length(ElF)] do AddDictionary(posF,ElF[i],i); od;
		return [ElF,posF];
	end;
	#Solve both gauge equations on F1^(g1^-1).
	inclusiondata:=function(gg1,gg2,fdata)
		local gamma1,gamma2,eps1,eps2,ElF,posF,ElH,rows,rhs,row,f1,f2,x,n,sol;
		ElF:=fdata[1]; posF:=fdata[2];
		if not IsBound(om) then
				gamma1:=function(ff1,ff2) return gamma1in(ff1^gg1,ff2^gg1); end;
				gamma2:=function(ff1,ff2) return gamma2in(ff1^gg2,ff2^gg2); end;
				eps1:=function(hh,ff) return eps1in(hh^gg1,ff^gg1); end;
				eps2:=function(hh,ff) return eps2in(hh^gg2,ff^gg2); end;
			else
				gamma1:=function(ff1,ff2) return gamma1in(ff1^gg1,ff2^gg1)/Om(gg1,ff1^gg1,ff2^gg1); end;
				gamma2:=function(ff1,ff2) return gamma2in(ff1^gg2,ff2^gg2)/Om(gg2,ff1^gg2,ff2^gg2); end;
				eps1:=function(hh,ff) return eps1in(hh^gg1,ff^gg1)*Om(gg1,(hh*ff*hh^-1)^gg1,hh^gg1)/Om(gg1,hh^gg1,ff^gg1); end;
				eps2:=function(hh,ff) return eps2in(hh^gg2,ff^gg2)*Om(gg2,(hh*ff*hh^-1)^gg2,hh^gg2)/Om(gg2,hh^gg2,ff^gg2); end;
		fi;
		ElH:=Elements(H2in^(gg2^-1));
		rows:=[]; rhs:=[];
		for f1 in ElF do for f2 in ElF do
			row:=ListWithIdenticalEntries(Length(ElF),0);
			row[LookupDictionary(posF,f1*f2)]:=row[LookupDictionary(posF,f1*f2)]+1;
			row[LookupDictionary(posF,f1)]:=row[LookupDictionary(posF,f1)]-1;
			row[LookupDictionary(posF,f2)]:=row[LookupDictionary(posF,f2)]-1;
			Add(rows,row); Add(rhs,lg(gamma2(f1,f2)/gamma1(f1,f2)));
		od; od;
		for x in ElH do for n in ElF do
			row:=ListWithIdenticalEntries(Length(ElF),0);
			row[LookupDictionary(posF,x*n*x^-1)]:=row[LookupDictionary(posF,x*n*x^-1)]+1;
			row[LookupDictionary(posF,n)]:=row[LookupDictionary(posF,n)]-1;
			Add(rows,row); Add(rhs,lg(eps2(x,n)/eps1(x,n)));
		od; od;
		sol:=SolveModZ(rows,rhs,Lcm(List(rhs,DenominatorRat)));
		if sol=fail then return fail; fi;
		return [ElF,List(sol,q->E(DenominatorRat(q))^NumeratorRat(q))];
	end;
	#Try g1=1 first and retain the existing return format.
	identityFData:=makeFData(One(G));
	for g in relative do
		sol:=inclusiondata(One(G),g,identityFData);
		if sol<>fail then return Concatenation(sol,[g]); fi;
	od;
	#Check every remaining pair before returning a negative answer.
	for g1 in Elements(G) do
		if not IsOne(g1) then
			FData:=makeFData(g1);
			for g in relative do
				g2:=g1*g;
				sol:=inclusiondata(g1,g2,FData);
				if sol<>fail then
					reduced:=inclusiondata(One(G),g,identityFData);
					if reduced=fail then
						ErrorNoReturn("IsSubalgebra: conjugator reduction check failed for this input");
					fi;
					return Concatenation(reduced,[g]);
				fi;
			od;
		fi;
	od;
	return "false inclusion data";
end;

#HasseDataG: builds the Hasse diagram of inclusions between algebra classes
#in: [algs,good], [algs,good,om] or either followed by rec(na:=list), with algs the algebra classes, good the class indices to keep ([] for all), om=rec(a,N) additive and na[i] the anyon multiplicity vector of class i (e.g. from AlgebraClasses), used only to skip pairs
#out: [coords,AdMat,HasseLines] with HasseLines the full inclusion relation as pairs [i,j] of class indices (class i strictly included in class j), AdMat the directed edges of its transitive reduction and coords the drawing coordinates (one row per dimension, the dimension increasing downwards), AdMat and coords indexed by the position of the class in Union(HasseLines), not by the class index
HasseDataG:=function(inp)
	local algs,good,om,subinp,na,opts,HasseLines,dims,i,j,k,ncl,incl,included,orderok,V,isin,paths,HasseLevels,n,AdMat,t,coords,x,y,HasseLevelsLengths;
	#each ordered pair of classes is decided once (memoized), by IsSubalgebra on every member of class i against every member of class j, after the necessary condition on the subgroup orders (|H2| divides |H1|, |F1| divides |F2|), and when na is given IsSubalgebra first tests the subobject condition na[i][a]<=na[j][a] for every anyon a
	algs:=inp[1];
	good:=inp[2];
	if good=[] then good:=[1..Length(algs)]; fi;
	opts:=rec();
	for k in [3..Length(inp)] do
		if IsRecord(inp[k]) and IsBound(inp[k].na) then opts:=inp[k];
		else om:=inp[k];
		fi;
	od;
	ncl:=Length(algs);
	if IsBound(opts.na) then
		na:=opts.na;
		if Length(na)<>ncl then ErrorNoReturn("HasseDataG: na must have one multiplicity vector per class"); fi;
	fi;
	dims:=List(algs,a->Order(a[1][5])*Order(a[1][2])/Order(a[1][1]));

	#necessary condition on the subgroups for A1 in A2 (IsSubalgebra needs H2^g <= H1 and F1 <= F2^g)
	orderok:=function(A1,A2)
		return IsInt(Size(A1[1])/Size(A2[1])) and IsInt(Size(A2[2])/Size(A1[2]));
	end;
	#input record of IsSubalgebra for A1 in class i and A2 in class j, with the stored na of the classes
	subinp:=function(A1,A2,i,j)
		local r;
		r:=rec(A2:=A2,A1:=A1);
		if IsBound(om) then r.om:=om; fi;
		if IsBound(na) then r.na1:=na[i]; r.na2:=na[j]; fi;
		return r;
	end;
	#memoized inclusion test between classes: IsSubalgebra runs at most once per ordered pair of members
	incl:=List([1..ncl],i->List([1..ncl],j->fail));
	included:=function(i,j)
		if incl[i][j]=fail then
			if not dims[i]<dims[j] then
				incl[i][j]:=false;
			else
				incl[i][j]:=ForAny(algs[i],A1->ForAny(algs[j],A2->
					orderok(A1,A2) and not IsString(IsSubalgebra(subinp(A1,A2,i,j)))));
			fi;
		fi;
		return incl[i][j];
	end;

	#inclusions with at least one end in good, then all inclusions between the classes they touch
	HasseLines:=[];
	for i in [1..ncl] do
		for j in [1..ncl] do
			if (i in good or j in good) and included(i,j) then Add(HasseLines,[i,j]); fi;
		od;
	od;
	V:=Union(HasseLines);
	for i in V do
		for j in V do
			if included(i,j) then Add(HasseLines,[i,j]); fi;
		od;
	od;
	HasseLines:=Union([HasseLines]);
	V:=Union(HasseLines);

	#directed edges: the pairs of HasseLines that are not a composite of two pairs of HasseLines
	isin:=List([1..ncl],i->List([1..ncl],j->false));
	for t in HasseLines do isin[t[1]][t[2]]:=true; od;
	paths:=Filtered(HasseLines,t->not ForAny(V,k->isin[t[1]][k] and isin[k][t[2]]));
	if not V=Union(paths) then ErrorNoReturn("HasseLines not paths"); fi;

	HasseLevels:=[];
	for n in Union([dims]) do
		Add(HasseLevels,Filtered(V,k->dims[k]=n));
	od;
	#one level per dimension that occurs, in increasing dimension
	HasseLevels:=Filtered(HasseLevels,l->l<>[]);
	if not Union(HasseLevels)=V then ErrorNoReturn("HasseLines not HasseLevels"); fi;

	isin:=List([1..ncl],i->List([1..ncl],j->false));
	for t in paths do isin[t[1]][t[2]]:=true; od;
	AdMat:=List(V,i->List(V,j->0));
	for i in [1..Length(V)] do
		for j in [1..Length(V)] do
			if isin[V[i]][V[j]] then AdMat[i][j]:=1; fi;
		od;
	od;
	coords:=[];
	HasseLevelsLengths:=List([1..Length(HasseLevels)],u->Length(HasseLevels[u]));
	for i in V do
		x:=0;
		y:=0;
		for j in [1..Length(HasseLevels)] do
			if i in HasseLevels[j] then
				x:=(Position(HasseLevels[j],i)-1-(HasseLevelsLengths[j]-1)*0.5);
				if not HasseLevelsLengths[j]=1 then
					x:=x*((Maximum(HasseLevelsLengths)-1)/(HasseLevelsLengths[j]-1))*1.1;
				fi;
				y:=-4.5*j;
			fi;
		od;
		Add(coords,[x,y*0.3]);
	od;
	return [coords,AdMat,HasseLines];
end;



#HassePhases: names the gapped phase of each algebra from the Hasse diagram
#in: [algs,nsym,HasseLines] or [algs,nsym,HasseLines,false] with algs the list of [dimension,anyon vector], nsym the index of the symmetric algebra (Lagrangian), HasseLines from HasseDataG, and false to omit the prefix i, which is correct only when algs contains every Lagrangian algebra class above each algebra
#out: the list of phase names, one string per algebra
HassePhases:=function(inp)#(algs,nsym,HasseLines)
		local algs,AA,nsym,HasseLines,withi,dims,dimM,paths,nA,phases,t,A,n,ReachableFrom;
		#SPT/SSB for a Lagrangian algebra with one or more vacua (<A_sym,A>=1 or >1), gSPT/gSSB likewise for a non-Lagrangian one, and the prefix "i" (intrinsically gapless) when every Lagrangian above the algebra in the partial order has more vacua than the algebra itself, the criterion of Bhardwaj et al. [arXiv:2403.00905, cited in TwinAlgebras.tex Sec. Hasse]
		algs:=inp[1];
		nsym:=inp[2];
		HasseLines:=inp[3];
		withi:=not (Length(inp)>3 and inp[4]=false);

		dims:=List(algs,x->x[1]); #dims of the algebras
		AA:=List(algs,x->x[2]); #anyon vectors of the algebras
		dimM:=Maximum(dims);
		paths:=HasseLines;

		#n=scalar product with A[nsym]
		nA:=[];
		for A in AA do
			Add(nA,AA[nsym]*A);
		od;

		phases:=[];
		for n in [1..Length(nA)] do
			if dims[n]=dimM then
				if nA[n]=1 then
					Add(phases,"SPT");
				else
					Add(phases,"SSB");
				fi;
			else
				if nA[n]=1 then
					Add(phases,"gSPT");
				else
					Add(phases,"gSSB");
				fi;
			fi;
		od;
		#HasseLines is the full inclusion relation (third output of HasseDataG). ReachableFrom gives the same set for it and for its directed edges, so a maximal-dimension algebra above n need not be a direct successor of n.
		ReachableFrom:=function(start,edges)
			local reached,frontier,next,e;
			reached:=[];
			frontier:=[start];
			while frontier<>[] do
				next:=[];
				for e in edges do
					if e[1] in frontier and not e[2] in reached then
						Add(reached,e[2]);
						Add(next,e[2]);
					fi;
				od;
				frontier:=next;
			od;
			return reached;
		end;
		if withi then
			for n in [1..Length(nA)] do
				if phases[n] in ["gSPT","gSSB"] then
					t:=Filtered(ReachableFrom(n,paths),k->dims[k]=dimM);
					if t<>[] and Minimum(List(t,k->nA[k]))>nA[n] then
						phases[n]:=Concatenation("i",phases[n]);
					fi;
				fi;
			od;
		fi;
		return phases;
end;

#OperatorAlgebra: the algebra of order parameters of an algebra of a theory, the G-graded algebra structure of A(H,F,gamma,eps) as an explicit ordered-basis model (degree 1 the local operators, degree g the g-twisted sector operators for the Vec_G^omega symmetry, TwinAlgebras.tex Sec. The Algebra of Order Parameters)
#in: (th,A[,R]) with th from TQDTheory (or a record with [om]), A an algebra [H,F,gamma,eps,G] or a record from AlgebrasWithAnyons, and R one representative of every left coset of H in G (default the GAP representatives)
#out: rec(data,om,R,basis,structureConstants,multiplyBasis,multiply,unit,grading,GAction) with vectors given as coefficient lists in basis
OperatorAlgebra:=function(arg)
	local inp,A,H,F,gamma,eps,G,omega,omegam,trivialOmega,ElF,ElG,cosets,cos,R,
		seen,g,r,k,basis,dim,one,multiplyBasis,multiply,unit,grading,GAction,
		structureConstants,i,j,pair1,pair2,coefficient,q,ci,rp,h,np,out,u,v;
	#the basis is Cartesian(R,Elements(F)) of TwinAlgebras.tex eq. (basiselm), one twisted group-algebra block per representative of a left coset gH, since eq. (v_equiv_rel) identifies v_{gh,n} with v_{g,hnh^-1}: products from different blocks vanish, and vectors are coefficient lists in this basis
	#the input record of the computation below: the algebra, omega of the theory and the optional R
	inp:=rec(data:=arg[2]);
	if IsRecord(inp.data) then inp.data:=inp.data.A; fi;
	if IsBound(arg[1].om) then inp.om:=arg[1].om; fi;
	if Length(arg)>2 then inp.R:=arg[3]; fi;
	if not "data" in RecNames(inp) or not IsList(inp.data) or Length(inp.data)<>5 then
		ErrorNoReturn("OperatorAlgebra: data must be [H,F,gamma,epsilon,G]");
	fi;
	A:=inp.data;
	H:=A[1]; F:=A[2]; gamma:=A[3]; eps:=A[4]; G:=A[5];
	if not (IsGroup(H) and IsGroup(F) and IsGroup(G)) then
		ErrorNoReturn("OperatorAlgebra: H, F, and G must be groups");
	fi;
	if not (IsFunction(gamma) and IsFunction(eps)) then
		ErrorNoReturn("OperatorAlgebra: gamma and epsilon must be functions");
	fi;
	if not IsSubset(G,H) then
		ErrorNoReturn("OperatorAlgebra: H must be a subgroup of G");
	fi;
	if not IsSubset(H,F) or not IsNormal(H,F) then
		ErrorNoReturn("OperatorAlgebra: F must be normal in H");
	fi;
	if "om" in RecNames(inp) then
		omega:=inp.om;
		if not IsRecord(omega) or not ("a" in RecNames(omega)) or
			not ("N" in RecNames(omega)) or not IsFunction(omega.a) or
			not IsPosInt(omega.N) then
			ErrorNoReturn("OperatorAlgebra: om must have a function a and positive integer N");
		fi;
		omegam:=function(g1,g2,g3) return E(omega.N)^omega.a(g1,g2,g3); end;
		trivialOmega:=false;
	else
		omega:=rec(a:=function(g1,g2,g3) return 0; end,N:=1);
		omegam:=function(g1,g2,g3) return 1; end;
		trivialOmega:=true;
	fi;
	ElF:=Elements(F);
	ElG:=Elements(G);
	cosets:=LeftCosets(G,H);
	cos:=List(cosets,c->Elements(c));
	if "R" in RecNames(inp) then
		R:=ShallowCopy(inp.R);
		if Length(R)<>Length(cosets) or not ForAll(R,x->x in G) then
			ErrorNoReturn("OperatorAlgebra: R must contain one representative of every left coset");
		fi;
		seen:=List(R,x->Posinlist(cos,x));
		if fail in seen or Length(Set(seen))<>Length(cosets) then
			ErrorNoReturn("OperatorAlgebra: R must contain one representative of every left coset");
		fi;
		cos:=List(R,x->Elements(cosets[Posinlist(List(cosets,c->Elements(c)),x)]));
	else
		R:=List(cosets,Representative);
	fi;
	basis:=Cartesian(R,ElF);
	dim:=Length(basis);
	one:=One(F);
	coefficient:=function(r,n1,n2)
		if trivialOmega then
			return gamma(n1,n2);
		fi;
		return gamma(n1,n2)/3cocl(omegam,r,n1,n2);
	end;
	multiplyBasis:=function(i,j)
		local ans,b1,b2;
		if not (i in [1..dim] and j in [1..dim]) then
			ErrorNoReturn("OperatorAlgebra.multiplyBasis: basis index out of range");
		fi;
		ans:=List([1..dim],x->0);
		b1:=basis[i]; b2:=basis[j];
		if b1[1]=b2[1] then
			ans[Position(basis,[b1[1],b1[2]*b2[2]])]:=
				coefficient(b1[1],b1[2],b2[2]);
		fi;
		return ans;
	end;
	multiply:=function(v,u)
		local ans,ii,jj,term;
		if not (IsList(v) and IsList(u) and Length(v)=dim and Length(u)=dim) then
			ErrorNoReturn("OperatorAlgebra.multiply: vectors have the wrong dimension");
		fi;
		ans:=List([1..dim],x->0);
		for ii in PosNonZero(v) do for jj in PosNonZero(u) do
			term:=multiplyBasis(ii,jj);
			ans:=ans+v[ii]*u[jj]*term;
		od; od;
		return ans;
	end;
	unit:=List([1..dim],x->0);
	for r in R do
		unit[Position(basis,[r,one])]:=1;
	od;
	grading:=List(basis,b->b[1]*b[2]*b[1]^-1);
	GAction:=function(g,v)
		local ans,ii,b,q,cosIndex,rnew,hh,nnew,factor;
		if not g in G then
			ErrorNoReturn("OperatorAlgebra.GAction: first argument is not in G");
		fi;
		if not IsList(v) or Length(v)<>dim then
			ErrorNoReturn("OperatorAlgebra.GAction: vector has the wrong dimension");
		fi;
		ans:=List([1..dim],x->0);
		for ii in PosNonZero(v) do
			b:=basis[ii];
			q:=g*b[1];
			cosIndex:=Posinlist(cos,q);
			rnew:=R[cosIndex];
			hh:=rnew^-1*q;
			if not hh in H then
				ErrorNoReturn("OperatorAlgebra.GAction: invalid right correction");
			fi;
			nnew:=hh*b[2]*hh^-1;
			#g.v_{r,n} = omega(g,r|n)^-1 v_{g r,n} and v_{rnew hh,n} = eps(hh,n) omega(rnew,hh|n) v_{rnew,hh n hh^-1}, omega(f,g|h) = 3cocr. These are eqn:G-action_algebra_basis and eq:v_equiv_rel of TwinAlgebras.tex with omega(f,g|h) inverted, so that the action is omega(.,.|x)^-1-projective as for the anyons (Prop. anyon) and the product is G-equivariant.
			if trivialOmega then
				factor:=eps(hh,b[2]);
			else
				factor:=eps(hh,b[2])*3cocr(omegam,rnew,hh,b[2])/3cocr(omegam,g,b[1],b[2]);
			fi;
			ans[Position(basis,[rnew,nnew])]:=
				ans[Position(basis,[rnew,nnew])]+v[ii]*factor;
		od;
		return ans;
	end;
	structureConstants:=[];
	for i in [1..dim] do for j in [1..dim] do
		out:=multiplyBasis(i,j);
		for k in PosNonZero(out) do
			Add(structureConstants,[i,j,k,out[k]]);
		od;
	od; od;
	return rec(
		data:=A,
		om:=omega,
		R:=R,
		basis:=basis,
		structureConstants:=structureConstants,
		multiplyBasis:=multiplyBasis,
		multiply:=multiply,
		unit:=unit,
		grading:=grading,
		GAction:=GAction
	);
end;

#TopologicalSectors: the topological sectors of the gapped boundary of a Lagrangian algebra, one per double coset HgH of H in G and irreducible projective representation of H meet gHg^-1 for the 2-cocycle psi^g of Ostrik (math/0202130, Prop. 3.1, with psi1=psi2=gamma)
#in: (th,L) with th from TQDTheory (or a record with [om]) and L a Lagrangian algebra [H,H,gamma,eps,G] or a record from AlgebrasWithAnyons
#out: the sorted list of sectors [double coset,projective character values,elements of H^g meet H]
TopologicalSectors:=function(arg)
	local inp,H,gamma,psi,G,om,h1,h2,h3,totest,toret,dc,hL,hR,ElG,ElH,g,t,Upsi,rst,rs,m,beta,extensionData,projCharData,ElHg,Hg,iso,bbeta,exp,val,ch,cl,clr,irr,Uret,r,EmbedIntoPCGroupExtCg,j,dict;
	#the input record of the computation below: the algebra and omega of the theory
	inp:=rec(data:=arg[2]);
	if IsRecord(inp.data) then inp.data:=inp.data.A; fi;
	if IsBound(arg[1].om) then inp.om:=arg[1].om; fi;
	H:=inp.data[1];
	if not H=inp.data[2] then ErrorNoReturn("TopologicalSectors: L must be Lagrangian (H=F)"); fi;
	gamma:=inp.data[3];
	G:=inp.data[5];
	if "om" in RecNames(inp) then
		om:=inp.om;
	else 
		om:=rec(a:=function(h1,h2,h3) return 0; end, N:=1); 
	fi;
	ElG:=Elements(G);
	ElH:=Elements(H);
	toret:=[];
	#Ostrik math/0202130 Prop. 3.1: one sector per double coset HgH, with psi^g defined on H cap g H g^-1 (GAP: H^g = g^-1 H g)
	for g in List(DoubleCosets(G,H,H),Representative) do
		dc:=DoubleCoset(H,g,H);
		Hg:=Intersection(H,H^(g^-1));
		ElHg:=Elements(Hg);

		if not Order(Hg)=1 then 
			psi:=function(g,h1,h2) return gamma(h1,h2)*gamma((h2^-1)^g,(h1^-1)^g)*(E(om.N)^(-om.a(h1*h2*g,(h2^-1)^g,(h1^-1)^g)))*(E(om.N)^(om.a(h1,h2,g)))*(E(om.N)^(om.a(h1,h2*g,(h2^-1)^g))); end;
			totest:=function(h1,h2) return psi(g,h1,h2); end;
			if (not 2coctest(Hg,totest)=true) then ErrorNoReturn("psi not 2coc"); fi;

			Upsi:=[];
			for h1 in Hg do for h2 in Hg do
				t:=psi(g,h1,h2);
				if (not t in Upsi) then Add(Upsi,t); fi;
			od; od;
			rst:=List(Upsi,DescriptionOfRootOfUnity);
			m:=Lcm(List(rst,r->r[1]));
			rs:=List(rst,r->(m/r[1])*r[2]);
			#psi in additive notation
			beta:=function(h1,h2)
				local tt;
				if (h1 in Hg and h2 in Hg) then
					tt:=psi(g,h1,h2);
					if tt=1 then return 0;
						else return rs[Position(Upsi,tt)]; 
					fi;
				else return 0;
				fi;
			end;
			val:=Gcd(Concatenation(rs,[m]));
			exp:=m/val;
		
			iso:= IsomorphismFpGroupByGeneratorsNC(Hg,GeneratorsOfGroup(Hg));
   		bbeta       := function(h1, h2)
   	   	return beta(PreImage(iso, h1), PreImage(iso, h2))/val;
   	   end;
			for h1 in Image(iso) do for h2 in Image(iso) do for h3 in Image(iso) do
				if not ((bbeta(h1,h2)+bbeta(h1*h2,h3)-bbeta(h2,h3)-bbeta(h1,h2*h3)) mod exp = 0) then ErrorNoReturn("bbeta not 2coc"); fi;
			od; od; od;
			extensionData:=[iso, Hg, GroupExtension(Image(iso), exp, bbeta)];	

			projCharData:=ProjectiveCharacters(extensionData[3].CgExtGens, extensionData[3].CgExtPc, extensionData[3].CgExtIso);	
	
			EmbedIntoPCGroupExtCg:=extensionData[3].embedding;

			for j in projCharData do
				Add(toret,[Elements(dc),List(ElHg,h1->EmbedIntoPCGroupExtCg(h1^iso)^j),ElHg]);
			od;
		else
					Add(toret,[Elements(dc),List(ElHg,h1->1),ElHg]);
		fi;

	od;
	Uret:=Union([toret]);
	SortBy(Uret,x->[x[1],Length(Union([x[2]]))]);
	return Uret;
end;

#AlgebraClasses: the algebra classes and twin pairs of a theory, each class with its anyon decomposition
#in: (th[,filter]) with th from TQDTheory and filter as in SubgroupPairs, so that only the algebras on those subgroup pairs are classified (the filters are invariant under isomorphism, so these are the classes of the theory that pass the filter)
#out: rec(classes,twins,reasons,[filter]) with classes a list of rec(n,algebras,name,dim,na,decomposition) (n the class index, name the AlgebraName of the first algebra), twins and reasons as in AlgebraClassesG with op="" (class indices), and filter the filter when one is given
AlgebraClasses:=function(arg)
	local th,data,res,classes,n,A,na;
	th:=arg[1];
	data:=rec(G:=th.G,aG:=th.aG,glG:=th.glG);
	if IsBound(th.om) then data.om:=th.om; fi;
	if Length(arg)>1 then
		data.HFtot:=SubgroupPairs(th,arg[2]);
		if data.HFtot=[] then return rec(classes:=[],twins:=[],reasons:=[],filter:=arg[2]); fi;
	fi;
	res:=AlgebraClassesG(data);
	classes:=[];
	for n in [1..Length(res[1])] do
		A:=res[1][n][1];
		#the anyon vector of A, computed by AlgebraClassesG (with the zero cocycle for an untwisted theory, which gives the same vector)
		na:=res[4][n];
		Add(classes,rec(n:=n,algebras:=res[1][n],name:=AlgebraName(A,th.glG),
			dim:=Order(th.G)*Order(A[2])/Order(A[1]),na:=na,decomposition:=ShowAlg(na,th.labels)));
	od;
	res:=rec(classes:=classes,twins:=res[2],reasons:=res[3]);
	if Length(arg)>1 then res.filter:=arg[2]; fi;
	return res;
end;

#Hasse: the Hasse diagram of inclusions between the algebra classes of a theory
#in: (th[,M]) with th from TQDTheory and M from AlgebraClasses (computed when absent)
#out: rec(M,coords,AdMat,inclusions,edges,vertices) with class indices throughout: inclusions the full inclusion relation (third output of HasseDataG), edges its directed edges (the 1s of AdMat), vertices the class labelling row/column n of AdMat and coords[n] (HasseDataG indexes these by Union(inclusions), not by class)
Hasse:=function(arg)
	local th,M,inp,res,V;
	th:=arg[1];
	if Length(arg)>1 then M:=arg[2]; else M:=AlgebraClasses(th); fi;
	inp:=[List(M.classes,c->c.algebras),[]];
	if IsBound(th.om) then Add(inp,th.om); fi;
	Add(inp,rec(na:=List(M.classes,c->c.na)));
	res:=HasseDataG(inp);
	V:=Union(res[3]);
	return rec(M:=M,coords:=res[1],AdMat:=res[2],inclusions:=res[3],vertices:=V,
		edges:=Concatenation(List([1..Length(V)],i->List(Filtered([1..Length(V)],j->res[2][i][j]=1),j->[V[i],V[j]]))));
end;

#DisplayClasses: the classes shown by AlgebraTableTeX and HasseTikz, in display order
#in: (M,opts) with M from AlgebraClasses and opts a record with optional field classes (a list of class indices of M, default all classes)
#out: the class indices sorted by dimension (the identity algebra first, the Lagrangian algebras last), ties in the order of M; display number i (the label prefix:i) is the i-th entry, so a table and a Hasse diagram built with the same opts.classes and prefix refer to the same algebras
DisplayClasses:=function(M,opts)
	local cl;
	if IsBound(opts.classes) then cl:=ShallowCopy(opts.classes); else cl:=[1..Length(M.classes)]; fi;
	SortBy(cl,c->[M.classes[c].dim,c]);
	return cl;
end;

#TeXOutput: returns a LaTeX string, after writing it to opts.file when that is given
#in: (s,opts) with s a string and opts a record with optional field file (a file name, overwritten)
#out: s
TeXOutput:=function(s,opts)
	local out;
	if IsBound(opts.file) then
		#without print formatting, so that long lines are not broken with backslashes
		out:=OutputTextFile(opts.file,false);
		SetPrintFormattingStatus(out,false);
		WriteAll(out,s);
		CloseStream(out);
	fi;
	return s;
end;

#AlgebraTableTeX: the table of algebras of a theory in the layout of TwinAlgebras.tex (Table tab:G_om)
#in: (th,M[,opts]) with th from TQDTheory, M from AlgebraClasses(th) and opts a record with optional fields classes (class indices to show, default all), prefix (label prefix, default "A"), symbol (the displayed name of algebra i is symbol_{i}, default "A^\omega" for a twisted theory and "A" otherwise), file (write the table there)
#out: the LaTeX string of a one-column tabular: for each class, in the order of DisplayClasses, the rows \nameref{prefix:i}$=A(H,N,gamma,eps)$, then $\xlabel[$symbol_{i}$]{prefix:i} decomposition$, then the reduced topological order (Trivial for the Lagrangian algebras, which follow a double \hline); \xlabel is the macro of TwinAlgebras.tex, \newcommand\xlabel[2][]{\phantomsection\def\@currentlabelname{#1}\label{#2}} (needs hyperref and \makeatletter), and \Z is its macro for cyclic groups
AlgebraTableTeX:=function(arg)
	local th,M,opts,prefix,symbol,cl,s,i,c,lagstarted;
	th:=arg[1]; M:=arg[2];
	if Length(arg)>2 then opts:=arg[3]; else opts:=rec(); fi;
	if IsBound(opts.prefix) then prefix:=opts.prefix; else prefix:="A"; fi;
	if IsBound(opts.symbol) then symbol:=opts.symbol;
	elif IsBound(th.om) then symbol:="A^\\omega";
	else symbol:="A";
	fi;
	cl:=DisplayClasses(M,opts);
	s:="\\begin{tabular}{|l|}\n\\hline\n";
	lagstarted:=false;
	for i in [1..Length(cl)] do
		c:=M.classes[cl[i]];
		#a Lagrangian class has dimension |G|
		if c.dim=Order(th.G) and not lagstarted then
			if i>1 then Append(s,"\\hline\n"); fi;
			lagstarted:=true;
		fi;
		Append(s,HasseEntryTeX(th,c,i,rec(prefix:=prefix,symbol:=symbol)));
	od;
	Append(s,"\\end{tabular}\n");
	return TeXOutput(s,opts);
end;

#TwinTableTeX: the table of twin algebras of a theory in the layout of TwinAlgebras.tex (Table tab:twinsG32-43)
#in: (th,M[,opts]) with th from TQDTheory, M from AlgebraClasses(th) and opts a record with optional field file
#out: the LaTeX string of an array with one row per twin pair of M.twins: the two algebras A(H,N,gamma,eps) and their common anyon decomposition, their reduced topological orders, and the reason(s) of M.reasons for that pair (inequivalence of the subgroups or of gamma, eps up to conjugation, as found by AlgebraClassesG)
TwinTableTeX:=function(arg)
	local th,M,opts,s,p,r1,r2,why;
	th:=arg[1]; M:=arg[2];
	if Length(arg)>2 then opts:=arg[3]; else opts:=rec(); fi;
	s:=Concatenation("\\begin{array}{|c|c|c|}\n\\hline\n\\makecell{\\text{Twin Algebras}} & \\makecell{\\text{Reduced} \\\\ \\text{TO}}",
		" & \\makecell{\\text{Algebra} \\\\ \\text{Inequivalence}}\\\\\n\\hline \\hline\n");
	for p in M.twins do
		r1:=AlgebraDisplayData(th,M.classes[p[1]]);
		r2:=AlgebraDisplayData(th,M.classes[p[2]]);
		why:=List(Filtered(M.reasons,x->Set(x[1])=Set(p)),x->x[2]);
		Append(s,Concatenation("\\makecell{",r1.nameTeX," \\\\\n",r2.nameTeX," \\\\\n",r1.decompositionTeX,"}\n & \\makecell{",
			r1.reducedTOTeX," \\\\ ",r2.reducedTOTeX," \\\\ { }} & \\makecell{",JoinStringsWithSeparator(why," \\\\ "),"}\\\\\n\\hline\n"));
	od;
	Append(s,"\\end{array}\n");
	return TeXOutput(s,opts);
end;

#HasseTikz: the Hasse diagram of a theory as a tikz picture in the layout of TwinAlgebras.tex (Figure fig:Hasse3243_om)
#in: (th,Hs[,opts]) with th from TQDTheory, Hs from Hasse(th) and opts a record with optional fields classes (class indices of Hs.M to draw, default all: a partial diagram as in the paper), prefix (as in AlgebraTableTeX, default "A"), nameref:=false (label the nodes $symbol_{i}$ instead of \nameref{prefix:i}; symbol as in AlgebraTableTeX), xsep (horizontal distance of neighbouring nodes in the widest level, default 11/10; the other levels are spread over the same width), ysep (distance of the dimension levels, default 3/2), file (write the picture there)
#out: the LaTeX string of the tikzpicture: the shown algebras arranged by quantum dimension along the vertical axis (the identity algebra at the top, the Lagrangian algebras at the bottom), node i the i-th class of DisplayClasses, and an arrow p_i -> p_j for each directed edge among the shown classes (A_i strictly included in A_j and no shown A_k in between), from the full inclusion relation Hs.inclusions
HasseTikz:=function(arg)
	local th,Hs,M,opts,prefix,symbol,xsep,ysep,cl,n,dims,levels,maxlev,incl,cover,dec,s,i,j,k,lev,x,y,pos;
	th:=arg[1]; Hs:=arg[2]; M:=Hs.M;
	if Length(arg)>2 then opts:=arg[3]; else opts:=rec(); fi;
	if IsBound(opts.prefix) then prefix:=opts.prefix; else prefix:="A"; fi;
	if IsBound(opts.symbol) then symbol:=opts.symbol;
	elif IsBound(th.om) then symbol:="A^\\omega";
	else symbol:="A";
	fi;
	if IsBound(opts.xsep) then xsep:=opts.xsep; else xsep:=11/10; fi;
	if IsBound(opts.ysep) then ysep:=opts.ysep; else ysep:=3/2; fi;
	cl:=DisplayClasses(M,opts);
	n:=Length(cl);
	if n=0 then ErrorNoReturn("HasseTikz: no class selected (opts.classes or the filter is empty)"); fi;
	dims:=List(cl,c->M.classes[c].dim);
	levels:=Set(dims);
	maxlev:=Maximum(List(levels,d->Number(dims,e->e=d)));
	incl:=List([1..n],i->List([1..n],j->[cl[i],cl[j]] in Hs.inclusions));
	cover:=List([1..n],i->List([1..n],j->incl[i][j] and not ForAny([1..n],k->incl[i][k] and incl[k][j])));
	#a rational number as a decimal string with two digits after the point
	dec:=function(q)
		local m,t;
		m:=Int(AbsInt(q)*100+1/2);
		t:=String(m mod 100);
		if Length(t)=1 then t:=Concatenation("0",t); fi;
		if q<0 and m>0 then return Concatenation("-",String(QuoInt(m,100)),".",t); fi;
		return Concatenation(String(QuoInt(m,100)),".",t);
	end;
	s:="\\begin{tikzpicture}[vertex/.style={draw}, scale=0.9]\n \\begin{scope}[shift={(0,0)}]\n    \\foreach \\coord/\\i/\\j in {\n";
	for i in [1..n] do
		lev:=Position(levels,dims[i]);
		pos:=Filtered([1..n],k->dims[k]=dims[i]);
		#each level is spread over the width of the widest level, so that arrows avoid the nodes of a level with fewer nodes
		x:=(Position(pos,i)-(Length(pos)+1)/2)*xsep;
		if Length(pos)>1 then x:=x*(maxlev-1)/(Length(pos)-1); fi;
		y:=-lev*ysep;
		Append(s,Concatenation("(",dec(x),",",dec(y),")/",String(i),"/{"));
		if IsBound(opts.nameref) and opts.nameref=false then
			Append(s,Concatenation("$",symbol,"_{",String(i),"}$}"));
		else
			Append(s,Concatenation("\\nameref{",prefix,":",String(i),"}}"));
		fi;
		if i<n then Append(s,",\n"); else Append(s,"}\n"); fi;
	od;
	Append(s,"     {\n      \\node[vertex,align=center] (p\\i) at \\coord {\\j};\n     }\n  \\foreach [count=\\r] \\row in \n{");
	Append(s,JoinStringsWithSeparator(List([1..n],i->Concatenation("{",JoinStringsWithSeparator(List(cover[i],function(b) if b then return "1"; fi; return "0"; end),","),"}")),",\n"));
	Append(s,"}\n    {\n     \\foreach [count=\\c] \\cell in \\row{\n            \\ifnum\\cell=1%\n                \\draw[-stealth] (p\\r) edge [thick] (p\\c);\n            \\fi\n        }\n    }\n\\end{scope}\n\\end{tikzpicture}\n");
	return TeXOutput(s,opts);
end;

#HasseTableTeX: produce a Hasse diagram and its linked algebra table together
#in: (th,Hs[,opts]) with Hs from Hasse(th), and opts as in HasseTikz and AlgebraTableTeX, with optional diagramFile and tableFile for the two TeX fragments
#out: rec(diagram,table,classes,prefix) where the display numbers and label prefix agree in both fragments. The caller supplies tikz, hyperref, \nameref, \xlabel, \cZ, \Vec and \Z in the TeX preamble. The files contain fragments without figure/table wrappers.
HasseTableTeX:=function(arg)
	local th,Hs,opts,cl,prefix,tikzopts,tableopts,diagram,table;
	th:=arg[1]; Hs:=arg[2];
	if Length(arg)>2 then opts:=arg[3]; else opts:=rec(); fi;
	cl:=DisplayClasses(Hs.M,opts);
	if cl=[] or Length(Set(cl))<>Length(cl) or not ForAll(cl,i->IsInt(i) and i in [1..Length(Hs.M.classes)]) then
		ErrorNoReturn("HasseTableTeX: classes must be distinct class indices of Hs.M");
	fi;
	if IsBound(opts.prefix) then prefix:=opts.prefix; else prefix:="A"; fi;
	tikzopts:=rec(classes:=cl,prefix:=prefix);
	tableopts:=rec(classes:=cl,prefix:=prefix);
	if IsBound(opts.symbol) then tikzopts.symbol:=opts.symbol; tableopts.symbol:=opts.symbol; fi;
	if IsBound(opts.xsep) then tikzopts.xsep:=opts.xsep; fi;
	if IsBound(opts.ysep) then tikzopts.ysep:=opts.ysep; fi;
	if IsBound(opts.diagramFile) then tikzopts.file:=opts.diagramFile; fi;
	if IsBound(opts.tableFile) then tableopts.file:=opts.tableFile; fi;
	diagram:=HasseTikz(th,Hs,tikzopts);
	table:=AlgebraTableTeX(th,Hs.M,tableopts);
	return rec(diagram:=diagram,table:=table,classes:=cl,prefix:=prefix);
end;

#HasseEntryTeX: the LaTeX entry of one algebra of a Hasse diagram
#in: th from TQDTheory, A an algebra or class record, i its display number, and optional opts with prefix and symbol
#out: three table rows containing the algebra name, linked anyon decomposition, and reduced topological order
HasseEntryTeX:=function(arg)
	local th,A,i,opts,prefix,symbol,r;
	th:=arg[1]; A:=arg[2]; i:=arg[3];
	if Length(arg)>3 then opts:=arg[4]; else opts:=rec(); fi;
	if IsBound(opts.prefix) then prefix:=opts.prefix; else prefix:="A"; fi;
	if IsBound(opts.symbol) then symbol:=opts.symbol;
	elif IsBound(th.om) then symbol:="A^\\omega";
	else symbol:="A";
	fi;
	r:=AlgebraDisplayData(th,A);
	return Concatenation(
		"\\nameref{",prefix,":",String(i),"}$=",r.nameTeX,"$\\\\\n",
		"$\\xlabel[$",symbol,"_{",String(i),"}$]{",prefix,":",String(i),"}",r.decompositionTeX,"$\\\\\n",
		"$",r.reducedTOTeX,"$\\\\\n\\hline\n");
end;

#PhaseLabels: the gapped-phase name of every algebra class, relative to a chosen symmetry boundary
#in: (th,nsym[,Hs]) with th from TQDTheory, nsym the index of the symmetry-boundary class in Hs.M.classes, which must be Lagrangian (dimension |G|), and Hs from Hasse (default Hasse(th))
#out: the list of HassePhases names, indexed like the classes. For Hs.M from a filtered AlgebraClasses there are not enough algebras to determine whether a phase is intrinsically gapless, so the non-Lagrangian classes are labelled only gSPT or gSSB
PhaseLabels:=function(arg)
	local th,nsym,Hs;
	th:=arg[1]; nsym:=arg[2];
	if Length(arg)>2 then Hs:=arg[3]; else Hs:=Hasse(th); fi;
	#the symmetry boundary is a gapped boundary: a Lagrangian algebra, i.e. of dimension |G| (TwinAlgebras.tex, Corollary Lagrangian algebras)
	if not nsym in [1..Length(Hs.M.classes)] or Hs.M.classes[nsym].dim<>Order(th.G) then
		ErrorNoReturn("PhaseLabels: nsym must be the index of a Lagrangian algebra class (dimension |G|)");
	fi;
	#a filtered list may miss Lagrangian classes above a class, which the prefix i needs, so it is omitted
	return HassePhases([List(Hs.M.classes,c->[c.dim,c.na]),nsym,Hs.inclusions,not IsBound(Hs.M.filter)]);
end;
