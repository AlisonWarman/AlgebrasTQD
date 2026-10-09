#############################################################################
##
## source/3_cocycles.g                 AlgebrasTQD
##
## Cocycle construction, validation, and trivialization.
##
## Functions in this file (the first line of each header):
## - ftriv: the trivial multiplicative 2-cochain
## - omtriv: the trivial additive 3-cocycle
## - igomf: the 2-cocycle theta_g of the g-twisted sector on the centralizer of g, obtained from a 3-cocycle
## - 3cocr: the right G-action phase omega(f,g|h)
## - 3cocl: the left-handed counterpart of 3cocr
## - theta: the projective phase theta_g(x,y) of a flux sector (Gruen's thesis eq. (4.1))
## - 3coctest: tests whether an additive 3-cochain is a normalized 3-cocycle (for cocycles not from omf or omaut)
## - UCTInvariants: HAP's UCT record of TR in degree n and the invariant factors of its cocycle basis
## - omf: representatives of H^3(F,U(1))
## - omaut: representatives of H^3(F,U(1)) up to automorphisms of F
## - 3coctestm: tests whether a multiplicative 3-cochain is a normalized 3-cocycle
## - Show3coc: prints the nonzero values of a 3-cocycle
## - 2coctest: tests whether a multiplicative 2-cochain is a 2-cocycle
## - IsTrivial2coc: trivializes a multiplicative 2-cocycle gamma(f1,f2)=c(f1*f2)/(c(f1)*c(f2)) (inverse of the convention of IsCounterterm (07))
## - gammatest: tests gamma(g2,g3)gamma(g1,g2g3)=gamma(g1g2,g3)gamma(g1,g2)omega(g1,g2,g3) and normalization
## - GammaTrivialization: one trivialization gamma0 of omega restricted to F (equations only for g3 in a generating set, which suffice for a normalized omega)
## - GammaH2Representatives: representatives of H^2(F,U(1))
## - gammaf: all normalized trivializations gamma of omega restricted to F, one per class of H^2(F,U(1))
## - Nice3coc: regauges omega so that every gamma of the algebras is a genuine 2-cocycle
## - IsNormalizedCocycle: tests whether an additive 3-cochain is normalized
## - NormalizeCocycle: a normalized 3-cocycle om-d(beta) in the class of om, beta solved by SolveModZ (not called by the package)
## - H3Invariants: the coordinates of H^3(G,U(1)) used by H3Cocycle
## - H3Cocycle: the additive 3-cocycle of a class of H^3(G,U(1)) given by its coordinates
## - TQDTheory: the data of Z(Vec_G^omega) used by the other routines, computed once
## - OmegaArgs: the trailing omega argument of the existing list-input routines
##
#############################################################################

#ftriv: the trivial multiplicative 2-cochain
#in: g1,g2 group elements
#out: 1, i.e. the trivial multiplicative 2-cochain
ftriv:=function(g1,g2) return 1; end;
#omtriv: the trivial additive 3-cocycle
#in: none
#out: rec(a,N) with a=0 and N=1
omtriv:=rec(a:=function(g1,g2,g3) return 0; end, N:=1);
#igomf: the 2-cocycle theta_g of the g-twisted sector on the centralizer of g, obtained from a 3-cocycle
#in: om=rec(a,N) an additive 3-cocycle and g a group element
#out: the function (g1,g2)->root of unity; for g1,g2 in C_G(g) it is Gruen-Morrison's theta_g(g1,g2), elsewhere it is not a 2-cocycle (the conjugates of g in theta are replaced by g)
igomf:=function(om, g)
    local igom,g1,g2;
    igom := function(g1, g2)
        return E(om.N)^(om.a(g,g1,g2)+om.a(g1,g2,g)-om.a(g1,g,g2));
			#omega(g, h, k) + omega(h, k, g) - omega(h, g, k);
    end;
	return igom;
end;

#3cocr: the right G-action phase omega(f,g|h)
#in: 3coc a multiplicative 3-cocycle and f,g,h group elements
#out: the root of unity omega(f,g|h) used by the right G-action
3cocr:=function(3coc,f,g,h)
	return 3coc(f,g*h*Inverse(g),g)/(3coc(f,g,h)*3coc((f*g)*h*Inverse(f*g),f,g));
end;

#3cocl: the left-handed counterpart of 3cocr
#in: 3coc a multiplicative 3-cocycle and f,g,h group elements
#out: the root of unity of the left-handed counterpart of 3cocr
3cocl:=function(3coc,f,g,h)
	return 3coc(f,g,h)*3coc(f*g*Inverse(f),f*h*Inverse(f),f)/3coc(f*g*Inverse(f),f,h);
end;


#theta: the projective phase theta_g(x,y) of a flux sector (Gruen's thesis eq. (4.1))
#in: 3coc a multiplicative 3-cocycle, g a flux and x,y group elements
#out: theta_g(x,y) as a root of unity
theta:=function(3coc,g,x,y)
	return 3coc(g,x,y)*3coc(x,y,(x*y)^-1*g*(x*y))/3coc(x,x^-1*g*x,y);
end;


#3coctest: tests whether an additive 3-cochain is a normalized 3-cocycle (for cocycles not from omf or omaut)
#in: [El,om] with El the elements of a group and om=rec(a,N) additive
#out: true or false; warns when om is a 3-cocycle but not normalized (see NormalizeCocycle)
3coctest:=function(inp)
	local El,om,g1,g2,g3,g4;
	El:=inp[1];
	om:=inp[2];
	for g1 in El do for g2 in El do for g3 in El do for g4 in El do
		if not (om.a(g2,g3,g4)-om.a(g1*g2,g3,g4)+om.a(g1,g2*g3,g4)-om.a(g1,g2,g3*g4)+om.a(g1,g2,g3)) mod om.N = 0 then
			return false;
		fi;
	od; od; od; od; 
	if not IsNormalizedCocycle(El,om) then
		Info(InfoWarning,1,"3coctest: om is a 3-cocycle but not normalized; NormalizeCocycle(G,om) gives a cohomologous normalized one");
		return false;
	fi;
	return true;
end;


#UCTInvariants: HAP's UCT record of TR in degree n and the invariant factors of its cocycle basis
#in: TR=TensorWithIntegers(R), R a resolution of a finite group, and n=2 or 3
#out: [UCT,Homol] (Smith form; Homology can give primary factors, Mignard-Schauenburg Rem. 2.4); not for the trivial group
UCTInvariants:=function(TR,n)
	local UCT;
	UCT:=UniversalCoefficientsTheorem(TR,n);
	return [UCT,Filtered(UCT.torsion,x->x<>1)];
end;

#omf: representatives of H^3(F,U(1))
#in: F a finite group
#out: a list of records rec(a,N,G:=F), one normalized additive 3-cocycle per class (all |H^3| classes: for C2^5, 2^25; use omaut or H3Cocycle)
omf:=function(F)
	local R,TR,Homol,UCT,N,sols,3coc,coeffs,coeff,g1,g2,g3,tt,ElF,
		ftabs,ftabt,ftabtt,ftab,i,tables,table,makecoc,result;
	makecoc:=function(tab,modulus,elements)
		local pos,i;
		pos:=NewDictionary(elements[1],true);
		for i in [1..Length(elements)] do AddDictionary(pos,elements[i],i); od;
		return rec(a:=function(g1,g2,g3)
			return tab[LookupDictionary(pos,g1)][LookupDictionary(pos,g2)][LookupDictionary(pos,g3)];
		end,N:=modulus,G:=F);
	end;
	if Size(F)=1 then return [rec(a:=function(g1,g2,g3) return 0; end,N:=1,G:=F)]; fi;
	R:=ResolutionFiniteGroup(F,4);
	TR:=TensorWithIntegers(R);
	UCT:=UCTInvariants(TR,3); Homol:=UCT[2]; UCT:=UCT[1];
	ElF:=Elements(F);
	if not Homol=[] then
		N:=UCT.exponent;
		sols:=UCT.cocyclebasis;
		ftabs:=[];
		for i in [1..Length(sols)] do
			3coc:=StandardCocycle(R,sols[i],3,N);
			ftab:=[];
			for g1 in ElF do ftabt:=[];
				for g2 in ElF do ftabtt:=[];
					for g3 in ElF do
						Add(ftabtt,3coc(g1,g2,g3));
					od;
					Add(ftabt,ftabtt);
				od;
				Add(ftab,ftabt);
			od;
			Add(ftabs,ftab);
		od;
		coeffs:=[];
		coeff:=List([1..Length(Homol)],x->0);	
		Add(coeffs,coeff);	
		while not coeff=List(Homol,x->x-1) do
			coeff:=add1(coeff,List(Homol,x->x-1));
			Add(coeffs,coeff);
		od;
		if not Length(Union([coeffs]))=Product(Homol) then ErrorNoReturn("wrong coeffs for Homol"); fi;
		tables:=[];
		for coeff in coeffs do
			table:=[];
			for g1 in [1..Length(ElF)] do
				ftabt:=[];
				for g2 in [1..Length(ElF)] do
					ftabtt:=[];
					for g3 in [1..Length(ElF)] do
						Add(ftabtt,Sum([1..Length(Homol)],tt->
							coeff[tt]*ftabs[tt][g1][g2][g3]) mod N);
					od;
					Add(ftabt,ftabtt);
				od;
				Add(table,ftabt);
			od;
			Add(tables,table);
		od;
		else 	
			N:=1;
			tables:=[List(ElF,g1->List(ElF,g2->List(ElF,g3->0)))];
	fi;
	#HAP standard cocycles: 3-cocycles by construction, not tested here (|F|^4 per class)
	return List(tables,tab->makecoc(tab,N,ElF));
end;

#omaut: representatives of H^3(F,U(1)) up to automorphisms of F
#in: F a finite group
#out: a list of records rec(a,N,G:=F), one normalized additive 3-cocycle per H^3(F,U(1)) class up to automorphisms of F
omaut:=function(F)
	local ElF,coc,3coc,ftabs,i,ftab,ftabt,ftabtt,g1,g2,g3,makecoc;
	makecoc:=function(tab,modulus,elements)
		local pos,i;
		pos:=NewDictionary(elements[1],true);
		for i in [1..Length(elements)] do AddDictionary(pos,elements[i],i); od;
		return rec(a:=function(g1,g2,g3)
			return tab[LookupDictionary(pos,g1)][LookupDictionary(pos,g2)][LookupDictionary(pos,g3)];
		end,N:=modulus,G:=F);
	end;
	if Size(F)=1 then return [rec(a:=function(g1,g2,g3) return 0; end,N:=1,G:=F)]; fi;
	coc:=ThreeCocyclesUpToAutomorphism(F);
	ElF:=Elements(F);
	ftabs:=[];
	for i in [1..Length(coc[2])] do
		3coc:=StandardCocycle(coc[1],coc[2][i].vec,3,coc[2][i].exp);
		ftab:=[];
		for g1 in ElF do ftabt:=[];
			for g2 in ElF do ftabtt:=[];
				for g3 in ElF do
					Add(ftabtt,3coc(g1,g2,g3));
				od;
				Add(ftabt,ftabtt);
			od;
			Add(ftab,ftabt);
		od;
		Add(ftabs,ftab);
	od;
	return List([1..Length(ftabs)],i->makecoc(ftabs[i],coc[2][i].exp,ElF));
end;

#3coctestm: tests whether a multiplicative 3-cochain is a normalized 3-cocycle
#in: [El,om] with El a list of group elements and om a multiplicative 3-cocycle function
#out: true if om is a normalized 3-cocycle, false otherwise
3coctestm:=function(inp)
	local El,one,om,g1,g2,g3,g4;
	El:=inp[1];
	if Order(El[1])=1 then one:=El[1]; else one:=Filtered(El,k->Order(k)=1)[1]; fi;
	om:=inp[2];
	for g1 in El do for g2 in El do for g3 in El do for g4 in El do
		if not (om(g2,g3,g4)/om(g1*g2,g3,g4))*(om(g1,g2*g3,g4)/om(g1,g2,g3*g4))*om(g1,g2,g3)=1 then
			return false;
		fi;
	od; od; od; od; 
	for g1 in El do for g2 in El do
		if not (om(one,g1,g2)=1 and om(g1,one,g2)=1 and om(g1,g2,one)=1) then return false; fi;
	od; od;
	return true;
end;

#Show3coc: prints the nonzero values of a 3-cocycle
#in: El a list of group elements and 3coc=rec(a,N) additive
#out: prints the nonzero values as roots of unity, returns nothing
Show3coc:=function(El,3coc)
	local g1,g2,g3;
	for g1 in El do for g2 in El do for g3 in El do
		if not 3coc.a(g1,g2,g3) mod 3coc.N=0 then Print("3coc(",g1,",",g2,",",g3,")=",E(3coc.N)^(3coc.a(g1,g2,g3)),"\n"); fi;
	od; od; od;
end;


#2coctest: tests whether a multiplicative 2-cochain is a 2-cocycle
#in: ElFin a group or its element list, gamma a multiplicative 2-cochain
#out: true if gamma is a 2-cocycle, fail otherwise
2coctest:=function(ElFin,gamma)
	local ElF,t,g1,g2,g3;
	if IsGroup(ElFin) then ElF:=Elements(ElFin); else ElF:=ElFin; fi;
	t:=false;
	for g1 in ElF do for g2 in ElF do for g3 in ElF do
		t:=(gamma(g1,g2)*gamma(g1*g2,g3)=gamma(g1,g2*g3)*gamma(g2,g3));
		if not t=true then return fail; fi;
	od; od; od; 
	if t=true then return true; fi;
end;



#IsTrivial2coc: trivializes a multiplicative 2-cocycle gamma(f1,f2)=c(f1*f2)/(c(f1)*c(f2)) (inverse of the convention of IsCounterterm (07))
#in: [ElF,gamma] or [ElF,gamma,fixed], fixed a list of [element,exponent in units of 1/m], m the root order of the values of gamma
#out: the 1-cochain c as roots of unity indexed like ElF, or fail if gamma is not a coboundary
IsTrivial2coc:=function(inp)
	local ElF,gamma,fixed,n,pos,rows,rhs,f1,f2,t,tt,lg,m,x,c,i;
	ElF:=inp[1];
	gamma:=inp[2];
	n:=Length(ElF);
	pos:=NewDictionary(ElF[1],true);
	for i in [1..n] do AddDictionary(pos,ElF[i],i); od;
	lg:=function(z) local d; d:=DescriptionOfRootOfUnity(z); return d[2]/d[1]; end;
	rows:=[]; rhs:=[];
	#gamma(f1,f2)=c(f1 f2)/(c(f1) c(f2)), exponents in full turns
	for f1 in ElF do for f2 in ElF do
		t:=ListWithIdenticalEntries(n,0);
		t[LookupDictionary(pos,f1)]:=t[LookupDictionary(pos,f1)]-1;
		t[LookupDictionary(pos,f2)]:=t[LookupDictionary(pos,f2)]-1;
		t[LookupDictionary(pos,f1*f2)]:=t[LookupDictionary(pos,f1*f2)]+1;
		Add(rows,t); Add(rhs,lg(gamma(f1,f2)));
	od; od;
	#fixed values are exponents in units of 1/m, m the common root order of the values of gamma
	m:=Lcm(List(Set(List(Cartesian(ElF,ElF),p->gamma(p[1],p[2]))),z->DescriptionOfRootOfUnity(z)[1]));
	if Length(inp)>2 then
		fixed:=inp[3];
		for tt in fixed do
			t:=ListWithIdenticalEntries(n,0);
			t[LookupDictionary(pos,tt[1])]:=1;
			Add(rows,t); Add(rhs,tt[2]/m);
		od;
	fi;
	#exact Hermite-normal-form solver, D the common denominator of the right-hand side (the fixed values can have denominators beyond m)
	x:=SolveModZ(rows,rhs,Lcm(List(rhs,DenominatorRat)));
	if x=fail then return fail; fi;
	c:=List(x,q->E(DenominatorRat(q))^NumeratorRat(q));
	for f1 in ElF do for f2 in ElF do
		if gamma(f1,f2)<>c[LookupDictionary(pos,f1*f2)]/(c[LookupDictionary(pos,f1)]*c[LookupDictionary(pos,f2)]) then
			ErrorNoReturn("IsTrivial2coc: solver returned a non-solution");
		fi;
	od; od;
	if IsBound(fixed) then
		for tt in fixed do
			if c[LookupDictionary(pos,tt[1])]<>E(m*DenominatorRat(tt[2]))^NumeratorRat(tt[2]) then
				ErrorNoReturn("IsTrivial2coc: solver ignored a fixed value");
			fi;
		od;
	fi;
	return c;
end;



#gammatest: tests gamma(g2,g3)gamma(g1,g2g3)=gamma(g1g2,g3)gamma(g1,g2)omega(g1,g2,g3) and normalization
#in: F a group, omega=rec(a,N) additive, gamma a multiplicative 2-cochain
#out: true or false
gammatest:=function(F,omega,gamma)
	local ElF,one,omegam,g1,g2,g3;
	ElF:=Elements(F);
	one:=One(F);
	omegam:=function(g1,g2,g3)
		return E(omega.N)^omega.a(g1,g2,g3);
	end;
	for g1 in ElF do
		if not (gamma(one,g1)=1 and gamma(g1,one)=1) then
			return false;
		fi;
	od;
	for g1 in ElF do for g2 in ElF do for g3 in ElF do
		if not gamma(g2,g3)*gamma(g1,g2*g3)=
			gamma(g1*g2,g3)*gamma(g1,g2)*omegam(g1,g2,g3) then
			return false;
		fi;
	od; od; od;
	return true;
end;

#GammaTrivialization: one trivialization gamma0 of omega restricted to F (equations only for g3 in a generating set, which suffice for a normalized omega)
#in: F a group and omega=rec(a,N) an additive normalized 3-cocycle
#out: a normalized multiplicative gamma0 with d(gamma0)=omega|F, or fail if omega|F is not a coboundary
GammaTrivialization:=function(F,omega)
	local ElF,El1,S,m,one,pos,pairIdx,rows,rhs,g1,g2,s,t,x,gamma0,i;
	ElF:=Elements(F);
	if Size(F)=1 then return function(g1,g2) return 1; end; fi;
	one:=One(F);
	#unknowns gamma(a,b) for a,b<>1 only: gamma(1,b)=gamma(a,1)=1 (normalized)
	El1:=Filtered(ElF,g->g<>one);
	m:=Length(El1);
	pos:=NewDictionary(one,true);
	for i in [1..m] do AddDictionary(pos,El1[i],i); od;
	pairIdx:=function(a,b) return (LookupDictionary(pos,a)-1)*m+LookupDictionary(pos,b); end;
	#d(gamma)=omega on (g1,g2,s), s in a generating set S, implies it on F^3 (omega a normalized 3-cocycle); the triples with an entry 1 hold automatically
	S:=Filtered(SmallGeneratingSet(F),s->s<>one);
	rows:=[]; rhs:=[];
	#gamma(g2,s)gamma(g1,g2s)=gamma(g1g2,s)gamma(g1,g2)omega(g1,g2,s), exponents in full turns; a term with an entry 1 is 0
	for g1 in El1 do for g2 in El1 do for s in S do
		t:=ListWithIdenticalEntries(m^2,0);
		t[pairIdx(g2,s)]:=t[pairIdx(g2,s)]+1;
		if g2*s<>one then t[pairIdx(g1,g2*s)]:=t[pairIdx(g1,g2*s)]+1; fi;
		if g1*g2<>one then t[pairIdx(g1*g2,s)]:=t[pairIdx(g1*g2,s)]-1; fi;
		t[pairIdx(g1,g2)]:=t[pairIdx(g1,g2)]-1;
		Add(rows,t); Add(rhs,omega.a(g1,g2,s)/omega.N);
	od; od; od;
	#exact Hermite-normal-form solver (D=omega.N); fail means omega|F is not a coboundary
	x:=SolveModZ(rows,rhs,omega.N);
	if x=fail then
		return fail;
	fi;
	gamma0:=function(g1,g2)
		local q;
		if g1=one or g2=one then return 1; fi;
		q:=x[pairIdx(g1,g2)];
		return E(DenominatorRat(q))^NumeratorRat(q);
	end;
	#d(gamma0)=omega on all of F^3: d(gamma0)/omega is a normalized 3-cocycle equal to 1 at every (g1,g2,s), s in S, so the cocycle condition at (g1,g2,g3,s) gives it at (g1,g2,g3 s) and by induction everywhere (not tested here)
	return gamma0;
end;

#GammaH2Representatives: representatives of H^2(F,U(1))
#in: F a finite group
#out: a list of normalized multiplicative 2-cocycles, one per class
GammaH2Representatives:=function(F)
	local ElF,pos,genF,R,TR,Homol,UCT,N,sols,ftabs,i,coc,ftab,ftabt,
		g1,g2,coeffs,coeff,reps;
	if Size(F)=1 then return [function(g1,g2) return 1; end]; fi;
	ElF:=Elements(F);
	pos:=NewDictionary(ElF[1],true);
	for i in [1..Length(ElF)] do AddDictionary(pos,ElF[i],i); od;
	if StructureDescription(F)="C2 x C2" then
		genF:=IndependentGeneratorsOfAbelianGroup(F);
		return [
			function(g1,g2) return 1; end,
			function(g1,g2)
				if [g1,g2] in [[genF[1],genF[2]],
					[genF[1],genF[1]*genF[2]],
					[genF[1]*genF[2],genF[2]],
					[genF[1]*genF[2],genF[1]*genF[2]]] then
					return -1;
				fi;
				return 1;
			end
		];
	fi;
	R:=ResolutionFiniteGroup(F,3);
	TR:=TensorWithIntegers(R);
	UCT:=UCTInvariants(TR,2); Homol:=UCT[2]; UCT:=UCT[1];
	if Homol=[] then
		return [function(g1,g2) return 1; end];
	fi;
	N:=UCT.exponent;
	sols:=UCT.cocyclebasis;
	ftabs:=[];
	for i in [1..Length(sols)] do
		coc:=StandardCocycle(R,sols[i],2,N);
		ftab:=[];
		for g1 in ElF do
			ftabt:=[];
			for g2 in ElF do
				Add(ftabt,coc(g1,g2));
			od;
			Add(ftab,ftabt);
		od;
		Add(ftabs,ftab);
	od;
	coeffs:=[];
	coeff:=List(Homol,x->0);
	Add(coeffs,coeff);
	while not coeff=List(Homol,x->x-1) do
		coeff:=add1(coeff,List(Homol,x->x-1));
		Add(coeffs,coeff);
	od;
	if Length(Set(coeffs))<>Product(Homol) then
		ErrorNoReturn("GammaH2Representatives: incomplete coefficient product");
	fi;
	reps:=List(coeffs,c->function(g1,g2)
		local exponent,j;
		exponent:=0;
		for j in [1..Length(Homol)] do
			exponent:=exponent+c[j]*ftabs[j][LookupDictionary(pos,g1)][LookupDictionary(pos,g2)];
		od;
		return E(N)^exponent;
	end);
	#HAP standard 2-cocycles: 2-cocycles by construction, not tested here
	return reps;
end;

#gammaf: all normalized trivializations gamma of omega restricted to F, one per class of H^2(F,U(1))
#in: a group F, or [F,omega] with omega=rec(a,N) an additive normalized 3-cocycle (as from omf or omaut)
#out: the list of gamma with d(gamma)=omega|F, or fail when omega|F is not a coboundary
gammaf:=function(inp)
	local F,omega,ElF,trivial,gamma0,reps,gammas;
	if IsGroup(inp) then
		F:=inp;
		omega:=rec(a:=function(g1,g2,g3) return 0; end,N:=1);
		trivial:=true;
	else
		F:=inp[1];
		omega:=inp[2];
		ElF:=Elements(F);
		trivial:=ForAll(ElF,g1->ForAll(ElF,g2->ForAll(ElF,g3->omega.a(g1,g2,g3) mod omega.N=0)));
	fi;
	if trivial then
		gamma0:=function(g1,g2) return 1; end;
	else
		gamma0:=GammaTrivialization(F,omega);
		if gamma0=fail then
			return fail;
		fi;
	fi;
	reps:=GammaH2Representatives(F);
	if Length(reps)=1 then
		gammas:=[gamma0];
	else
		gammas:=List(reps,coc->function(g1,g2)
			return gamma0(g1,g2)*coc(g1,g2);
		end);
	fi;
	#d(gamma0*beta)=d(gamma0)=omega for every 2-cocycle beta (not tested here)
	return gammas;
end;


#Nice3coc: regauges omega so that every gamma of the algebras is a genuine 2-cocycle
#in: [CAG,om] or [CAG,om,"stop"] with CAG a list of algebras and om=rec(a,N) additive ("stop": one regauging step only)
#out: [CAG,om] regauged (with "stop": that step's output); errors if the iteration cycles or does not converge
Nice3coc:=function(inp)
	local oneiter,nit,inpt,inpnew,seen,key;
	#one iteration
	oneiter:=function(inp)
		local CAG,G,op,ElG,posG,A,om,Fs,F,ElF,gamma,gammaF,gammas,Ugamma,f1,f2,rst,m,rs,ga,g1,g2,g3,t,lcm,ftab,ftabt,ftabtt,omnew,CAGnew,omtest;
		CAG:=inp[1];
		G:=CAG[1][5];
		ElG:=Elements(G);
		posG:=NewDictionary(ElG[1],true);
		for g1 in [1..Length(ElG)] do AddDictionary(posG,ElG[g1],g1); od;
		om:=inp[2];

		if Length(inp)>2 then
			op:=inp[3];
		else
			op:="";
		fi;
	
		Fs:=[];
		gammaF:=[];
		gammas:=[];
		for A in CAG do
			F:=A[2];
			gamma:=A[3];
			if (not F in Fs) then
				Add(Fs,F);
				if 2coctest(F,gamma)=fail then
					Add(gammaF,F);
					Add(gammas,gamma);
				fi;
			fi;
		od;
	
		if gammaF=[] then return true;
		else
			if not Length(gammaF)=1 then 
				Print("call this function again with new omega and new CAG\n");
			fi;
			ElF:=Elements(gammaF[1]);
			gamma:=gammas[1];
	
			Ugamma:=[];
			for f1 in ElF do for f2 in ElF do 
				t:=gamma(f1,f2);
				if not t in Ugamma then Add(Ugamma,t); fi;
			od; od;
			rst:=List(Ugamma,x->DescriptionOfRootOfUnity(x));
			m:=Lcm(List(rst,x->x[1]));
			rs:=List(rst,r->(m/r[1])*r[2]);
			#gamma in additive notation
			ga:=function(f1,f2)
				local tt;
				if f1 in gammaF[1] and f2 in gammaF[1] then
					tt:=gamma(f1,f2);
					if tt=1 then return 0;
						else return rs[Position(Ugamma,tt)]; 
					fi;
				else return 0;
				fi;
			end;
	
			ftab:=[];
			lcm:=Lcm(om.N,m);
			for g1 in ElG do ftabt:=[];
				for g2 in ElG do ftabtt:=[];
					for g3 in ElG do
						Add(ftabtt,((lcm/om.N)*om.a(g1,g2,g3)+(lcm/m)*(-ga(g2,g3)-ga(g1,g2*g3)+ga(g1,g2)+ga(g1*g2,g3))) mod lcm);
					od;
					Add(ftabt,ftabtt);
				od;
				Add(ftab,ftabt);
			od;
	
			omnew:=rec(a:=function(g1,g2,g3) return ftab[LookupDictionary(posG,g1)][LookupDictionary(posG,g2)][LookupDictionary(posG,g3)]; end, N:=lcm);
			omtest:=rec(a:=function(g1,g2,g3) return (Lcm(om.N,omnew.N)/om.N)*om.a(g1,g2,g3)-(Lcm(om.N,omnew.N)/omnew.N)*omnew.a(g1,g2,g3); end, N:=Lcm(om.N,omnew.N));
			if gammaf([G,omtest])=fail then ErrorNoReturn("wrong cohom class"); fi;
			Print("omnew computed\n");
			if op="stop" then
				return omnew;
			else
				CAGnew:=AlgebraData(rec(G:=G,om:=omnew));	
			fi;
			return [CAGnew,omnew];
		fi;
	end;

	#no algebras: nothing to regauge
	if inp[1]=[] then return inp; fi;
	inpt:=inp;

	seen:=[];
	for nit in [1..100] do
		key:=[inpt[2].N,List(Cartesian(Elements(inpt[1][1][5]),
			Elements(inpt[1][1][5]),Elements(inpt[1][1][5])),
			x->inpt[2].a(x[1],x[2],x[3]))];
		if key in seen then ErrorNoReturn("Nice3coc: iteration cycled"); fi;
		Add(seen,key);
		inpnew:=oneiter(inpt);
		if inpnew=true then return inpt; fi;
		if Length(inp)>2 and inp[3]="stop" then return inpnew; fi;
		inpt:=inpnew;
	od;
	ErrorNoReturn("Nice3coc: iteration did not converge");
end;

#IsNormalizedCocycle: tests whether an additive 3-cochain is normalized
#in: (El,om) with El = list of the elements of a group and om = additive 3-cochain rec(a,N)
#out: true if om(1,g,h), om(g,1,h) and om(g,h,1) are 0 mod N for all g,h in El, false otherwise
IsNormalizedCocycle:=function(El,om)
	local one;
	one:=One(El[1]);
	return ForAll(El,g->ForAll(El,h->om.a(one,g,h) mod om.N=0 and om.a(g,one,h) mod om.N=0 and om.a(g,h,one) mod om.N=0));
end;

#NormalizeCocycle: a normalized 3-cocycle om-d(beta) in the class of om, beta solved by SolveModZ (not called by the package)
#in: G a finite group and om=rec(a,N) an additive 3-cocycle of G
#out: om if normalized, otherwise a new rec(a,N') with the same class, with a warning
NormalizeCocycle:=function(G,om)
	local ElG,n,one,pos,pairIdx,trip,tr,rows,rhs,t,x,beta,D,c,tab,g1,g2,g3,i,new;
	ElG:=Elements(G);
	if IsNormalizedCocycle(ElG,om) then return om; fi;
	n:=Length(ElG);
	one:=One(G);
	pos:=NewDictionary(ElG[1],true);
	for i in [1..n] do AddDictionary(pos,ElG[i],i); od;
	pairIdx:=function(a,b) return (LookupDictionary(pos,a)-1)*n+LookupDictionary(pos,b); end;
	#the triples with an entry equal to 1
	trip:=Set(Concatenation(List(ElG,g->Concatenation(List(ElG,h->[[one,g,h],[g,one,h],[g,h,one]])))));
	rows:=[]; rhs:=[];
	for tr in trip do
		g1:=tr[1]; g2:=tr[2]; g3:=tr[3];
		t:=ListWithIdenticalEntries(n^2,0);
		t[pairIdx(g2,g3)]:=t[pairIdx(g2,g3)]+1;
		t[pairIdx(g1*g2,g3)]:=t[pairIdx(g1*g2,g3)]-1;
		t[pairIdx(g1,g2*g3)]:=t[pairIdx(g1,g2*g3)]+1;
		t[pairIdx(g1,g2)]:=t[pairIdx(g1,g2)]-1;
		Add(rows,t); Add(rhs,om.a(g1,g2,g3)/om.N);
	od;
	x:=SolveModZ(rows,rhs,om.N);
	if x=fail then ErrorNoReturn("NormalizeCocycle: no normalizing 2-cochain, om is not a 3-cocycle"); fi;
	beta:=function(a,b) return x[pairIdx(a,b)]; end;
	#om-d(beta) in turns, written over the common denominator D
	D:=Lcm(Concatenation([om.N],List(x,DenominatorRat)));
	tab:=List(ElG,g1->List(ElG,g2->List(ElG,g3->
		((om.a(g1,g2,g3)/om.N-(beta(g2,g3)-beta(g1*g2,g3)+beta(g1,g2*g3)-beta(g1,g2)))*D) mod D)));
	#smallest modulus that keeps the values integral: divide D and every value by their common divisor c
	c:=Gcd(Concatenation([D],Set(Flat(tab))));
	D:=D/c;
	tab:=List(tab,l2->List(l2,l1->List(l1,a->a/c)));
	new:=rec(N:=D,G:=G);
	new.a:=function(g1,g2,g3)
		return tab[LookupDictionary(pos,g1)][LookupDictionary(pos,g2)][LookupDictionary(pos,g3)];
	end;
	if not IsNormalizedCocycle(ElG,new) then ErrorNoReturn("NormalizeCocycle: internal error, result not normalized"); fi;
	Info(InfoWarning,1,"NormalizeCocycle: returning the cohomologous normalized cocycle omega-d(beta)");
	return new;
end;

#H3Invariants: the coordinates of H^3(G,U(1)) used by H3Cocycle
#in: G a finite group
#out: [n1,...,nr] with H^3(G,U(1)) = H_3(G,Z) = Z_n1 x ... x Z_nr in the HAP basis of omf ([] when H^3 is trivial)
H3Invariants:=function(G)
	if Size(G)=1 then return []; fi;
	return UCTInvariants(TensorWithIntegers(ResolutionFiniteGroup(G,4)),3)[2];
end;

#H3Cocycle: the additive 3-cocycle of a class of H^3(G,U(1)) given by its coordinates
#in: G a finite group and v a list with one integer per H3Invariants(G) (v=0 or [] trivial), or rec(a,N[,G]) (returned untested)
#out: rec(a,N,G) additive, the table of omf(G)[k] for the k with coefficient vector v; error if v.G is another group object
H3Cocycle:=function(G,v)
	local R,TR,Homol,UCT,N,ElG,pos,cocs,tab,om,i;
	if IsRecord(v) then
		#the tables are indexed by the elements of v.G: a copy of G (e.g. SmallGroup called again) does not work
		if IsBound(v.G) and not IsIdenticalObj(v.G,G) then
			ErrorNoReturn("H3Cocycle: omega was built on another copy of the group; build it from this G, e.g. omaut(MakeGroup(...))");
		fi;
		return v;
	fi;
	if Size(G)=1 then
		if not (v=0 or v=[]) then ErrorNoReturn("H3Cocycle: H^3 of the trivial group is 0, give v=0 or []"); fi;
		return rec(a:=function(g1,g2,g3) return 0; end,N:=1,G:=G);
	fi;
	R:=ResolutionFiniteGroup(G,4);
	TR:=TensorWithIntegers(R);
	UCT:=UCTInvariants(TR,3); Homol:=UCT[2]; UCT:=UCT[1];
	if v=0 or v=[] then v:=List(Homol,x->0); fi;
	if not (IsList(v) and Length(v)=Length(Homol) and ForAll(v,IsInt)) then
		ErrorNoReturn("H3Cocycle: H^3(G,U(1)) has invariants ",Homol,", give one integer per invariant");
	fi;
	ElG:=Elements(G);
	if Homol=[] then
		return rec(a:=function(g1,g2,g3) return 0; end,N:=1,G:=G);
	fi;
	N:=UCT.exponent;
	cocs:=List(UCT.cocyclebasis,s->StandardCocycle(R,s,3,N));
	v:=List([1..Length(Homol)],t->v[t] mod Homol[t]);
	#the zero vector gives the zero table: skip the |G|^3 table and the |G|^4 cocycle test
	if ForAll(v,x->x=0) then
		return rec(a:=function(g1,g2,g3) return 0; end,N:=1,G:=G);
	fi;
	tab:=List(ElG,g1->List(ElG,g2->List(ElG,g3->
		Sum([1..Length(Homol)],t->v[t]*cocs[t](g1,g2,g3)) mod N)));
	pos:=NewDictionary(ElG[1],true);
	for i in [1..Length(ElG)] do AddDictionary(pos,ElG[i],i); od;
	om:=rec(a:=function(g1,g2,g3)
		return tab[LookupDictionary(pos,g1)][LookupDictionary(pos,g2)][LookupDictionary(pos,g3)];
	end,N:=N,G:=G);
	#HAP standard cocycle, as in omf: not tested here
	return om;
end;

#TQDTheory: the data of Z(Vec_G^omega) used by the other routines, computed once
#in: (G[,v[,opts]]), v as in H3Cocycle (default trivial), opts optional fields ST:=true (S,T matrices; data:=true too), glG, bos:=true
#out: rec(G,glG,aG,labels,H3,[om],[S,T]); om bound only for a nontrivial cocycle, S and T only with ST:=true
TQDTheory:=function(arg)
	local G,v,opts,th,inp,res,ElG;
	G:=MakeGroup(arg[1]);
	if Length(arg)>1 then v:=arg[2]; else v:=0; fi;
	if Length(arg)>2 then opts:=arg[3]; else opts:=rec(); fi;
	th:=rec(G:=G,H3:=H3Invariants(G));
	if IsBound(opts.glG) then th.glG:=opts.glG; else th.glG:=MakeGroupLabels([G]); fi;
	ElG:=Elements(G);
	v:=H3Cocycle(G,v);
	#the existing routines take the untwisted code path only when om is absent
	if v.N<>1 and ForAny(ElG,g1->ForAny(ElG,g2->ForAny(ElG,g3->v.a(g1,g2,g3) mod v.N<>0))) then th.om:=v; fi;
	inp:=rec(G:=G,glG:=th.glG);
	if IsBound(th.om) then inp.om:=th.om; fi;
	if IsBound(opts.bos) then inp.bos:=opts.bos; fi;
	#S and T only on request (data:=true, the old default, also asks for them)
	if (IsBound(opts.ST) and opts.ST=true) or (IsBound(opts.data) and opts.data=true) then
		inp.opA:="data";
		res:=Anyons(inp);
		th.aG:=res.aG; th.S:=res.S; th.T:=res.T;
	else
		th.aG:=Anyons(inp);
	fi;
	th.labels:=AnyonLabelStrings(th.aG);
	return th;
end;

#ShowTQDTheory: construct a theory, print all its anyons and fusion rules, and return it
#in: (G[,v[,opts]]) as for TQDTheory, with ST:=true enforced so fusion is available
#out: the record returned by TQDTheory
ShowTQDTheory:=function(arg)
	local G,v,opts,th;
	G:=arg[1];
	if Length(arg)>1 then v:=arg[2]; else v:=0; fi;
	if Length(arg)>2 then opts:=ShallowCopy(arg[3]); else opts:=rec(); fi;
	opts.ST:=true;
	th:=TQDTheory(G,v,opts);
	ShowAnyons(th);
	Print("\n");
	ShowFusion(th);
	return th;
end;

#OmegaArgs: the trailing omega argument of the existing list-input routines
#in: th a record from TQDTheory
#out: [] for trivial omega, [th.om] otherwise, e.g. AlgAnyonsV(Concatenation([A,th.aG],OmegaArgs(th)))
OmegaArgs:=function(th)
	if IsBound(th.om) then return [th.om]; fi;
	return [];
end;
