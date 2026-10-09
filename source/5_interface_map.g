#############################################################################
##
## source/5_interface_map.g           AlgebrasTQD
##
## Maps from algebra data to anyons across interfaces.
##
## Functions in this file (the first line of each header):
## - AlgAnyonsProducts: decomposes an algebra of G = G1 x ... x Gk into the product anyons a1 x ... x ak, ai of Z(Vec_Gi) (eq. (scalar_prod_anyon_decom), Gruen-Morrison (2.10))
## - AlgAnyonsV: decomposes an algebra into anyons (the case k=1 of AlgAnyonsProducts; the direct formula is AlgAnyonsVOld in extra.g)
## - AlgAnyons: decomposes an algebra into anyons and prints the decomposition
## - AlgAnyonsG1G2V: the case k=2 of AlgAnyonsProducts, with the old list input (opA="*" conjugates the second copy only)
## - alphaf: the condensed theory K=H/F of an algebra A(H,F,gamma,eps) and its 3-cocycle alpha, TwinAlgebras.tex eq. (twist_reduced_TO) with Changes 1.1, 1.2 of ../latex/Twin_Algebras_revision.tex
## - InterfaceMap: the anyon map across the interface of an algebra A(H,F,gamma,eps) of Z(Vec_G^omega) to Z(Vec_K^alpha), K=H/F, read off one folded Lagrangian algebra containing A x A(K,1,1,1) (TwinAlgebras.tex sec. Fold; all maps: AllInterfaceMaps)
## - AlgebrasWithAnyons: every algebra of a theory together with its decomposition into anyons
## - ShowAlgebrasWithAnyons: prints one line per algebra: index, dimension, name, condensed group K, decomposition
## - FindAlgebras: the algebras of a list from AlgebrasWithAnyons with a given anyon content
## - DoubledTheory: (helper) the theory Z(Vec_K^beta) x Z(Vec_K^beta)^rev = Z(Vec_{KxK}^{beta x bar beta}) in which the braided
## - AnyonPermutation: (helper) the anyon permutation of a Lagrangian algebra of the doubled theory, if it is one
## - CheckPermutation: (helper) consistency test of an anyon permutation: a braided autoequivalence preserves the vacuum
## - AutomorphismsAnyons: the braided autoequivalences of a theory Z(Vec_K^beta) and their action on the anyons
## - AutomorphismsDG: the braided autoequivalences of an untwisted double D(G) by Davydov's condition
## - AllInterfaceMaps: all anyon maps of the interfaces defined by an algebra, from the one map of InterfaceMap
##
#############################################################################





#AlgAnyonsProducts: decomposes an algebra of G = G1 x ... x Gk into the product anyons a1 x ... x ak, ai of Z(Vec_Gi) (eq. (scalar_prod_anyon_decom), Gruen-Morrison (2.10))
#in: rec(A:=[H,F,gamma,eps,G], ps:=projections G->Gi, es:=embeddings Gi->G, aGs:=anyons of the Gi, [stars:=k strings "" or "*" ("*" conjugates that copy)], [om:=rec(a,N) on G])
#out: [dimA,na] with na indexed by Cartesian(aG1,...,aGk), aG1 outermost
AlgAnyonsProducts:=function(inp)
	local A,H,F,eps,G,ps,es,aGs,stars,k,Gs,omega,omegam,twisted,dimA,R,Els,chi,na,dimna,tuple,i,x,ccx,ElCGx,f,c,g,t,y,sp,ch,one,fluxCache,W,h,j;
	A:=inp.A;
	H:=A[1]; F:=A[2]; eps:=A[4]; G:=A[5];
	ps:=inp.ps; es:=inp.es; aGs:=inp.aGs;
	k:=Length(aGs);
	if Length(ps)<>k or Length(es)<>k then ErrorNoReturn("AlgAnyonsProducts: ps, es and aGs must have the same length"); fi;
	if IsBound(inp.stars) then stars:=inp.stars; else stars:=ListWithIdenticalEntries(k,""); fi;
	if Length(stars)<>k or not ForAll(stars,s->s in ["","*"]) then
		ErrorNoReturn("AlgAnyonsProducts: stars must be k strings \"\" or \"*\"");
	fi;
	if ForAny(ps,p->Source(p)<>G) then ErrorNoReturn("AlgAnyonsProducts: the projections must start at G=A[5]"); fi;
	Gs:=List(ps,Image);
	if Size(G)<>Product(Gs,Size) then
		ErrorNoReturn("AlgAnyonsProducts: G must be the direct product G1 x ... x Gk of the images of ps (|G| is not |G1|...|Gk|)");
	fi;
	twisted:=IsBound(inp.om);
	if twisted then
		omega:=inp.om;
		omegam:=function(g1,g2,g3) return E(omega.N)^(omega.a(g1,g2,g3)); end;
	fi;
	dimA:=Order(G)*Order(F)/Order(H);
	#representatives of the left cosets yH
	R:=List(RightCosets(G,H),rc->Representative(Inverse(rc)));
	Els:=Union(List(ConjugacyClassSubgroups(G,F),Elements));
	one:=List(Gs,One);
	#character of copy i at h in Gi, conjugated for a "*" copy
	chi:=function(i,a,h)
		if stars[i]="*" then return ComplexConjugate(LookupDictionary(a[2],h)); fi;
		return LookupDictionary(a[2],h);
	end;
	#per flux x, computed once and shared by all anyons (tuples) with flux x: W, the list of [[p1(h),...,pk(h)],w(h)] over h in C_G(x) with w(h)<>0, where w(h) is the sum over f in the class of x (c with f^c=x, g=c h c^-1) of t(f,g), the sum over the cosets yH, times the conjugated phase of Gruen-Morrison (2.10) when twisted; then n_a=sum conj(ch(h))w(h)/|G|
	fluxCache:=NewDictionary(One(G),true,G);
	na:=[];
	dimna:=0;
	for tuple in Cartesian(aGs) do
		x:=Product([1..k],i->es[i](tuple[i][1]));
		#boson test
		if not (IsPosInt(Product([1..k],i->chi(i,tuple[i],tuple[i][1]))) and x in Els) then
			Add(na,0);
		else
			W:=LookupDictionary(fluxCache,x);
			if W=fail then
				ccx:=List(Cartesian(List([1..k],i->es[i](Elements(tuple[i][3])))),Product);
				ElCGx:=List(Cartesian(List([1..k],i->es[i](Elements(Centralizer(Gs[i],tuple[i][1]))))),Product);
				W:=List(ElCGx,h->0);
				for f in ccx do
					if f=x then c:=One(G); else c:=RepresentativeAction(G,f,x); fi;
					for j in [1..Length(ElCGx)] do
						g:=c*ElCGx[j]*Inverse(c);
						t:=0;
						for y in R do
							if (g^y in H) and (f^y in F) then
								if not twisted then
									t:=t+eps(g^y,f^y);
								else
									t:=t+eps(g^y,f^y)*3cocr(omegam,g^y,y^-1,f)/3cocr(omegam,y^-1,g,f);
								fi;
							fi;
						od;
						if t<>0 then
							if (not twisted) or f=x then
								W[j]:=W[j]+t;
							else	#Gruen-Morrison paper (2.10)
								W[j]:=W[j]+ComplexConjugate(theta(omegam,x,c^-1,g)*theta(omegam,x,c^-1*g,c)/theta(omegam,f,c,c^-1))*t;
							fi;
						fi;
					od;
				od;
				W:=List(Filtered([1..Length(ElCGx)],j->W[j]<>0),j->[List([1..k],i->ps[i](ElCGx[j])),W[j]]);
				AddDictionary(fluxCache,x,W);
			fi;
			sp:=0;
			for h in W do
				ch:=Product([1..k],i->chi(i,tuple[i],h[1][i]));
				sp:=sp+ComplexConjugate(ch)*h[2];
			od;
			sp:=sp/Order(G);
			Add(na,sp);
			dimna:=dimna+Product([1..k],i->dima(tuple[i],one[i]))*sp;
		fi;
	od;
	if not (IsNonNegIntv(na) and dimA=dimna) then
		ErrorNoReturn("AlgAnyonsProducts: the multiplicities ",na," are not non-negative integers summing to dim A=",dimA);
	fi;
	return [dimA,na];
end;

#AlgAnyonsV: decomposes an algebra into anyons (the case k=1 of AlgAnyonsProducts; the direct formula is AlgAnyonsVOld in extra.g)
#in: [[H,F,gamma,eps,G],anyons] or [[H,F,gamma,eps,G],anyons,omega] with the algebra from AlgebraData, anyons from Anyons, omega=rec(a,N) additive
#out: [dimA,na] with dimA the algebra dimension and na the multiplicity of each anyon
AlgAnyonsV:=function(inp)
	local G,r;
	G:=inp[1][5];
	r:=rec(A:=inp[1],ps:=[IdentityMapping(G)],es:=[IdentityMapping(G)],aGs:=[inp[2]]);
	if Length(inp)>2 then r.om:=inp[3]; fi;
	return AlgAnyonsProducts(r);
end;

#AlgAnyons: decomposes an algebra into anyons and prints the decomposition
#in: the same as AlgAnyonsV
#out: the same [dimA,na], after printing the decomposition as a sum of anyon labels
AlgAnyons:=function(inp)
	local res,na,lab;
	res:=AlgAnyonsV(inp);
	na:=Last(res);
	lab:=AnyonLabelStrings(inp[2]);
	Print(ShowAlg(na,lab),"\n");
	return res;
end;


#AlgAnyonsG1G2V: the case k=2 of AlgAnyonsProducts, with the old list input (opA="*" conjugates the second copy only)
#in: [[H,F,gamma,eps,G],[[p1,p2,e1,e2,G],aG1,aG2,[opA]]] or the same with omega=rec(a,N) as a third entry
#out: [dimA,na] with na the multiplicities over the product anyons of aG1 and aG2 (aG1 outermost)
AlgAnyonsG1G2V:=function(inp)
	local maps,r;
	maps:=inp[2][1];
	if inp[1][5]<>maps[5] then ErrorNoReturn("AlgAnyonsG1G2V: the algebra group A[5] is not the group of the maps"); fi;
	r:=rec(A:=inp[1],ps:=[maps[1],maps[2]],es:=[maps[3],maps[4]],aGs:=[inp[2][2],inp[2][3]],stars:=["",""]);
	if Length(inp[2])>3 then r.stars[2]:=inp[2][4]; fi;
	if Length(inp)>2 and not IsString(inp[3]) then r.om:=inp[3]; fi;
	return AlgAnyonsProducts(r);
end;


#alphaf: the condensed theory K=H/F of an algebra A(H,F,gamma,eps) and its 3-cocycle alpha, TwinAlgebras.tex eq. (twist_reduced_TO) with Changes 1.1, 1.2 of ../latex/Twin_Algebras_revision.tex
#in: [algebra] or [algebra,omega] with algebra=[H,F,gamma,eps,G] and omega=rec(a,N) additive
#out: [[pG,pK,eG,eK,p],ElK,ala,GK,omfull,Ualm]: ala=rec(a,N) is alpha with the bar on ElK, omfull=omega x bar alpha on GK=GxK, Ualm the values of alpha<>1
alphaf:=function(data)
	local H,F,gamma,eps,G,omega,Uom,t,almtab,almt,p,K,ElK,GK,pG,pK,eG,eK,ElG,preim,sec,s,tau,taup,alm,Ualm,rst,rs,m,ala,lcm,atab,atabt,atabtt,tt,x,y,z,omm;
	H:=data[1][1];
	F:=data[1][2];
	gamma:=data[1][3];
	eps:=data[1][4];
	G:=data[1][5];

	if Length(data)>1 then
		omega:=data[2];
		ElG:=Elements(G);
		#only Uom=[1] (omega identically 0) is tested below; ForAll stops at the first nonzero value
		if ForAll(ElG,g1->ForAll(ElG,g2->ForAll(ElG,g3->omega.a(g1,g2,g3) mod omega.N=0))) then
			Uom:=[1];
		else
			Uom:="not 1";
		fi;
	else
		Uom:=[1];
	fi;


	p:=NaturalHomomorphismByNormalSubgroup(H,F);
	K:=Image(p);
	GK:=DirectProduct(G,K);
	pG:=Projection(GK,1);
	pK:=Projection(GK,2);
	eG:=Embedding(GK,1);
	eK:=Embedding(GK,2);


	ElK:=Elements(K);
	#the section below stores One(H) at position 1, so the identity of K must come first (true for the sorted elements of the pc and perm quotients of GAP); otherwise put it first
	if ElK[1]<>One(K) then ElK:=Concatenation([One(K)],Filtered(ElK,k->k<>One(K))); fi;
	preim:=List(ElK,k->Elements(PreImages(p,k)));
	#one normalized section s of p (s(1)=1)
	sec:=Concatenation([One(H)],List([2..Length(preim)],j->preim[j][1]));
	s:=function(k) return sec[Position(ElK,k)]; end;
	tau:=function(y,z) return s(z)^-1*s(y)^-1*s(y*z); end;
	taup:=function(x,y,z) return s(x*y*z)^-1*s(x)*s(y)*s(x*y)^-1*s(x*y*z); end;
	
	omm:=function(a,b,c) if Uom=[1] then return 1; fi; return E(omega.N)^(omega.a(a,b,c)); end;
	#alpha(x,y,z) of eq. (twist_reduced_TO) with Changes 1.1, 1.2 of Twin_Algebras_revision.tex, factor by factor; yp=s(xy)^-1 s(xyz)=s(z)tau_4 and tp^-1=tau_3^{s(z)tau_4}, with f^g=g^-1 f g
	alm:=function(x,y,z)
		local tp,yp;
		tp:=taup(x,y,z); yp:=s(x*y)^-1*s(x*y*z);
		return omm(s(x),s(y),s(y)^-1*s(x)^-1*s(x*y*z))*gamma(tau(y,z),tau(x,y*z))/gamma(tau(x*y,z),tp^-1)
			*eps(yp,tp^-1)*omm(s(x)*s(y),tau(x,y),yp)*omm(s(z),tau(x*y,z),tp^-1)
			/(omm(s(y),s(y)^-1*s(y*z),tau(x,y*z))*omm(s(z),tau(y,z),tau(x,y*z))*omm(s(x),s(y),tau(x,y)));
	end;
	#alm once per triple: almtab[i][j][k]=alm(ElK[i],ElK[j],ElK[k]), almt reads the table
	almtab:=List(ElK,k1->List(ElK,k2->List(ElK,k3->alm(k1,k2,k3))));
	almt:=function(x,y,z) return almtab[Position(ElK,x)][Position(ElK,y)][Position(ElK,z)]; end;
	#the values different from 1, in the order of the triples
	Ualm:=[];
	for t in Flat(almtab) do
		if t<>1 and not t in Ualm then Add(Ualm,t); fi;
	od;
	#alpha identically 1 (Ualm=[]) is a normalized 3-cocycle; otherwise test the cocycle condition and normalization once
	if Ualm<>[] and 3coctestm([ElK,almt])=false then
		ErrorNoReturn("alphaf: eq. (twist_reduced_TO) gave no normalized 3-cocycle for ",
			StructureDescription(G), " with H=", StructureDescription(H),
			" and F=", StructureDescription(F));
	fi;
	if Ualm=[] then			
		if Uom=[1] then
			return [[pG,pK,eG,eK,p], ElK, rec(a:=function(x,y,z) return 0; end, N:=1), GK, rec(a:=function(x,y,z) return 0; end, N:=1), Ualm];
		else
			return [[pG,pK,eG,eK,p], ElK, rec(a:=function(x,y,z) return 0; end, N:=1), GK, rec(a:=function(x,y,z) return omega.a(pG(x),pG(y),pG(z)); end, N:=omega.N), Ualm];
		fi;
	else
		rst:=List(Ualm,DescriptionOfRootOfUnity);
		m:=Lcm(List(rst,r->r[1]));
		rs:=List(rst,r->(m/r[1])*r[2]);
		#alpha in additive notation
		atab:=[];
		for x in ElK do
			atabt:=[];
			for y in ElK do
				atabtt:=[];
				for z in ElK do
					tt:=almt(x,y,z);
					if tt=1 then
						Add(atabtt,0);
					else
						Add(atabtt,-rs[Position(Ualm,tt)]);  #here - is the bar
					fi;
				od;
				Add(atabt,atabtt);
			od;
			Add(atab,atabt);
		od;
		ala:=function(x,y,z)
			return (atab[Position(ElK,x)][Position(ElK,y)][Position(ElK,z)]) mod m;
		end;
		#pullback test p^*alpha ~ omega|H, not called:
		#pbtest:=function() local pala,lcm; if Uom=[1] then pala:=rec(a:=function(g1,g2,g3) return ala(p(g1),p(g2),p(g3)); end, N:=m); else lcm:=Lcm(omega.N,m); pala:=rec(a:=function(g1,g2,g3) return ((lcm/omega.N)*omega.a(g1,g2,g3)+(lcm/m)*ala(p(g1),p(g2),p(g3))) mod lcm; end, N:=lcm); fi; if gammaf([H,pala])=fail then return false; else return true; fi; end; ala is the bar of alm, already tested by 3coctestm above
		if Uom=[1] then
			return [[pG,pK,eG,eK,p], ElK, rec(a:=ala, N:=m), GK, rec(a:=function(x,y,z) return ala(pK(x),pK(y),pK(z)); end, N:=m), Ualm];
		else
			lcm:=Lcm(omega.N,m);
			return [[pG,pK,eG,eK,p], ElK, rec(a:=ala, N:=m), GK, rec(a:=function(x,y,z) return ((lcm/omega.N)*omega.a(pG(x),pG(y),pG(z))+(lcm/m)*ala(pK(x),pK(y),pK(z))) mod lcm; end, N:=lcm), Ualm];
		fi;
	fi;
end;




#InterfaceMap: the anyon map across the interface of an algebra A(H,F,gamma,eps) of Z(Vec_G^omega) to Z(Vec_K^alpha), K=H/F, read off one folded Lagrangian algebra containing A x A(K,1,1,1) (TwinAlgebras.tex sec. Fold; all maps: AllInterfaceMaps)
#in: (th,A[,opts]) with th from TQDTheory (or a record with aG, [om], [glG]), A an algebra [H,F,gamma,eps,G] or a record from AlgebrasWithAnyons, and opts a record with optional fields alpha (alphaf output), gen (elements of H giving m1, m2, ... of an untwisted abelian K), glK, aK (anyons of K built with opA:="*" and om:=ala)
#out: rec(m,aK,labK,K,ala,L,c) after printing the map: m[b][a] rows aK (barred, theta(b)=conj(theta(a)) for dim A>1), columns aG, row 1 = decomposition of A; dim A=1: m identity, aK=aG; Lagrangian: m=[na], aK=fail
InterfaceMap:=function(arg)
	local inp,f,H,F,gamma,eps,G,aG,om,zero,lab,thA,naA,dimA,out,pG,pK,eG,eK,p,ElK,K,ala,GK,omfull,Ualm,glK,gen,aK,labK,
		HL,gammaL,epsres,A,L,c,t,m,printmap,k,pos,cand;
	#the input record of the computation below: the algebra, the anyons, omega and labels of the theory, and the options
	inp:=rec(data:=arg[2],aG:=arg[1].aG);
	if IsRecord(inp.data) then inp.data:=inp.data.A; fi;
	if IsBound(arg[1].om) then inp.om:=arg[1].om; fi;
	if IsBound(arg[1].glG) then inp.glG:=arg[1].glG; fi;
	if Length(arg)>2 then
		for f in RecNames(arg[3]) do inp.(f):=arg[3].(f); od;
	fi;
	H:=inp.data[1]; F:=inp.data[2]; gamma:=inp.data[3]; eps:=inp.data[4]; G:=inp.data[5];
	aG:=inp.aG;
	zero:=rec(a:=function(x,y,z) return 0; end,N:=1);
	if IsBound(inp.om) then om:=inp.om; fi;
	#display labels of an anyon list (AnyonLabelStrings: the stored strings, or joined flux and charge on the abelian (m,e) path)
	lab:=AnyonLabelStrings(aG);
	printmap:=function(m,labK)
		local n;
		Print("\nAnyon mapping:\n");
		for n in [1..Length(m)] do
			if ForAny(m[n],x->x<>0) then Print(labK[n],"  ->  ",ShowAlg(m[n],lab),"\n"); fi;
		od;
		Print("\n");
	end;
	#print the algebra (without its reduced topological order, which is computed below)
	thA:=rec(G:=G,aG:=aG,labels:=lab);
	if IsBound(inp.glG) then thA.glG:=inp.glG; else thA.glG:=MakeGroupLabels([G]); fi;
	if IsBound(om) then thA.om:=om; fi;
	naA:=ShowAlgData(thA,inp.data,rec(reducedTO:=false)).na;
	dimA:=Order(G)*Order(F)/Order(H);

	if dimA=1 then
		#A=A(G,1,1,1): the interface is the identity of Z(Vec_G^omega)
		m:=IdentityMat(Length(aG));
		if m[1]<>naA then ErrorNoReturn("InterfaceMap: vacuum row does not equal algebra decomposition"); fi;
		GK:=DirectProduct(G,G);
		HL:=Group(List(GeneratorsOfGroup(G),k->Embedding(GK,1)(k)*Embedding(GK,2)(k)),One(GK));
		L:=[HL,HL,ftriv,ftriv,GK];
		printmap(m,lab);
		if IsBound(om) then ala:=om; else ala:=zero; fi;
		return rec(m:=m,aK:=aG,labK:=lab,K:=G,ala:=ala,L:=L,c:=fail);
	fi;
	if dimA=Order(G) then
		#Lagrangian algebra: the reduced theory is trivial
		return rec(m:=[naA],aK:=fail,labK:=["1"],K:=TrivialSubgroup(G),ala:=zero,L:=fail,c:=fail);
	fi;

	#reduced theory K=H/F with alpha (stored with the bar) and the folded theory GxK with omfull=omega x bar alpha
	if IsBound(inp.alpha) then out:=inp.alpha;
	elif IsBound(om) then out:=alphaf([inp.data,om]);
	else out:=alphaf([inp.data]);
	fi;
	pG:=out[1][1]; pK:=out[1][2]; eG:=out[1][3]; eK:=out[1][4]; p:=out[1][5];
	#K is the group object of alphaf (Image(p)), not a new group
	ElK:=out[2]; K:=Image(p); ala:=out[3]; GK:=out[4]; omfull:=out[5]; Ualm:=out[6];

	#anyons of the reduced theory, the barred factor of the folded theory (opA:="*"); k in K labelled by its shortest G-label
	if IsBound(inp.glK) then glK:=inp.glK;
	else
		glK:=[ElK,List(ElK,function(k)
			local l;
			l:=List(Elements(PreImages(p,k)),h->thA.glG[2][Position(thA.glG[1],h)]);
			StableSortBy(l,Length);
			return l[1];
		end)];
	fi;
	if IsBound(inp.aK) then aK:=inp.aK;
	else
		aK:=rec(G:=K,opA:="*",glG:=glK);
		if Ualm<>[] then aK.om:=ala; fi;
		if IsBound(inp.gen) then aK.gen:=List(inp.gen,h->p(h));
		elif IsAbelian(K) and Ualm=[] and not IsTrivial(K) then
			#default m1, m2, ...: images of G's generators in H first, then by order and label, kept if independent
			pos:=Filtered([1..Length(ElK)],i->not IsOne(ElK[i]));
			SortBy(pos,i->[-Order(ElK[i]),Length(glK[2][i]),glK[2][i]]);
			cand:=ElK{pos};
			if HasGroupData(G) then cand:=Concatenation(List(Filtered(GroupData(G).gens,g->g in H),g->p(g)),cand); fi;
			gen:=[];
			for k in cand do
				if not IsOne(k) and Size(Group(Concatenation(gen,[k])))=Product(gen,Order)*Order(k) then Add(gen,k); fi;
			od;
			if Product(gen,Order)=Size(K) then aK.gen:=gen; fi;
		fi;
		aK:=Anyons(aK);
	fi;
	labK:=AnyonLabelStrings(aK);
	if Ualm<>[] then Print("Anyons in D^alpha(",StructureDescription(K),"):\n"); else Print("Anyons in D(",StructureDescription(K),"):\n"); fi;
	for k in [1..Length(aK)] do Print("d=",dima(aK[k],One(K)),"\t",labK[k],"\n"); od;

	#A x A(K,1,1,1) in the folded theory (eq. (alg_to_include))
	A:=[Group(Concatenation(eG(Elements(H)),eK(ElK))),eG(F),
		function(g,h) return gamma(pG(g),pG(h)); end,function(g,h) return eps(pG(g),pG(h)); end,GK];
	#the first Lagrangian algebra L(H^diag,phi) of the folded theory that contains it; the inclusion is tested in the folded theory, whose cocycle omfull is also that of L, so it is passed even when omega is trivial (alpha need not be)
	HL:=Group(List(Elements(H),h->eG(h)*eK(p(h))));
	gammaL:=gammaf([HL,omfull]);
	if gammaL=fail then ErrorNoReturn("InterfaceMap: folded cocycle obstructed"); fi;
	L:=fail;
	for t in gammaL do
		epsres:=epsf([HL,HL,t,omfull]);
		if epsres=fail or epsres=[] then ErrorNoReturn("InterfaceMap: no folded epsilon solution"); fi;
		c:=IsSubalgebra(rec(A2:=[HL,HL,t,epsres[1],GK],A1:=A,om:=omfull));
		if not IsString(c) then L:=[HL,HL,t,epsres[1],GK]; break; fi;
	od;
	if L=fail then ErrorNoReturn("InterfaceMap: no folded Lagrangian algebra contains the algebra"); fi;

	#anyon decomposition of L over the products a x b, a in aG, b in aK: m[b][a]
	t:=AlgAnyonsG1G2V([L,[[pG,pK,eG,eK,GK],aG,aK],omfull]);
	if t[1]<>Order(G)*Order(K) then ErrorNoReturn("InterfaceMap: wrong dimension of the folded Lagrangian algebra"); fi;
	m:=TransposedMat(Reshape(t[2],Length(aK)));
	if m[1]<>naA then ErrorNoReturn("InterfaceMap: vacuum row does not equal algebra decomposition"); fi;
	printmap(m,labK);
	return rec(m:=m,aK:=aK,labK:=labK,K:=K,ala:=ala,L:=L,c:=[List(c[1],g->pG(g)),c[2],c[3]]);
end;

#AlgebrasWithAnyons: every algebra of a theory together with its decomposition into anyons
#in: (th[,filter]) with th from TQDTheory and filter as in TQDAlgebras
#out: a list of rec(n,A,name,H,F,K,dim,Lag,na,decomposition,labels), n the position, K=StructureDescription(H/F), na indexed like th.aG
AlgebrasWithAnyons:=function(arg)
	local th,algs,out,A,n,na,dim;
	th:=arg[1];
	algs:=CallFuncList(TQDAlgebras,arg);
	out:=[];
	for n in [1..Length(algs)] do
		A:=algs[n];
		na:=Last(AlgAnyonsV(Concatenation([A,th.aG],OmegaArgs(th))));
		dim:=Order(th.G)*Order(A[2])/Order(A[1]);
		Add(out,rec(n:=n,A:=A,name:=AlgebraName(A,th.glG),H:=A[1],F:=A[2],
			K:=StructureDescription(A[1]/A[2]),dim:=dim,Lag:=dim=Order(th.G),
			na:=na,decomposition:=ShowAlg(na,th.labels),labels:=th.labels));
	od;
	return out;
end;

#ShowAlgebrasWithAnyons: prints one line per algebra: index, dimension, name, condensed group K, decomposition
#in: L a list from AlgebrasWithAnyons
#out: prints the table, returns nothing
ShowAlgebrasWithAnyons:=function(L)
	local r;
	for r in L do
		Print(r.n,"\tdim=",r.dim,"\t",r.name,"\tK=",r.K,"\t",r.decomposition,"\n");
	od;
end;

#FindAlgebras: the algebras of a list from AlgebrasWithAnyons with a given anyon content
#in: (L,q) with q one of rec(decomposition:=string), rec(na:=multiplicity vector), rec(contains:=anyon label or index into th.aG)
#out: the sublist of L matching q
FindAlgebras:=function(L,q)
	local pos;
	if IsBound(q.decomposition) then return Filtered(L,r->r.decomposition=q.decomposition); fi;
	if IsBound(q.na) then return Filtered(L,r->r.na=q.na); fi;
	if IsBound(q.contains) then
		if IsPosInt(q.contains) then
			if L<>[] and q.contains>Length(L[1].na) then
				ErrorNoReturn("FindAlgebras: anyon index ",q.contains," out of range, the theory has ",Length(L[1].na)," anyons");
			fi;
			return Filtered(L,r->r.na[q.contains]>0);
		fi;
		if L=[] then return []; fi;
		pos:=Position(L[1].labels,q.contains);
		if pos=fail then ErrorNoReturn("FindAlgebras: no anyon labelled ",q.contains); fi;
		return Filtered(L,r->r.na[pos]>0);
	fi;
	ErrorNoReturn("FindAlgebras: give rec(decomposition:=...), rec(na:=...) or rec(contains:=...)");
end;

#DoubledTheory: (helper) the theory Z(Vec_K^beta) x Z(Vec_K^beta)^rev = Z(Vec_{KxK}^{beta x bar beta}) in which the braided autoequivalences of Z(Vec_K^beta) are Lagrangian algebras
#in: th = rec(G,aG,[om]) with G = the group K, aG = a list of its anyons (as returned by Anyons, also with opA:="*") and om = the additive 3-cocycle beta=rec(a,N) of the theory (absent, or identically 0 mod N, for an untwisted theory)
#out: rec(K,KK,ps,es,om) with KK=DirectProduct(K,K), ps, es its projections and embeddings, and om the 3-cocycle beta(x1,y1,z1)-beta(x2,y2,z2) on KK (not bound for an untwisted theory)
DoubledTheory:=function(th)
	local K,KK,ps,es,El,beta,r;
	K:=th.G;
	KK:=DirectProduct(K,K);
	ps:=[Projection(KK,1),Projection(KK,2)];
	es:=[Embedding(KK,1),Embedding(KK,2)];
	r:=rec(K:=K,KK:=KK,ps:=ps,es:=es);
	El:=Elements(K);
	if IsBound(th.om) and ForAny(El,x->ForAny(El,y->ForAny(El,z->th.om.a(x,y,z) mod th.om.N<>0))) then
		beta:=th.om;
		r.om:=rec(a:=function(x,y,z)
			return (beta.a(ps[1](x),ps[1](y),ps[1](z))-beta.a(ps[2](x),ps[2](y),ps[2](z))) mod beta.N;
		end,N:=beta.N);
	fi;
	return r;
end;

#AnyonPermutation: (helper) the anyon permutation of a Lagrangian algebra of the doubled theory, if it is one
#in: (th,D,L) with th as in DoubledTheory, D its output and L=[H,H,gamma,eps,KK] a Lagrangian algebra of D.KK
#out: the list p with L = sum_a a x bar(aG[p[a]]), i.e. the decomposition of L over the products aG[a] x aG[b] (second copy conjugated, AlgAnyonsProducts with stars ["","*"]) is 1 for b=p[a] and 0 otherwise; fail if it is not of this form
AnyonPermutation:=function(th,D,L)
	local r,n,na,p,a,b;
	r:=rec(A:=L,ps:=D.ps,es:=D.es,aGs:=[th.aG,th.aG],stars:=["","*"]);
	if IsBound(D.om) then r.om:=D.om; fi;
	na:=AlgAnyonsProducts(r)[2];
	n:=Length(th.aG);
	p:=[];
	for a in [1..n] do
		b:=Positions(na{[(a-1)*n+1..a*n]},1);
		if Length(b)<>1 or ForAny(na{[(a-1)*n+1..a*n]},x->not x in [0,1]) then return fail; fi;
		p[a]:=b[1];
	od;
	if Length(Set(p))<>n then return fail; fi;
	return p;
end;

#CheckPermutation: (helper) consistency test of an anyon permutation: a braided autoequivalence preserves the vacuum and the topological spins theta=chi(g)/chi(1)
#in: (aG,p) with aG a list of anyons and p a permutation of [1..Length(aG)] as a list
#out: nothing; an error if p moves the vacuum or changes a spin
CheckPermutation:=function(aG,p)
	local spin,a;
	spin:=a->LookupDictionary(a[2],a[1])/LookupDictionary(a[2],One(a[1]));
	if p[1]<>1 or ForAny([1..Length(aG)],a->spin(aG[a])<>spin(aG[p[a]])) then
		ErrorNoReturn("the anyon permutation of a braided autoequivalence must fix the vacuum and the spins");
	fi;
end;

#AutomorphismsAnyons: the braided autoequivalences of a theory Z(Vec_K^beta) and their action on the anyons, from the Lagrangian algebras of Z(Vec_K^beta) x Z(Vec_K^beta)^rev whose decomposition is a permutation (Davydov, Mueger, Nikshych, Ostrik, arXiv:1009.2117)
#in: th = rec(G,aG,[om]) as in DoubledTheory: a TQDTheory record, or rec(G:=I.K,aG:=I.aK,om:=I.ala) for the reduced theory of an InterfaceMap record I
#out: a list with one record rec(L,perm) per isomorphism class of such Lagrangian algebras (= per braided autoequivalence up to isomorphism), L=[H,H,gamma,eps,KK] a member of the class (KK=DirectProduct(K,K)) and perm the list with phi(aG[a])=aG[perm[a]], the identity perm=[1..Length(aG)] among them (several L may have the same perm, each perm is checked to fix the vacuum and the spins)
AutomorphismsAnyons:=function(th)
	local D,inp,res,out,cl,p;
	#a braided autoequivalence phi of a modular category C is the Lagrangian algebra sum_a a x bar(phi(a)) of C x C^rev, and the Lagrangian algebras whose decomposition is a permutation (meeting C x 1 and 1 x C only in the vacuum) are exactly these. Here C x C^rev = Z(Vec_{KxK}^{beta x bar beta}), whose Lagrangian algebras are those of AlgebraData up to isomorphism
	D:=DoubledTheory(th);
	if Length(th.aG)=1 then return [rec(L:=[D.KK,D.KK,ftriv,ftriv,D.KK],perm:=[1])]; fi;
	inp:=rec(G:=D.KK,HFtot:=AlgSubgroups(rec(G:=D.KK,op:="Lag")));
	if IsBound(D.om) then inp.om:=D.om; fi;
	res:=AlgebraClassesG(inp);
	out:=[];
	for cl in res[1] do
		p:=AnyonPermutation(th,D,cl[1]);
		if p<>fail then
			CheckPermutation(th.aG,p);
			Add(out,rec(L:=cl[1],perm:=p));
		fi;
	od;
	if not ForAny(out,r->r.perm=[1..Length(th.aG)]) then ErrorNoReturn("AutomorphismsAnyons: the identity is missing"); fi;
	return out;
end;

#AutomorphismsDG: the braided autoequivalences of an untwisted double D(G) by Davydov's condition (Davydov 2009, as quoted in arXiv:2512.13777 Sec. II): the Lagrangian algebras L(K,psi) of D(GxG) with p1(K)=p2(K)=G and eps(g,h)=psi(g,h)/psi(ghg^-1,g) non-degenerate on (K cap Gx1) x (K cap 1xG)
#in: th = rec(G,aG) as in DoubledTheory, untwisted (an error for a nontrivial om)
#out: a list with one record rec(L,K,psi,perm) per isomorphism class of such L(K,psi): L=[K,K,psi,eps,GxG] a member of the class and perm as in AutomorphismsAnyons (an error if the decomposition of one of them is not a permutation)
AutomorphismsDG:=function(th)
	local D,G,HF,res,out,cl,L,K,psi,A,B,epsD,nondeg,p;
	#the anyon permutation of each L(K,psi) is computed as in AutomorphismsAnyons
	D:=DoubledTheory(th);
	if IsBound(D.om) then ErrorNoReturn("AutomorphismsDG: Davydov's condition is for untwisted doubles only"); fi;
	G:=th.G;
	if Length(th.aG)=1 then return [rec(L:=[D.KK,D.KK,ftriv,ftriv,D.KK],K:=D.KK,psi:=ftriv,perm:=[1])]; fi;
	HF:=Filtered(AlgSubgroups(rec(G:=D.KK,op:="Lag")),x->Image(D.ps[1],x[1])=G and Image(D.ps[2],x[1])=G);
	res:=AlgebraClassesG(rec(G:=D.KK,HFtot:=HF));
	out:=[];
	for cl in res[1] do
		L:=cl[1]; K:=L[1]; psi:=L[3];
		A:=Elements(Intersection(K,Image(D.es[1])));
		B:=Elements(Intersection(K,Image(D.es[2])));
		epsD:=function(g,h) return psi(g,h)/psi(g*h*g^-1,g); end;
		nondeg:=Length(A)=Length(B) and
			ForAll(A,g->IsOne(g) or ForAny(B,h->epsD(g,h)<>1)) and ForAll(B,h->IsOne(h) or ForAny(A,g->epsD(g,h)<>1));
		if nondeg then
			p:=AnyonPermutation(th,D,L);
			if p=fail then ErrorNoReturn("AutomorphismsDG: Davydov's condition holds but the decomposition is not a permutation"); fi;
			CheckPermutation(th.aG,p);
			Add(out,rec(L:=L,K:=K,psi:=psi,perm:=p));
		fi;
	od;
	return out;
end;

#AllInterfaceMaps: all anyon maps of the interfaces defined by an algebra, from the one map of InterfaceMap: the folded Lagrangian algebras are related by braided autoequivalences of the reduced theory (TwinAlgebras.tex, after eq. (Afolded)), so the maps are P.m for the permutation matrices P of AutomorphismsAnyons
#in: (I[,auts]) with I a record of InterfaceMap and auts a list of records with field perm, permutations of the rows of I.m (default AutomorphismsAnyons(rec(G:=I.K,aG:=I.aK,om:=I.ala)))
#out: the distinct matrices m' with m'[perm[b]]=I.m[b], as records rec(m,auts) with auts the positions in auts giving m'; the first is I.m itself. For a Lagrangian algebra (I.aK=fail) the list [rec(m:=I.m,auts:=[])]
AllInterfaceMaps:=function(arg)
	local I,auts,out,k,m,b,pos;
	I:=arg[1];
	if I.aK=fail then return [rec(m:=I.m,auts:=[])]; fi;
	if Length(arg)>1 then auts:=arg[2]; else auts:=AutomorphismsAnyons(rec(G:=I.K,aG:=I.aK,om:=I.ala)); fi;
	out:=[rec(m:=I.m,auts:=[])];
	for k in [1..Length(auts)] do
		m:=[];
		for b in [1..Length(I.m)] do m[auts[k].perm[b]]:=I.m[b]; od;
		pos:=PositionProperty(out,r->r.m=m);
		if pos=fail then Add(out,rec(m:=m,auts:=[k])); else Add(out[pos].auts,k); fi;
	od;
	return out;
end;
