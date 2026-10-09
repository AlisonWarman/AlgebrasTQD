#############################################################################
##
## source/4_algebra_data.g             AlgebrasTQD
##
## Epsilon calculations, subgroup enumeration, and algebra data.
##
## Functions in this file (the first line of each header):
## - GammaTest: tests the assumption of epsf on a gamma that does not come from gammaf
## - epsfA: the solutions eps of the epsilon relations for abelian H (the gauge is trivial, all are returned)
## - epsf: the solutions eps of the epsilon relations, one per gauge class eps->eps*c(^h f)/c(f), c in Lin(F)
## - NormalSubgroupReps: the normal subgroups of H up to conjugation by N_G(H)
## - AlgSubgroups: the subgroup pairs (H,F), F normal in H, one per G-conjugacy class of pairs
## - AlgebraData: the algebras A(H,F,gamma,eps) of Z(Vec_G^omega)
## - SubgroupPairs: the subgroup pairs of the algebras of a theory that pass a filter
## - TQDAlgebras: the algebras of a theory that pass a filter
## - AlgebraName: a one-line name of an algebra
## - ShowFgammagl: prints F and the nontrivial values of gamma
## - TeXGroupName: a group name in the notation of TwinAlgebras.tex
## - TeXLabel: a group-element or anyon label in LaTeX (math mode)
## - AlgebraDisplayData: the display data of one algebra of a theory, for ShowAlgData and the LaTeX tables (prints nothing)
## - ShowAlgData: prints one algebra: name, dimension, H/N, reduced TO, anyons (opP:="long": H, N and the values of gamma, eps, alpha)
##
#############################################################################

#GammaTest: tests the assumption of epsf on a gamma that does not come from gammaf
#in: [H,F,gamma] or [H,F,gamma,omega], as for epsf
#out: true if gamma is normalized and d(gamma)=omega|F (omega=1 for three entries), false otherwise
GammaTest:=function(inpdata)
	if Length(inpdata)>3 then
		return gammatest(inpdata[2],inpdata[4],inpdata[3]);
	fi;
	return gammatest(inpdata[2],omtriv,inpdata[3]);
end;

#epsfA: the solutions eps of the epsilon relations for abelian H (the gauge is trivial, all are returned)
#in: [H,F,gamma] or [H,F,gamma,omega], H abelian, gamma a normalized trivialization of omega|F, omega=rec(a,N)
#out: the list of eps(h,f); fail or [] when there is none
epsfA:=function(inpdata)
	local H,F,gamma,ElF,Ugamma,ElD,ElH,Uom,g1,g2,g3,omega,omegam,t,epstest,epsFF,epsFFt,f1,f2,chtabF,clF,chF,genH,genHnotF,h,poss1,poss,beta,betat,kh,sol,Herm,Hermt,v,lb,mtoa,r,roots,rootData,Mv,n1,n2,tocart,n,p,epstabs,known,epstab,i,setvalh1h2,f,epssols,h1,h2,epsnumsfinal,epsnums,epsfinal,khn;
	H:=inpdata[1];
	if not IsAbelian(H) then ErrorNoReturn("H not abelian"); fi;
	F:=inpdata[2];
	gamma:=inpdata[3];
	if Length(inpdata)>3 then
		omega:=inpdata[4];
	else 
		Uom:=[1];
	fi;
	if not (IsGroup(H) and IsGroup(F) and IsSubset(H,F) and IsNormal(H,F)) then
		ErrorNoReturn("epsf: F must be normal in H");
	fi;
	if not IsFunction(gamma) then ErrorNoReturn("epsf: gamma must be a function"); fi;
	#gamma is assumed to be a normalized trivialization of omega|F (omega=1 for 3-argument input), as returned by gammaf (correct by construction). For a gamma from another source call GammaTest(inpdata) first.
	ElF:=Elements(F);
	if ElF=[One(F)] then
		return [function(h,f) return 1; end];  
	fi;
	Ugamma:=Union([List(Cartesian(ElF,ElF),y->gamma(y[1],y[2]))]);	
	#let D=H-F
	ElD:=Difference(Elements(H),ElF);
	ElH:=Concatenation(ElF,ElD);
	if not IsBound(Uom) then
		omegam:=function(g1,g2,g3) return E(omega.N)^(omega.a(g1,g2,g3)); end;
		#only Uom=[1] (omega|H identically 0) is tested below; ForAll stops at the first nonzero value
		if ForAll(ElH,g1->ForAll(ElH,g2->ForAll(ElH,g3->omega.a(g1,g2,g3) mod omega.N=0))) then
			Uom:=[1];
		else
			Uom:="not 1";
		fi;
	fi;	
	#test function for eps
	epstest:=function(eps)
		local test,h1,h2,f1,f2,f,h;
		test:=true;
		if Uom=[1] then
			for h1 in ElH do
				for h2 in ElH do
					for f in ElF do
						test:=(eps(h1*h2,f)=eps(h1,f)*eps(h2,f));
						if test=false then return false; fi; #Print([false,1,h1,h2,f]); return false; fi;
					od;
				od;
			od;
			for f1 in ElF do
				for f2 in ElF do
					for h in ElH do
						test:=(eps(h,f1*f2)=eps(h,f1)*eps(h,f2));
						if test=false then return false; fi; #Print([false,2,f1,f2,h]); return false; fi;
					od;
				od;
			od;
		else
			for h1 in ElH do
				for h2 in ElH do
					for f in ElF do
						test:=(eps(h1*h2,f)=eps(h1,f)*eps(h2,f)*3cocr(omegam,h1,h2,f));
						if test=false then return false; fi; #Print([false,1,h1,h2,f],"om"); return false; fi;
					od;
				od;
			od;
			for f1 in ElF do
				for f2 in ElF do
					for h in ElH do
						test:=(eps(h,f1*f2)=eps(h,f1)*eps(h,f2)*3cocl(omegam,h,f1,f2));
						if test=false then return false; fi; #Print([false,2,h,f1,f2],"om"); return false; fi;
					od;
				od;
			od;
		fi;
		return test;
	end;	

	epsFF:=[];
	for f1 in ElF do
		epsFFt:=[];
		for f2 in ElF do
			if Ugamma=[1] then 
				Add(epsFFt,1);
			else	
				Add(epsFFt,gamma(f1,f2)/gamma(f2,f1)); 
			fi;
		od;
		Add(epsFF,epsFFt);
	od;
				
	if IsEqualSet(ElH,ElF) then
		#eps from gamma solves the epsilon relations when d(gamma)=omega|F (TwinAlgebras.tex App. A), not re-tested: if epstest(function(f1,f2) return epsFF[Position(ElF,f1)][Position(ElF,f2)]; end) then
			return [function(f1,f2) return epsFF[Position(ElF,f1)][Position(ElF,f2)]; end];
		#else ErrorNoReturn("ERROR in Lag eps"); return fail; fi;
	else
		chtabF:=CharacterTable(F);
		clF:=ConjugacyClasses(chtabF);
		chF:=LinearCharacters(chtabF);
		genH:=IndependentGeneratorsOfAbelianGroup(H);
		genHnotF:=[];
		for h in genH do
			if not (h in ElF) then
				Add(genHnotF,h);
			fi;
		od;
		poss1:=List([1..Length(chF)],n->List(ElF,f->chF[n][Posinlist(clF,f)]));
		if Uom=[1] then
			poss:=Cartesian(List([1..Length(genHnotF)],n->poss1));
		else
			kh:=[];
			for h in genHnotF do
				beta:=[];
				for f1 in ElF do betat:=[];
					for f2 in ElF do
						Add(betat,1/3cocl(omegam,h,f1,f2));
					od;
					Add(beta,betat);
				od;
				roots:=Set(Flat(beta));
				rootData:=List(roots,DescriptionOfRootOfUnity);
				lb:=Lcm(List(rootData,r->r[1]));
				mtoa:=function(x)
					local rd;
					rd:=DescriptionOfRootOfUnity(x);
					return (lb/rd[1])*rd[2];
				end;
				#compute trivialiazion of proj 1d irrep
				Mv:=[];
				for n1 in [1..Length(ElF)] do
					for n2 in [1..Length(ElF)] do
						t:=List([1..Length(ElF)],x->0);
						t[n1]:=t[n1]+1;
						t[n2]:=t[n2]+1;
						t[Position(ElF,(ElF[n1])*(ElF[n2]))]:=t[Position(ElF,(ElF[n1])*(ElF[n2]))]-1;
						Add(t,mtoa(beta[n1][n2]));
						Add(Mv,t);
					od;
				od;
				#solve c(f1)+c(f2)-c(f1 f2) = beta(f1,f2) mod 1 (exponents in full turns), exact Hermite-normal-form solver (n=lb)
				sol:=SolveModZ(List(Mv,r->r{[1..Length(ElF)]}),
					List(Mv,r->Last(r)/lb),lb);
				if sol=fail then return fail; fi;
				Add(kh,List(sol,x->E(DenominatorRat(x))^NumeratorRat(x)));
				#kh solves the projective equation: SolveModZ stops with an error otherwise, not re-tested:
				#khn:=Last(kh); if ForAny([1..Length(ElF)],n1->ForAny([1..Length(ElF)],n2-> khn[n1]*khn[n2]/khn[Position(ElF,ElF[n1]*ElF[n2])]<>beta[n1][n2])) then ErrorNoReturn("epsf: solver returned a non-solution for the projective character"); fi;
			od;
			tocart:=[];
			for n in [1..Length(genHnotF)] do
				Add(tocart,TransposedMat(List([1..Length(TransposedMat(poss1))],m->TransposedMat(poss1)[m]*kh[n][m])));
			od;
			poss:=Cartesian(tocart);
		fi;

			epstabs:=[];
			for p in poss do
				known:=Concatenation(ElF,genHnotF);
				epstab:=Concatenation(epsFF,NullMat(Length(ElD),Length(ElF)));
				for i in [1..Length(genHnotF)] do
					epstab[Position(ElH,genHnotF[i])]:=p[i];
				od;
				setvalh1h2:=function(h1,h2)
					if Uom=[1] then
						if h1*h2 in known then
							for f in ElF do
								if not epstab[Position(ElH,h1*h2)][Position(ElF,f)]=epstab[Position(ElH,h1)][Position(ElF,f)]*epstab[Position(ElH,h2)][Position(ElF,f)]
								then return false; 
								fi;
							od;
							else 
							for f in ElF do						
								epstab[Position(ElH,h1*h2)][Position(ElF,f)]:=epstab[Position(ElH,h1)][Position(ElF,f)]*epstab[Position(ElH,h2)][Position(ElF,f)];
							od;	
						fi;
					else
						if h1*h2 in known then
							for f in ElF do
								if not epstab[Position(ElH,h1*h2)][Position(ElF,f)]=epstab[Position(ElH,h1)][Position(ElF,f)]*epstab[Position(ElH,h2)][Position(ElF,f)]*3cocr(omegam,h1,h2,f)
								then return false; 
								fi;
							od;
							else 
							for f in ElF do						
								epstab[Position(ElH,h1*h2)][Position(ElF,f)]:=epstab[Position(ElH,h1)][Position(ElF,f)]*epstab[Position(ElH,h2)][Position(ElF,f)]*3cocr(omegam,h1,h2,f);
							od;	
						fi;

					fi;	
					return [epstab,Union([Concatenation(known,[h1*h2])])];			
				end;
				repeat
					for h1 in Difference(known,[One(H)]) do
						for h2 in genH do
							t:=setvalh1h2(h1,h2);
							if t=false then
								break;
							else epstab:=t[1]; known:=t[2]; fi;
						od;
						if t=false then break; fi;
					od;
					if t=false then break;
					else if IsEqualSet(known,ElH) then Add(epstabs,epstab); fi;
					fi;
				until IsEqualSet(known,ElH);
			od;
		if epstabs=[] then 
			return fail;
		fi;
		epssols:=List([1..Length(epstabs)],i->function(h,f) return epstabs[i][Position(ElH,h)][Position(ElF,f)]; end);	
		epsnumsfinal:=[];
		for n in [1..Length(epssols)] do
			if epstest(epssols[n])=true then
				Add(epsnumsfinal,n);
			fi;
		od;
		if epsnumsfinal=[] then
			epsfinal:=[];
		else
			epsfinal:=List(epsnumsfinal,y->epssols[y]);
		fi;
		return epsfinal;
	fi;
end;





#epsf: the solutions eps of the epsilon relations, one per gauge class eps->eps*c(^h f)/c(f), c in Lin(F)
#in: [H,F,gamma] or [H,F,gamma,omega], F normal in H, gamma a normalized trivialization of omega|F, omega=rec(a,N)
#out: the list of eps(h,f) (from epsfA for abelian H); fail or [] when there is none
epsf:=function(inpdata)
	local H,F,gamma,omega,omegam,Uom,g1,g2,g3,ElF,Ugamma,ElD,ElH,epstest,epsFF,epsFFt,f1,f2,chtabF,clF,chF,genH,genHnotF,h,poss,poss1,kh,beta,betat,Mv,n1,n2,t,Herm,Hermt,v,sol,tocart,lb,mtoa,r,roots,rootData,n,epstabs,epstab,p,setvalh1h2,h1,h2,known,i,f,epssols,AreEquivEps,irr,epsnums,TestEquiv,test,j1,j2,epsnumsfinal,epsfinal,khn;
	H:=inpdata[1];
	if IsAbelian(H) then return epsfA(inpdata); fi;
	F:=inpdata[2];
	gamma:=inpdata[3];
	if Length(inpdata)>3 then
		omega:=inpdata[4];
	else 
		Uom:=[1];
	fi;
	if not (IsGroup(H) and IsGroup(F) and IsSubset(H,F) and IsNormal(H,F)) then
		ErrorNoReturn("epsf: F must be normal in H");
	fi;
	if not IsFunction(gamma) then ErrorNoReturn("epsf: gamma must be a function"); fi;
	#gamma is assumed to be a normalized trivialization of omega|F (omega=1 for 3-argument input), as returned by gammaf (correct by construction). For a gamma from another source call GammaTest(inpdata) first.
	ElF:=Elements(F);
	if ElF=[One(F)] then
		return [function(h,f) return 1; end];  
	fi;
	Ugamma:=Union([List(Cartesian(ElF,ElF),y->gamma(y[1],y[2]))]);	
	#let D=H-F
	ElD:=Difference(Elements(H),ElF);
	ElH:=Concatenation(ElF,ElD);
	if not IsBound(Uom) then
		omegam:=function(g1,g2,g3) return E(omega.N)^(omega.a(g1,g2,g3)); end;
		#only Uom=[1] (omega|H identically 0) is tested below; ForAll stops at the first nonzero value
		if ForAll(ElH,g1->ForAll(ElH,g2->ForAll(ElH,g3->omega.a(g1,g2,g3) mod omega.N=0))) then
			Uom:=[1];
		else
			Uom:="not 1";
		fi;
	fi;	
	#test function for eps
	epstest:=function(eps)
		local test,h1,h2,f1,f2,f,h;
		test:=true;
		if Uom=[1] then
			for h1 in ElH do
				for h2 in ElH do
					for f in ElF do
						test:=(eps(h1*h2,f)=eps(h1,h2*f*Inverse(h2))*eps(h2,f));
						if test=false then return false; fi; #Print([false,1,h1,h2,f]); return false; fi;
					od;
				od;
			od;
			for f1 in ElF do
				for f2 in ElF do
					for h in ElH do
						test:=(gamma(f1,f2)*eps(h,f1*f2)=eps(h,f1)*eps(h,f2)*gamma(h*f1*Inverse(h),h*f2*Inverse(h)));
						if test=false then return false; fi; #Print([false,2,f1,f2,h]); return false; fi;
					od;
				od;
			od;
		else
			for h1 in ElH do
				for h2 in ElH do
					for f in ElF do
						test:=(eps(h1*h2,f)=eps(h1,h2*f*Inverse(h2))*eps(h2,f)*3cocr(omegam,h1,h2,f));
						if test=false then return false; fi; #Print([false,1,h1,h2,f],"om"); return false; fi;
					od;
				od;
			od;
			for f1 in ElF do
				for f2 in ElF do
					for h in ElH do
						test:=(gamma(f1,f2)*eps(h,f1*f2)=eps(h,f1)*eps(h,f2)*gamma(h*f1*Inverse(h),h*f2*Inverse(h))*3cocl(omegam,h,f1,f2));
						if test=false then return false; fi; #Print([false,2,h,f1,f2],"om"); return false; fi;
					od;
				od;
			od;
		fi;
		return test;
	end;	

	epsFF:=[];
	for f1 in ElF do
		epsFFt:=[];
		for f2 in ElF do
			if Ugamma=[1] then 
				Add(epsFFt,1);
			else	
				Add(epsFFt,gamma(f1,f2)/gamma(f1*f2*Inverse(f1),f1)); 
			fi;
		od;
		Add(epsFF,epsFFt);
	od;
				
	if IsEqualSet(ElH,ElF) then
		#eps from gamma solves the epsilon relations when d(gamma)=omega|F (TwinAlgebras.tex App. A), not re-tested: if epstest(function(f1,f2) return epsFF[Position(ElF,f1)][Position(ElF,f2)]; end) then
			return [function(f1,f2) return epsFF[Position(ElF,f1)][Position(ElF,f2)]; end];
		#else ErrorNoReturn("ERROR in Lag eps"); return fail; fi;
	else
		chtabF:=CharacterTable(F);
		clF:=ConjugacyClasses(chtabF);
		chF:=LinearCharacters(chtabF);
		genH:=SmallGeneratingSet(H);
		genHnotF:=[];
		for h in genH do
			if not (h in ElF) then
				Add(genHnotF,h);
			fi;
		od;
		poss1:=List([1..Length(chF)],n->List(ElF,f->chF[n][Posinlist(clF,f)]));
		if Ugamma=[1] and Uom=[1] then
			poss:=Cartesian(List([1..Length(genHnotF)],n->poss1));
		else
			kh:=[];
			for h in genHnotF do
				beta:=[];
				if Uom=[1] then
					for f1 in ElF do betat:=[];
						for f2 in ElF do
							Add(betat,gamma(f1,f2)/gamma(h*f1*Inverse(h),h*f2*Inverse(h)));
						od;
						Add(beta,betat);
					od;	
				else
					for f1 in ElF do betat:=[];
						for f2 in ElF do
							Add(betat,gamma(f1,f2)/(gamma(h*f1*Inverse(h),h*f2*Inverse(h))*3cocl(omegam,h,f1,f2)));
						od;
						Add(beta,betat);
					od;
				fi;
				roots:=Set(Flat(beta));
				rootData:=List(roots,DescriptionOfRootOfUnity);
				lb:=Lcm(List(rootData,r->r[1]));
				mtoa:=function(x)
					local rd;
					rd:=DescriptionOfRootOfUnity(x);
					return (lb/rd[1])*rd[2];
				end;
				#compute trivialiazion of proj 1d irrep
				Mv:=[];
				for n1 in [1..Length(ElF)] do
					for n2 in [1..Length(ElF)] do
						t:=List([1..Length(ElF)],x->0);
						t[n1]:=t[n1]+1;
						t[n2]:=t[n2]+1;
						t[Position(ElF,(ElF[n1])*(ElF[n2]))]:=t[Position(ElF,(ElF[n1])*(ElF[n2]))]-1;
						Add(t,mtoa(beta[n1][n2]));
						Add(Mv,t);
					od;
				od;
				#solve c(f1)+c(f2)-c(f1 f2) = beta(f1,f2) mod 1 (exponents in full turns), exact Hermite-normal-form solver (n=lb)
				sol:=SolveModZ(List(Mv,r->r{[1..Length(ElF)]}),
					List(Mv,r->Last(r)/lb),lb);
				if sol=fail then return fail; fi;
				Add(kh,List(sol,x->E(DenominatorRat(x))^NumeratorRat(x)));
				#kh solves the projective equation: SolveModZ stops with an error otherwise, not re-tested:
				#khn:=Last(kh); if ForAny([1..Length(ElF)],n1->ForAny([1..Length(ElF)],n2-> khn[n1]*khn[n2]/khn[Position(ElF,ElF[n1]*ElF[n2])]<>beta[n1][n2])) then ErrorNoReturn("epsf: solver returned a non-solution for the projective character"); fi;
			od;
			tocart:=[];
			for n in [1..Length(genHnotF)] do
				Add(tocart,TransposedMat(List([1..Length(TransposedMat(poss1))],m->TransposedMat(poss1)[m]*kh[n][m])));
			od;
			poss:=Cartesian(tocart);
		fi;

			epstabs:=[];
			for p in poss do
				known:=Concatenation(ElF,genHnotF);
				epstab:=Concatenation(epsFF,NullMat(Length(ElD),Length(ElF)));
				for i in [1..Length(genHnotF)] do
					epstab[Position(ElH,genHnotF[i])]:=p[i];
				od;
				setvalh1h2:=function(h1,h2)
					if Uom=[1] then
						if h1*h2 in known then
							for f in ElF do
								if not epstab[Position(ElH,h1*h2)][Position(ElF,f)]=epstab[Position(ElH,h1)][Position(ElF,h2*f*Inverse(h2))]*epstab[Position(ElH,h2)][Position(ElF,f)]
								then return false; 
								fi;
							od;
							else 
							for f in ElF do						
								epstab[Position(ElH,h1*h2)][Position(ElF,f)]:=epstab[Position(ElH,h1)][Position(ElF,h2*f*Inverse(h2))]*epstab[Position(ElH,h2)][Position(ElF,f)];
							od;	
						fi;
					else
						if h1*h2 in known then
							for f in ElF do
								if not epstab[Position(ElH,h1*h2)][Position(ElF,f)]=epstab[Position(ElH,h1)][Position(ElF,h2*f*Inverse(h2))]*epstab[Position(ElH,h2)][Position(ElF,f)]*3cocr(omegam,h1,h2,f)
								then return false; 
								fi;
							od;
							else 
							for f in ElF do						
								epstab[Position(ElH,h1*h2)][Position(ElF,f)]:=epstab[Position(ElH,h1)][Position(ElF,h2*f*Inverse(h2))]*epstab[Position(ElH,h2)][Position(ElF,f)]*3cocr(omegam,h1,h2,f);
							od;	
						fi;

					fi;	
					return [epstab,Union([Concatenation(known,[h1*h2])])];			
				end;
				repeat
					for h1 in Difference(known,[One(H)]) do
						for h2 in genH do
							t:=setvalh1h2(h1,h2);
							if t=false then
								break;
							else epstab:=t[1]; known:=t[2]; fi;
						od;
						if t=false then break; fi;
					od;
					if t=false then break;
					else if IsEqualSet(known,ElH) then Add(epstabs,epstab); fi;
					fi;
				until IsEqualSet(known,ElH);
			od;
		if epstabs=[] then 
			return fail;
		fi;
		epssols:=List([1..Length(epstabs)],i->function(h,f) return epstabs[i][Position(ElH,h)][Position(ElF,f)]; end);			
		#Partial Equivalence relation on eps
		AreEquivEps:=function(j1,j2)
				for irr in chF do
					t:=true;
					for h in Reversed(ElH) do
						for f in ElF do
							t:=(epssols[j1](h,f)*irr[Posinlist(clF,h*f*Inverse(h))]=irr[Posinlist(clF,f)]*epssols[j2](h,f));
							if t=false then break; fi;
						od;
						if t=false then break; fi;
					od;
					if t=true then break; fi;
				od;
			return t;
		end;

	epsnums:=[1];
	TestEquiv:=function(j2)
		test:=false;
		for j1 in epsnums do
			if AreEquivEps(j1,j2) then
				test:=true;
				return true;
			fi;
		od;
		if test=false then
			return false;
		fi;
	end;
	if Length(epssols)>1 then
		for j2 in [2..Length(epssols)] do
			t:=TestEquiv(j2);
			if not t then
				Add(epsnums,j2);
			fi;
		od;
	fi;
	epsnumsfinal:=[];
	for n in epsnums do
		if epstest(epssols[n])=true then
			Add(epsnumsfinal,n);
		fi;
	od;
	if epsnumsfinal=[] then
		epsfinal:=[];
	else
		epsfinal:=List(epsnumsfinal,y->epssols[y]);
	fi;
	return epsfinal;
	fi;
end;

#NormalSubgroupReps: the normal subgroups of H up to conjugation by N_G(H)
#in: G a group and H a subgroup of G
#out: one normal subgroup F of H per N_G(H)-orbit
NormalSubgroupReps:=function(G,H)
	local NGH,reps,F;
	NGH:=Normalizer(G,H);
	reps:=[];
	for F in List(ConjugacyClassesSubgroups(H),Representative) do
		if IsNormal(H,F) and not ForAny(reps,R->Order(R)=Order(F) and IsConjugate(NGH,R,F)) then
			Add(reps,F);
		fi;
	od;
	return reps;
end;

#AlgSubgroups: the subgroup pairs (H,F), F normal in H, one per G-conjugacy class of pairs
#in: G, or rec(G,op) with op "" (all), "G" (H=G), "Lag" (F=H), "non-Lag" (F<>H) or a positive integer |H/F|
#out: the list of pairs [H,F], sorted by the dimension |G||F|/|H|
AlgSubgroups:=function(data)
	local G,op,Hcltot,Htot,H,Ftot,Ftott,F,HFtot,i;
	op:="";
	if IsGroup(data) then
		G:=data;
	else
		G:=data.G;
		if "op" in RecNames(data) then
			op:=data.op;
		fi;
	fi;
	if not (op in ["","G","Lag","non-Lag"] or IsPosInt(op)) then
		ErrorNoReturn("AlgSubgroups: invalid op");
	fi;

	Hcltot:=ConjugacyClassesSubgroups(G);
	Htot:=List(Hcltot,Representative);
	Ftot:=[];
	if op="G" then
		Ftott:=[];
		for F in Htot do
			if IsNormal(G,F) then
				Add(Ftott,F);
			fi;
		od;
		Add(Ftot,Ftott);
	else
		for H in Htot do
			if (H=Group(One(G)) and not op="non-Lag") or op="Lag" then
				Add(Ftot,[H]);
			else 
				Ftott:=[];
				#pairs (H,F), (H,^gF) with g in N_G(H) give isomorphic algebras (Lemma Morita_equiv), one is kept
				for F in NormalSubgroupReps(G,H) do
					if not (F=H and op="non-Lag") then
						Add(Ftott,F);
					fi;
				od;
				Add(Ftot,Ftott);
			fi;
		od;
	fi;

	HFtot:=[];
	if op="G" then
		for F in Ftot[1] do
			Add(HFtot,[G,F]);
		od;
	else
		for i in [1..Length(Htot)] do
			for F in Ftot[i] do
				if (not IsInt(op)) or (IsInt(op) and Order(Htot[i])/Order(F)=op) then
					Add(HFtot,[Htot[i],F]);
				fi;
			od;
		od;
	fi;
	SortBy(HFtot,x->[Order(G)*Order(x[2])/Order(x[1]),-Order(x[1]),StructureDescription(x[1]),Elements(x[1]),StructureDescription(x[2]),Elements(x[2])]);

	return HFtot;
end;


#AlgebraData: the algebras A(H,F,gamma,eps) of Z(Vec_G^omega)
#in: G, or rec(G,[om:=rec(a,N)],[HFtot:=list of pairs [H,F]],[op as in AlgSubgroups])
#out: the list of [H,F,gamma,eps,G]: per pair, gamma one per class of H^2(F,U(1)) and eps one per gauge class
AlgebraData:=function(data)
	local G,omega,UF,gammas,out,HFtot,HF,inp,epsres,l,i,eps,F,n;

	if IsGroup(data) then
		G:=data;
	else
		G:=data.G;
		if "om" in RecNames(data) then
			omega:=data.om;
		fi;
	fi;
	if IsRecord(data) and "HFtot" in RecNames(data) then
		HFtot:=data.HFtot;
	fi;
	if not IsBound(HFtot) then
		HFtot:=AlgSubgroups(data);
	fi;

	UF:=[];
	for HF in HFtot do
		if not HF[2] in UF then
			Add(UF,HF[2]);
		fi;
	od;

	gammas:=[];
	for F in UF do
		if not IsBound(omega) then
			Add(gammas,gammaf(F));
		else
			Add(gammas,gammaf([F,omega]));
		fi;
	od;

	out:=[];
	n:=1;
	for HF in HFtot do
		l:=gammas[Position(UF,HF[2])];
		if not l=fail then
			for i in [1..Length(l)] do
				if not IsBound(omega) then
					inp:=[HF[1],HF[2],l[i]];
				else
					inp:=[HF[1],HF[2],l[i],omega];
				fi;
				epsres:=epsf(inp);
				if not epsres in [fail,false] then
					for eps in epsres do
						Add(out,[HF[1],HF[2],l[i],eps,G]);
						n:=n+1;
					od;
				fi;
			od;
		fi;
	od;
	return out;
end;

#SubgroupPairs: the subgroup pairs of the algebras of a theory that pass a filter
#in: (th[,filter]), filter with optional fields dim, Lag, H, F (up to conjugation in G), K=|H/F|, each a value or a list
#out: the pairs [H,F] in AlgSubgroups order (with filter.H only the pairs of those H are generated)
SubgroupPairs:=function(arg)
	local th,filt,G,HF,inlist,conjin,d,Hs,H;
	th:=arg[1];
	if Length(arg)>1 then filt:=arg[2]; else filt:=rec(); fi;
	G:=th.G;
	inlist:=function(x,l) if IsList(l) then return x in l; fi; return x=l; end;
	conjin:=function(S,l)
		if IsGroup(l) then l:=[l]; fi;
		return ForAny(l,T->Order(T)=Order(S) and IsConjugate(G,S,T));
	end;
	d:=x->Order(G)*Order(x[2])/Order(x[1]);
	if IsBound(filt.H) then
		Hs:=[];
		for H in Flat([filt.H]) do
			if not ForAny(Hs,T->Order(T)=Order(H) and IsConjugate(G,H,T)) then Add(Hs,H); fi;
		od;
		HF:=Concatenation(List(Hs,H->List(NormalSubgroupReps(G,H),F->[H,F])));
		SortBy(HF,x->[d(x),-Order(x[1]),StructureDescription(x[1]),Elements(x[1]),StructureDescription(x[2]),Elements(x[2])]);
	else
		HF:=AlgSubgroups(G);
	fi;
	if IsBound(filt.dim) then HF:=Filtered(HF,x->inlist(d(x),filt.dim)); fi;
	if IsBound(filt.Lag) then HF:=Filtered(HF,x->(d(x)=Order(G))=filt.Lag); fi;
	if IsBound(filt.K) then HF:=Filtered(HF,x->inlist(Order(x[1])/Order(x[2]),filt.K)); fi;
	if IsBound(filt.F) then HF:=Filtered(HF,x->conjin(x[2],filt.F)); fi;
	return HF;
end;

#TQDAlgebras: the algebras of a theory that pass a filter
#in: (th[,filter]), filter as in SubgroupPairs
#out: the algebras [H,F,gamma,eps,G] of AlgebraData on the pairs of SubgroupPairs
TQDAlgebras:=function(arg)
	local th,HF,data;
	th:=arg[1];
	HF:=CallFuncList(SubgroupPairs,arg);
	if HF=[] then return []; fi;
	data:=rec(G:=th.G,HFtot:=HF);
	if IsBound(th.om) then data.om:=th.om; fi;
	return AlgebraData(data);
end;

#AlgebraName: a one-line name of an algebra
#in: (A[,glG]), A=[H,F,gamma,eps,G], glG=[elements,labels] (default MakeGroupLabels([G]))
#out: a string such as "A(S3=<s,r>, C3=<r>, 1, eps)" (gamma, eps written 1 when identically 1)
AlgebraName:=function(arg)
	local A,glG,gl,gens,H,F,ElH,ElF,s;
	A:=arg[1];
	if Length(arg)>1 then glG:=arg[2]; else glG:=MakeGroupLabels([A[5]]); fi;
	gl:=g->glG[2][Position(glG[1],g)];
	gens:=function(S)
		local l;
		l:=List(MinimalGeneratingSet(S),gl);
		if l=[] then return StructureDescription(S); fi;
		return Concatenation(StructureDescription(S),"=<",JoinStringsWithSeparator(l,","),">");
	end;
	H:=A[1]; F:=A[2]; ElH:=Elements(H); ElF:=Elements(F);
	s:=Concatenation("A(",gens(H),", ",gens(F),", ");
	if ForAll(ElF,f1->ForAll(ElF,f2->A[3](f1,f2)=1)) then Append(s,"1, "); else Append(s,"gamma, "); fi;
	if ForAll(ElH,h->ForAll(ElF,f->A[4](h,f)=1)) then Append(s,"1)"); else Append(s,"eps)"); fi;
	return s;
end;


#ShowFgammagl: prints F and the nontrivial values of gamma
#in: F a group, gamma a multiplicative 2-cochain on F, gl a labelling function on F
#out: none (prints)
ShowFgammagl:=function(F,gamma,gl)
	local ElF,f1,f2;
	ElF:=Elements(F);
	Print("F=",StructureDescription(F),"=",List(ElF,k->gl(k)),"\n");
	for f1 in ElF do
		for f2 in ElF do
			if not gamma(f1,f2)=1 then
				Print("gamma(",gl(f1),",",gl(f2),")=",gamma(f1,f2),"\n");
			fi;
		od;
	od;
end;


#TeXGroupName: a group name in the notation of TwinAlgebras.tex
#in: s a string of StructureDescription, e.g. "C2 x C2", "C3 : C4"
#out: the LaTeX string, e.g. "\Z_{2} \times \Z_{2}", "\Z_{3} \rtimes \Z_{4}" (other names unchanged)
TeXGroupName:=function(s)
	local out,i,j,c;
	out:="";
	i:=1;
	while i<=Length(s) do
		c:=s[i];
		if c in "CDQSA" and (i=1 or not (IsAlphaChar(s[i-1]) or IsDigitChar(s[i-1]))) and i<Length(s) and IsDigitChar(s[i+1]) then
			j:=i+1;
			while j<=Length(s) and IsDigitChar(s[j]) do j:=j+1; od;
			if c='C' then Append(out,"\\Z_{"); else Append(out,[c,'_','{']); fi;
			Append(out,s{[i+1..j-1]});
			Append(out,"}");
			i:=j;
		elif i+2<=Length(s) and s{[i..i+2]}=" x " then
			Append(out," \\times ");
			i:=i+3;
		elif i+2<=Length(s) and s{[i..i+2]}=" : " then
			Append(out," \\rtimes ");
			i:=i+3;
		else
			Add(out,c);
			i:=i+1;
		fi;
	od;
	return out;
end;

#TeXLabel: a group-element or anyon label in LaTeX (math mode)
#in: s a label of MakeGroupLabels or AnyonLabelStrings, e.g. "([f2],1 f3=E(8)^5)", "1*e1"
#out: the LaTeX string, e.g. "([f_{2}],1\;f_{3}=\zeta_{8}^{5})", "e_{1}"
TeXLabel:=function(s)
	local out,i,j,fac;
	if '*' in s then
		fac:=Filtered(SplitString(s,"*"),x->x<>"1");
		if fac=[] then s:="1"; else s:=JoinStringsWithSeparator(fac,"*"); fi;
	fi;
	out:="";
	i:=1;
	while i<=Length(s) do
		if i+1<=Length(s) and s{[i..i+1]}="E(" then
			j:=i+2;
			while j<=Length(s) and s[j]<>')' do j:=j+1; od;
			Append(out,Concatenation("\\zeta_{",s{[i+2..j-1]},"}"));
			i:=j+1;
		elif s[i]='^' then
			j:=i+1;
			if j<=Length(s) and s[j]='-' then j:=j+1; fi;
			while j<=Length(s) and IsDigitChar(s[j]) do j:=j+1; od;
			Append(out,Concatenation("^{",s{[i+1..j-1]},"}"));
			i:=j;
		elif IsDigitChar(s[i]) and i>1 and IsAlphaChar(s[i-1]) then
			j:=i;
			while j<=Length(s) and IsDigitChar(s[j]) do j:=j+1; od;
			Append(out,Concatenation("_{",s{[i..j-1]},"}"));
			i:=j;
		elif s[i]='*' then
			i:=i+1;
		elif s[i]=' ' then
			Append(out,"\\;");
			i:=i+1;
		else
			Add(out,s[i]);
			i:=i+1;
		fi;
	od;
	return out;
end;

#AlgebraDisplayData: the display data of one algebra of a theory, for ShowAlgData and the LaTeX tables (prints nothing)
#in: (th,A[,opts]), A=[H,N,gamma,eps,G] or a record of AlgebrasWithAnyons or AlgebraClasses, opts: na, alpha, reducedTO:=false, values:=true
#out: rec(A,dim,Lag,K,na,decomposition,decompositionTeX,name,nameTeX,alphaTrivial,reducedTO,reducedTOTeX[,gamma,eps,alpha])
AlgebraDisplayData:=function(arg)
	local th,A,opts,G,H,N,gamma,eps,ElH,ElN,ElG,gl,gens,trivg,trive,pick,r,al,ElK,ala,lab,labTeX,nz,i,s,k1,k2,k3,f1,f2,h,f;
	th:=arg[1];
	A:=arg[2];
	if Length(arg)>2 then opts:=arg[3]; else opts:=rec(); fi;
	if IsRecord(A) then
		if IsBound(A.na) and not IsBound(opts.na) then opts:=ShallowCopy(opts); opts.na:=A.na; fi;
		if IsBound(A.A) then A:=A.A;
		elif IsBound(A.algebras) then A:=A.algebras[1];
		else ErrorNoReturn("AlgebraDisplayData: a record must come from AlgebrasWithAnyons or AlgebraClasses");
		fi;
	fi;
	H:=A[1]; N:=A[2]; gamma:=A[3]; eps:=A[4]; G:=A[5];
	if not IsIdenticalObj(G,th.G) then ErrorNoReturn("AlgebraDisplayData: the algebra does not belong to the theory th"); fi;
	ElH:=Elements(H); ElN:=Elements(N);
	ElG:=th.glG[1];
	gl:=g->th.glG[2][Position(ElG,g)];
	#generator strings of a subgroup: [plain, TeX]
	gens:=function(S)
		local l;
		l:=List(MinimalGeneratingSet(S),gl);
		if l=[] then return ["1","1"]; fi;
		return [Concatenation(StructureDescription(S),"=<",JoinStringsWithSeparator(l,","),">"),
			Concatenation(TeXGroupName(StructureDescription(S)),"=\\langle ",JoinStringsWithSeparator(List(l,TeXLabel),","),"\\rangle")];
	end;
	trivg:=ForAll(ElN,x->ForAll(ElN,y->gamma(x,y)=1));
	trive:=ForAll(ElH,x->ForAll(ElN,y->eps(x,y)=1));
	r:=rec(A:=A,dim:=Order(G)*Order(N)/Order(H),Lag:=H=N,K:=StructureDescription(H/N));
	pick:=function(b,x,y) if b then return x; fi; return y; end;
	r.name:=Concatenation("A(",gens(H)[1],", ",gens(N)[1],", ",pick(trivg,"1","gamma"),", ",pick(trive,"1","eps"),")");
	r.nameTeX:=Concatenation("A(",gens(H)[2],", ",gens(N)[2],", ",pick(trivg,"1","\\gamma"),", ",pick(trive,"1","\\epsilon"),")");
	#anyon decomposition
	if IsBound(opts.na) then r.na:=opts.na;
	elif IsBound(th.om) then r.na:=Last(AlgAnyonsV([A,th.aG,th.om]));
	else r.na:=Last(AlgAnyonsV([A,th.aG]));
	fi;
	r.decomposition:=ShowAlg(r.na,th.labels);
	lab:=ShallowCopy(th.labels);
	lab[1]:="([1],1)";
	labTeX:=List(lab,TeXLabel);
	nz:=Filtered([1..Length(r.na)],i->r.na[i]<>0);
	r.decompositionTeX:=JoinStringsWithSeparator(List(nz,function(i)
		if r.na[i]=1 then return labTeX[i]; fi;
		return Concatenation(String(r.na[i]),labTeX[i]);
	end)," \\oplus ");
	#reduced topological order (TwinAlgebras.tex Thm DS-reducedTO)
	al:=fail;
	if IsBound(opts.reducedTO) and opts.reducedTO=false then
		#skipped
	elif r.Lag then
		r.alphaTrivial:=fail;
		r.reducedTO:="Trivial";
		r.reducedTOTeX:="\\text{Trivial}";
	elif H=G and Order(N)=1 then
		#alpha=omega on G/1=G: trivial when th.om is unbound or identically 0 (the zero test of TQDTheory), otherwise a coboundary iff GammaTrivialization finds a trivialization
		r.alphaTrivial:=not IsBound(th.om) or ForAll(ElG,g1->ForAll(ElG,g2->ForAll(ElG,g3->th.om.a(g1,g2,g3) mod th.om.N=0)))
			or GammaTrivialization(G,th.om)<>fail;
		if not r.alphaTrivial then
			r.reducedTO:=Concatenation("D^omega(",r.K,")");
			r.reducedTOTeX:=Concatenation("D^{\\omega}(",TeXGroupName(r.K),")");
		else
			r.reducedTO:=Concatenation("D(",r.K,")");
			r.reducedTOTeX:=Concatenation("D(",TeXGroupName(r.K),")");
		fi;
	else
		if IsBound(opts.alpha) then al:=opts.alpha;
		elif IsBound(th.om) then al:=alphaf([A,th.om]);
		else al:=alphaf([A]);
		fi;
		ElK:=al[2]; ala:=al[3];
		#alpha is a coboundary iff GammaTrivialization finds a 2-cochain trivializing it (same yes/no as gammaf)
		r.alphaTrivial:=GammaTrivialization(Group(ElK),ala)<>fail;
		if r.alphaTrivial then
			r.reducedTO:=Concatenation("D(",r.K,")");
			r.reducedTOTeX:=Concatenation("D(",TeXGroupName(r.K),")");
		else
			r.reducedTO:=Concatenation("D^alpha(",r.K,")");
			r.reducedTOTeX:=Concatenation("D^{\\alpha}(",TeXGroupName(r.K),")");
		fi;
	fi;
	if IsBound(opts.values) and opts.values=true then
		r.gamma:=[]; r.eps:=[]; r.alpha:=[];
		for f1 in ElN do for f2 in ElN do
			if gamma(f1,f2)<>1 then Add(r.gamma,Concatenation("gamma(",gl(f1),",",gl(f2),")=",String(gamma(f1,f2)))); fi;
		od; od;
		for f in ElN do for h in ElH do
			if eps(h,f)<>1 then Add(r.eps,Concatenation("eps(",gl(h),",",gl(f),")=",String(eps(h,f)))); fi;
		od; od;
		if al=fail and not r.Lag and not (H=G and Order(N)=1) then
			if IsBound(opts.alpha) then al:=opts.alpha;
			elif IsBound(th.om) then al:=alphaf([A,th.om]);
			else al:=alphaf([A]);
			fi;
			ElK:=al[2]; ala:=al[3];
		fi;
		if H=G and Order(N)=1 and IsBound(th.om) then
			#alpha=omega on G/1=G; th.om is stored as omega itself (not its bar)
			for k1 in ElG do for k2 in ElG do for k3 in ElG do
				if th.om.a(k1,k2,k3) mod th.om.N<>0 then
					Add(r.alpha,Concatenation("alpha(",gl(k1),",",gl(k2),",",gl(k3),")=",String(E(th.om.N)^th.om.a(k1,k2,k3))));
				fi;
			od; od; od;
		fi;
		if al<>fail then
			for k1 in ElK do for k2 in ElK do for k3 in ElK do
				if ala.a(k1,k2,k3) mod ala.N<>0 then
					Add(r.alpha,Concatenation("alpha(",String(k1),",",String(k2),",",String(k3),")=",String(E(ala.N)^(-ala.a(k1,k2,k3)))));
				fi;
			od; od; od;
		fi;
	fi;
	return r;
end;

#ShowAlgData: prints one algebra: name, dimension, H/N, reduced TO, anyons (opP:="long": H, N and the values of gamma, eps, alpha)
#in: (th,A[,opts]) as for AlgebraDisplayData, opts also opP:="short" (default) or "long"
#out: the record of AlgebraDisplayData
ShowAlgData:=function(arg)
	local th,r,s,opts,long,H,N,gl,gstr;
	th:=arg[1];
	if Length(arg)>2 then opts:=ShallowCopy(arg[3]); else opts:=rec(); fi;
	long:=false;
	if IsBound(opts.opP) then
		if not opts.opP in ["short","long"] then ErrorNoReturn("ShowAlgData: opP must be \"short\" or \"long\""); fi;
		long:=opts.opP="long";
		Unbind(opts.opP);
	fi;
	if long then opts.values:=true; opts.reducedTO:=false; fi;
	r:=AlgebraDisplayData(th,arg[2],opts);
	if not long then
		Print(r.name,"  dim=",r.dim,"  H/N=",r.K);
		if IsBound(r.reducedTO) then Print("  reduced TO: ",r.reducedTO); fi;
		Print("\n");
		Print("  ",r.decomposition,"\n");
		if IsBound(r.gamma) then
			for s in Concatenation(r.gamma,r.eps,r.alpha) do Print("  ",s,"\n"); od;
		fi;
		return r;
	fi;
	H:=r.A[1]; N:=r.A[2];
	gl:=g->th.glG[2][Position(th.glG[1],g)];
	#"S=<generators>" with S the StructureDescription, or just S for the trivial group
	gstr:=function(S)
		local l;
		l:=List(MinimalGeneratingSet(S),gl);
		if l=[] then return StructureDescription(S); fi;
		return Concatenation(StructureDescription(S),"=<",JoinStringsWithSeparator(l,","),">");
	end;
	Print("H=",gstr(H),"   N=",gstr(N),"  H/N=",r.K,"\n");
	for s in Concatenation(r.gamma,r.eps) do Print(s,"\n"); od;
	if H=th.G and IsTrivial(N) then
		if IsBound(th.om) and r.alpha<>[] then Print("3-cocycle=omega\n"); fi;
	else
		for s in r.alpha do Print(s,"\n"); od;
	fi;
	Print("  ",r.decomposition,"\n\n");
	return r;
end;

