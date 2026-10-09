#############################################################################
##
## source/7_quantum_information.g     AlgebrasTQD
##
## Non-Abelian-code utilities for quantum information.
##
## Functions in this file (the first line of each header):
## - DiagMat: diagonal matrix of a vector
## - Abs2: squared absolute value
## - Kr1: places an operator on one site of an N-site register
## - nzM: positions of the nonzero entries of a matrix
## - Dops: the d^2 displacement (generalized Pauli) operators of one qudit
## - Dtilde: the displacement group of N qudits, phases included
## - IsClifford: tests whether a unitary normalizes the displacement group
## - CliffordLevel: the Clifford-hierarchy level of a unitary
## - CliffordLevelOf: the Clifford-hierarchy level of a unitary, with the qudit register read off its size
## - Df: the phase-free displacement operators of N qudits
## - CycToFloat: real part of a cyclotomic as a floating-point number
## - 2Renyi: the second Renyi magic of a state
## - Cliffords1: generators of the single-qudit Clifford group
## - CoeffString: the sign and coefficient printed before a basis element
## - Showv: a vector in Dirac notation on one line
## - ShowKet: a vector in Dirac notation, one basis element per line
## - ShowOp: an operator in ket-bra notation, one matrix element per line
## - ShowOpTex: an operator as a single LaTeX ket-bra string
## - Showm: a linear map by the image of each basis element
## - Lvf: the left multiplication operators of a group algebra
## - Rvf: the right multiplication operators of a group algebra
## - GroupProjector: the projector onto the invariants of a subgroup
## - VertexProjectorL: the left vertex projector of a subgroup
## - VertexProjectorR: the right vertex projector of a subgroup
## - DiagProjector: the projector gauging a diagonal subgroup of a product of two code groups
## - RoughMergeSplitStep: a rough merge and split between finite-group code patches
## - RoughMergeSplit: the logical gate produced by two lattice-surgery merges
## - SPTStackingGate: the logical gate from a 2-cocycle and boundary counterterms
## - IsCounterterm: tests whether a 1-cochain trivializes a 2-cocycle
## - LogicalUab: the logical gate of a triangular patch with three boundaries
## - PhaseGate: the single-qubit phase gate diag(1,e^{i pi/m})
## - CCSgate: the multiply controlled S gate on nq qubits
## - D4NData: the group D_{4N} with its element order, labels and qubit data
## - D4NRecord: accepts N or an existing D4NData record
## - D4NCocycle: the nontrivial class of H^2(D_{4N},U(1)) with its counterterm on <r>
## - D4NCocycleRecord: accepts N, a D4NData record, or an existing D4NCocycle record
## - D4NCocycleTest: the slow cocycle identities for D_{4N}, checked on request
## - D4NPhaseGate: the constant-depth circuit for the counterterm beta and the logical gate it encodes
## - QuditSState: the Z_d stabilizer state |S>
## - D4NSurgeryGate: the T^{1/N} logical gate obtained by hybrid lattice surgery
##
#############################################################################

#DiagMat: diagonal matrix of a vector
#in: v a list of numbers
#out: the diagonal matrix with v on the diagonal
DiagMat:=function(v)
	return DiagonalMat(v);
end;



#Abs2: squared absolute value
#in: n a number or a vector
#out: n*ComplexConjugate(n), i.e. |n|^2
Abs2:=function(n)
	return n*ComplexConjugate(n);
end;

#Kr1: places an operator on one site of an N-site register
#in: M a d x d matrix, N the number of sites, n the site in [1..N]
#out: the matrix acting as M on site n and as the identity on the others
Kr1:=function(M,N,n)
	local l;
	if not IsPosInt(N) then ErrorNoReturn("N must be positive"); fi;
	if not IsPosInt(n) or n>N then ErrorNoReturn("n must lie in [1..N]"); fi;
	l:=Length(M);
	if n=1 then
		return Kr(M,IdentityMat(l^(N-1)));
	elif n=N then
		return Kr(IdentityMat(l^(N-1)),M);
	else
		return Kr(Kr(IdentityMat(l^(n-1)),M),IdentityMat(l^(N-n)));
	fi;
end;

#nzM: positions of the nonzero entries of a matrix
#in: M a matrix
#out: the list of [row,column] positions of its nonzero entries
nzM:=function(M)
	local i,j,t,toret;
	toret:=[];
	for i in [1..Length(M)] do
		for j in [1..Length(M[i])] do
			if not M[i][j]=0 then 
				Add(toret,[i,j]);
			fi;
		od;
	od;
	return toret;
end;

#Dops: the d^2 displacement (generalized Pauli) operators of one qudit
#in: d an integer >= 2
#out: the list of the d^2 matrices (-E(2d))^(kl) x^k z^l, in the order given by [k,l]
Dops:=function(d)
	local G,El,ord,g,x,z,D,Ds,k,l;
	if not IsInt(d) or d<2 then ErrorNoReturn("d must be an integer >= 2"); fi;
	G:=CyclicGroup(IsFpGroup,d);
	El:=Elements(G);
	ord:=List(El,Order);
	#g is a generator of Cd
	g:=El[Position(ord,Order(G))];
	if g<>El[2] or El<>List([0..d-1],k->g^k) then
		ErrorNoReturn("unexpected cyclic-group element ordering");
	fi;
	x:=TransposedMat(PermutationMat(AsPermutation(PartialPerm(List(g*El,k->Position(El,k)))),d));
	z:=DiagonalMat(List([0..d-1],k->E(d)^k));
	if not z*x=E(d)*x*z then ErrorNoReturn("wrong comm rel"); fi;
	D:=function(k,l)
		return (-E(2*d))^(k*l)*(x^k)*(z^l);
	end;
	Ds:=[];
	for k in [0..d-1] do
		for l in [0..d-1] do
			Add(Ds,D(k,l));
		od;
	od;	
	return Ds;
end;

#Dtilde: the displacement group of N qudits, phases included
#in: d an integer >= 2 and N a positive number of qudits
#out: the matrix group generated by the single-site displacements on all N sites
Dtilde:=function(d,N)
	local D1,Dt,n1,n2;
	if not IsInt(d) or d<2 then ErrorNoReturn("d must be an integer >= 2"); fi;
	if not IsPosInt(N) then ErrorNoReturn("N must be positive"); fi;
	D1:=Dops(d);
	if N=1 then 
		return Group(D1);
	else
		Dt:=[];
		for n1 in [1..N] do
			for n2 in [1..Length(D1)] do
				Add(Dt,Kr1(D1[n2],N,n1));
			od;
		od;
		return Group(Dt);
	fi;
end;

#IsClifford: tests whether a unitary normalizes the displacement group
#in: U a matrix and Dt a group as returned by Dtilde
#out: true or false, or the string "input matrix cannot be unitary"
IsClifford:=function(U,Dt)
	local P,test,M;
	M:=U*Dag(U);
	if (not M=M[1][1]*IdentityMat(Length(U))) or M[1][1]=0 then
		return "input matrix cannot be unitary";
	fi;
	test:=true;
	for P in GeneratorsOfGroup(Dt) do
		test:=(U*P*Dag(U)/M[1][1] in Dt);
		if test=false then
			return false;
		fi;
	od;
	return test;
end;

#CliffordLevel: the Clifford-hierarchy level of a unitary
#in: (U,Dt[,maxlevel]) with Dt from Dtilde and maxlevel the search bound (4 by default)
#out: the level as a positive integer, the string "input matrix cannot be unitary", or an error when no level is at or below maxlevel
CliffordLevel:=function(arg)
	local U,Dt,maxlevel,M,paulis,canon,canonPaulis,n,As,bad,A,mu,P,Q;
	if not Length(arg) in [2,3] then
		ErrorNoReturn("usage: CliffordLevel(U,Dt[,maxlevel])");
	fi;
	U:=arg[1];
	Dt:=arg[2];
	if Length(arg)=3 then maxlevel:=arg[3]; else maxlevel:=4; fi;
	if not IsPosInt(maxlevel) then ErrorNoReturn("maxlevel must be a positive integer"); fi;
	M:=U*Dag(U);
	if (not M=M[1][1]*IdentityMat(Length(U))) or M[1][1]=0 then
		return "input matrix cannot be unitary";
	fi;
	#U is not rescaled (Sqrt of an irrational cyclotomic is not available in GAP): the level does not depend on a scalar, canon removes it at level 1 and every conjugate below is divided by mu=(A*Dag(A))[1][1] Membership in a level is invariant under an overall scalar, so every comparison below is made through the representative canon(Q) of the phase class of Q. This also keeps the recursion from repeating each conjugate once per scalar in Dt.
	canon:=function(Q)
		local i,j;
		for i in [1..Length(Q)] do
			for j in [1..Length(Q[i])] do
				if not Q[i][j]=0 then return Q/Q[i][j]; fi;
			od;
		od;
		ErrorNoReturn("CliffordLevel: the zero matrix is not unitary");
	end;
	#Levels above 1 are not groups, so conjugating only the generators of Dt is not enough: use one representative of every phase class of Dt instead. Centre(Dt) is exactly the group of scalar matrices in Dt.
	paulis:=List(RightCosets(Dt,Centre(Dt)),Representative);
	canonPaulis:=Set(List(paulis,canon));
	if canon(U) in canonPaulis then return 1; fi;
	As:=[U];
	n:=2;
	while true do
		if n>maxlevel then
			ErrorNoReturn("CliffordLevel: no level at or below ",maxlevel,
				"; pass a larger maxlevel to search further");
		fi;
		bad:=[];
		for A in As do
			#A is only fixed up to a scalar, so normalize the conjugate by it
			mu:=(A*Dag(A))[1][1];
			for P in paulis do
				Q:=canon(A*P*Dag(A)/mu);
				if not Q in canonPaulis then Add(bad,Q); fi;
			od;
		od;
		bad:=Set(bad);
		if bad=[] then return n; fi;
		n:=n+1;
		As:=bad;
	od;
end;

#CliffordLevelOf: the Clifford-hierarchy level of a unitary, with the qudit register read off its size
#in: (U[,d[,maxlevel]]) with U a d^N x d^N matrix, d the qudit dimension (default 2), maxlevel as in CliffordLevel
#out: the output of CliffordLevel(U,Dtilde(d,N)[,maxlevel])
CliffordLevelOf:=function(arg)
	local U,d,N;
	U:=arg[1];
	if Length(arg)>1 then d:=arg[2]; else d:=2; fi;
	if not IsInt(d) or d<2 then ErrorNoReturn("CliffordLevelOf: d must be an integer >= 2"); fi;
	if Length(U)<d then ErrorNoReturn("CliffordLevelOf: U must be at least d x d (one qudit)"); fi;
	N:=LogInt(Length(U),d);
	if d^N<>Length(U) then ErrorNoReturn("CliffordLevelOf: the size ",Length(U)," of U is not a power of d=",d); fi;
	if Length(arg)>2 then return CliffordLevel(U,Dtilde(d,N),arg[3]); fi;
	return CliffordLevel(U,Dtilde(d,N));
end;

#Df: the phase-free displacement operators of N qudits
#in: d an integer >= 2 and N a positive number of qudits
#out: one matrix per coset of the scalars in Dtilde(d,N), i.e. one per displacement
Df:=function(d,N)
	local Dt,tau,one,Rs,Ds;
	Dt:=Dtilde(d,N);
	one:=One(Dt);
	tau:=-E(2*d)*IdentityMat(Length(one));
	Rs:=RightCosets(Dt,Group(tau));
	Ds:=List(Rs,r->Elements(r)[1]);
	return Ds;
end;

#CycToFloat: real part of a cyclotomic as a floating-point number
#in: z a cyclotomic
#out: its real part as a float, computed from CoeffsCyc when z is irrational
CycToFloat:=function(z)
	local n,c,k,s;
	#GAP 4.15 has no Float method for an irrational cyclotomic, so the real part is evaluated from the coefficients over E(Conductor)
	if IsRat(z) then return Float(z); fi;
	n:=Conductor(z);
	c:=CoeffsCyc(z,n);
	s:=0.;
	for k in [1..n] do
		if c[k]<>0 then
			s:=s+Float(c[k])*Cos(2.*FLOAT.PI*Float(k-1)/Float(n));
		fi;
	od;
	return s;
end;

#2Renyi: the second Renyi magic of a state
#in: v a nonzero state vector and D a list of displacement operators, e.g. Df(d,N)
#out: the magic -Log2(Xi2)-Log2(dim) as a float
2Renyi:=function(v,D)
	local res,dim,Xi2,M,t,norm2;
	res:=0;
	dim:=Length(v);
	Xi2:=0;
	norm2:=Abs2(v);
	if norm2=0 then ErrorNoReturn("2Renyi: zero vector"); fi;
	for M in D do
		t:=Abs2(ComplexConjugate(v)*M*v)/(norm2^2*dim);
		Xi2:=Xi2+t^2;
	od;
	Xi2:=CycToFloat(Xi2);
	if Xi2<=0. then ErrorNoReturn("2Renyi: nonpositive Xi2"); fi;
	res:=-Log2(Xi2)-Log2(Float(dim));
	if res>-1.e-10 and res<1.e-10 then res:=0.; fi;
	return res;
end;












#Cliffords1: generators of the single-qudit Clifford group
#in: d an integer >= 2
#out: the list [x,z,H,S] of the shift, clock, Fourier and phase matrices
Cliffords1:=function(d)
	local G,El,ord,g,x,z,H,n,S,Clgen;
	if not IsInt(d) or d<2 then ErrorNoReturn("d must be an integer >= 2"); fi;
	G:=CyclicGroup(IsFpGroup,d);
	El:=Elements(G);
	ord:=List(El,Order);
	#g is a generator of Cd
	g:=El[Position(ord,Order(G))];
	if g<>El[2] or El<>List([0..d-1],k->g^k) then
		ErrorNoReturn("unexpected cyclic-group element ordering");
	fi;
	x:=TransposedMat(PermutationMat(AsPermutation(PartialPerm(List(g*El,k->Position(El,k)))),d));
	z:=DiagonalMat(List([0..d-1],k->E(d)^k));
	if not z*x=E(d)*x*z then ErrorNoReturn("wrong comm rel"); fi;
	#Hadamard, aka Quantum Fourier Transform
	H:=[];
	for n in [0..d-1] do
		Add(H,List([0..d-1],k->E(d)^(k*n)));
	od;
	H:=H/Sqrt(d);
	if (not H*x*Dag(H)=z) or (not H*z*Dag(H)=Inverse(x)) then ErrorNoReturn("error in H"); fi;
	if not IsInt(d/2) then 
		S:=DiagonalMat(List([0..d-1],j->E(d*2)^(j*(j-1))));
		if (not S*x*Dag(S)=x*z) or (not S*z*Dag(S)=z) then ErrorNoReturn("error in S"); fi;	
	else
		S:=DiagonalMat(List([0..d-1],j->E(d*2)^(j^2)));
		if (not S*x*Dag(S)=E(2*d)*x*z) or (not S*z*Dag(S)=z) then ErrorNoReturn("error in S"); fi;	
	fi;
	Clgen:=[x,z,H,S];
	return Clgen;
end;



#############################################################################
##
## Logical states and logical operators in Dirac notation
##
#############################################################################

#CoeffString: the sign and coefficient printed before a basis element
#in: c a number
#out: the string "+", "-", or the signed coefficient
CoeffString:=function(c)
	local s;
	s:=String(c);
	if s="1" then return "+";
	elif s="-1" then return "-";
	elif '+' in s or '-' in s{[2..Length(s)]} then
		#a sum needs brackets to stay readable in front of a ket
		return Concatenation("+(",s,")");
	elif s[1]='-' then return s;
	else return Concatenation("+",s);
	fi;
end;

#Showv: a vector in Dirac notation on one line
#in: v a vector and lab the matching list of basis labels
#out: the string "+|lab1>-|lab3>..." of its nonzero entries
Showv:=function(v,lab)
	local s,i;
	if not Length(v)=Length(lab) then ErrorNoReturn("Showv: wrong lab length"); fi;
	s:="";
	for i in PosNonZero(v) do
		s:=Concatenation(s,CoeffString(v[i]),"|",String(lab[i]),">");
	od;
	return s;
end;

#ShowKet: a vector in Dirac notation, one basis element per line
#in: v a vector and lab the matching list of basis labels
#out: prints the nonzero entries, returns nothing
ShowKet:=function(v,lab)
	local i;
	if not Length(v)=Length(lab) then ErrorNoReturn("ShowKet: wrong lab length"); fi;
	for i in PosNonZero(v) do
		Print(CoeffString(v[i]),"|",String(lab[i]),">\n");
	od;
end;

#ShowOp: an operator in ket-bra notation, one matrix element per line
#in: M a matrix and lab the matching list of basis labels
#out: prints the nonzero entries ordered by column, returns nothing
ShowOp:=function(M,lab)
	local ns,n;
	if not Length(M)=Length(lab) then ErrorNoReturn("ShowOp: wrong lab length"); fi;
	ns:=ShallowCopy(nzM(M));
	SortBy(ns,l->l[2]);
	for n in ns do
		Print(CoeffString(M[n[1]][n[2]]),"|",String(lab[n[1]]),"><",String(lab[n[2]]),"|\n");
	od;
end;

#ShowOpTex: an operator as a single LaTeX ket-bra string
#in: M a matrix and lab the matching list of basis labels
#out: prints the \\ket{}\\bra{} string, returns nothing
ShowOpTex:=function(M,lab)
	local ns,n,s;
	if not Length(M)=Length(lab) then ErrorNoReturn("ShowOpTex: wrong lab length"); fi;
	ns:=ShallowCopy(nzM(M));
	SortBy(ns,l->l[2]);
	s:="";
	for n in ns do
		s:=Concatenation(s,CoeffString(M[n[1]][n[2]]),
			"\\ket{",String(lab[n[1]]),"}\\bra{",String(lab[n[2]]),"}");
	od;
	Print(s);
end;

#Showm: a linear map by the image of each basis element
#in: m a matrix whose rows are the images, lab1 the source and lab2 the target labels
#out: prints "|lab1[n]> -> image" for each nonzero row, returns nothing
Showm:=function(m,lab1,lab2)
	local n;
	if not Length(m)=Length(lab1) then ErrorNoReturn("Showm: wrong lab1 length"); fi;
	for n in [1..Length(m)] do
		if not PosNonZero(m[n])=[] then
			Print("|",String(lab1[n]),"> -> ",Showv(m[n],lab2),"\n");
		fi;
	od;
end;


#############################################################################
##
## Group-algebra operators and quantum-double projectors
##
#############################################################################

#Lvf: the left multiplication operators of a group algebra
#in: gs a nonempty list of group elements closed under multiplication
#out: the list of matrices L^g, one per element of gs, with L^g|h>=|gh>
Lvf:=function(gs)
	local n,Lg;
	#the columns are the images, so the matrices act on column vectors
	if not (IsList(gs) and Length(gs)>0) then
		ErrorNoReturn("Lvf: gs must be a nonempty list of group elements");
	fi;
	n:=Length(gs);
	Lg:=function(g)
		local M,k,p;
		M:=NullMat(n,n);
		for k in [1..n] do
			p:=Position(gs,g*gs[k]);
			if p=fail then ErrorNoReturn("Lvf: gs is not closed under multiplication"); fi;
			M[p][k]:=1;
		od;
		return M;
	end;
	return List(gs,g->Lg(g));
end;

#Rvf: the right multiplication operators of a group algebra
#in: gs a nonempty list of group elements closed under multiplication
#out: the list of matrices R^g, one per element of gs, with R^g|h>=|h g^-1>
Rvf:=function(gs)
	local n,Rg;
	if not (IsList(gs) and Length(gs)>0) then
		ErrorNoReturn("Rvf: gs must be a nonempty list of group elements");
	fi;
	n:=Length(gs);
	Rg:=function(g)
		local M,k,p;
		M:=NullMat(n,n);
		for k in [1..n] do
			p:=Position(gs,gs[k]*g^-1);
			if p=fail then ErrorNoReturn("Rvf: gs is not closed under multiplication"); fi;
			M[p][k]:=1;
		od;
		return M;
	end;
	return List(gs,g->Rg(g));
end;

#GroupProjector: the projector onto the invariants of a subgroup
#in: gs the ordered elements, Mv the operators Lvf(gs) or Rvf(gs), H a subgroup of Group(gs) or its element list
#out: the projector (1/|H|) sum_{h in H} Mv[h] as a matrix
GroupProjector:=function(gs,Mv,H)
	local hs,P;
	if IsGroup(H) then hs:=Elements(H); else hs:=H; fi;
	if not ForAll(hs,h->h in gs) then
		ErrorNoReturn("GroupProjector: H is not contained in gs");
	fi;
	P:=1/Length(hs)*Sum(List(hs,h->Mv[Position(gs,h)]));
	if not (P=Dag(P) and P*P=P) then
		ErrorNoReturn("GroupProjector: H is not a subgroup");
	fi;
	if not (Length(P)=Length(gs) and ForAll(P,row->Length(row)=Length(gs))) then
		ErrorNoReturn("GroupProjector: wrong dimensions");
	fi;
	return P;
end;

#VertexProjectorL: the left vertex projector of a subgroup
#in: gs the ordered elements and H a subgroup or its element list
#out: GroupProjector(gs,Lvf(gs),H) as a matrix
VertexProjectorL:=function(gs,H)
	return GroupProjector(gs,Lvf(gs),H);
end;

#VertexProjectorR: the right vertex projector of a subgroup
#in: gs the ordered elements and H a subgroup or its element list
#out: GroupProjector(gs,Rvf(gs),H) as a matrix
VertexProjectorR:=function(gs,H)
	return GroupProjector(gs,Rvf(gs),H);
end;

#DiagProjector: the projector gauging a diagonal subgroup Hd of a direct product A x B of code groups
#in: rec(Hd,p1,p2,els1,els2,M1,M2) with Hd the subgroup of A x B, p1, p2 the projections of A x B onto A and B, els1, els2 the ordered element lists of A and B, M1, M2 the multiplication operators (Lvf or Rvf) used on each factor
#out: the projector (1/|Hd|) sum_{h in Hd} M1[p1(h)] tensor M2[p2(h)] as a matrix
DiagProjector:=function(inp)
	local hs,P,d;
	if not (IsRecord(inp) and ForAll(["Hd","p1","p2","els1","els2","M1","M2"],
		f->IsBound(inp.(f)))) then
		ErrorNoReturn("DiagProjector: inp needs Hd, p1, p2, els1, els2, M1 and M2");
	fi;
	hs:=Elements(inp.Hd);
	P:=1/Length(hs)*Sum(List(hs,h->Kr(
		inp.M1[Position(inp.els1,Image(inp.p1,h))],
		inp.M2[Position(inp.els2,Image(inp.p2,h))])));
	d:=Length(inp.els1)*Length(inp.els2);
	if not (Length(P)=d and ForAll(P,row->Length(row)=d)) then
		ErrorNoReturn("DiagProjector: wrong dimensions");
	fi;
	if not (P=Dag(P) and P*P=P) then
		ErrorNoReturn("DiagProjector: Hd does not give a projector");
	fi;
	return P;
end;


#############################################################################
##
## Hybrid lattice surgery
##
## Merge a D(KL) patch into a D(G) patch, merge the result into a D(KR) patch, and measure the D(G) patch in its logical identity state. The logical action left on the D(KR) qudit is returned. See arXiv:2510.20890.
##
#############################################################################

#RoughMergeSplitStep: a rough merge of two finite-group code patches, gauging a subgroup of A x B, and optionally the split that reads out one patch
#in: rec(A,B,Hd,vA,vB[,elsA,elsB,sideA,sideB,readout]) with Hd a list of generator pairs [a,b] of the gauged subgroup, vA, vB the states in the ordered bases elsA, elsB (default Elements), sideA, sideB "L" or "R" (default "R") the multiplication operators, readout=rec(factor:=1 or 2,state:=ket) the patch read out and its state
#out: rec(projector,merged,Hd[,state,weight]) with state the unnormalized postselected vector of the other factor and weight its squared norm
RoughMergeSplitStep:=function(inp)
	local A,B,elsA,elsB,AB,eA,eB,pA,pB,Hd,MA,MB,P,merged,dA,dB,readout,out,j,i;
	if not (IsRecord(inp) and ForAll(["A","B","Hd","vA","vB"],
		f->IsBound(inp.(f)))) then
		ErrorNoReturn("RoughMergeSplitStep: inp needs A, B, Hd, vA and vB");
	fi;
	A:=inp.A; B:=inp.B;
	if IsBound(inp.elsA) then elsA:=inp.elsA; else elsA:=Elements(A); fi;
	if IsBound(inp.elsB) then elsB:=inp.elsB; else elsB:=Elements(B); fi;
	if not (IsEqualSet(elsA,Elements(A)) and IsEqualSet(elsB,Elements(B))) then
		ErrorNoReturn("RoughMergeSplitStep: elsA and elsB must list the group elements");
	fi;
	dA:=Length(elsA); dB:=Length(elsB);
	if not (Length(inp.vA)=dA and Length(inp.vB)=dB) then
		ErrorNoReturn("RoughMergeSplitStep: state dimensions do not match the groups");
	fi;
	if IsBound(inp.sideA) and inp.sideA="L" then MA:=Lvf(elsA);
	elif not IsBound(inp.sideA) or inp.sideA="R" then MA:=Rvf(elsA);
	else ErrorNoReturn("RoughMergeSplitStep: sideA must be L or R"); fi;
	if IsBound(inp.sideB) and inp.sideB="L" then MB:=Lvf(elsB);
	elif not IsBound(inp.sideB) or inp.sideB="R" then MB:=Rvf(elsB);
	else ErrorNoReturn("RoughMergeSplitStep: sideB must be L or R"); fi;
	if not ForAll(inp.Hd,p->Length(p)=2 and p[1] in elsA and p[2] in elsB) then
		ErrorNoReturn("RoughMergeSplitStep: Hd must contain generator pairs from A x B");
	fi;
	AB:=DirectProduct(A,B);
	eA:=Embedding(AB,1); eB:=Embedding(AB,2);
	pA:=Projection(AB,1); pB:=Projection(AB,2);
	Hd:=Group(List(inp.Hd,p->Image(eA,p[1])*Image(eB,p[2])),One(AB));
	P:=DiagProjector(rec(Hd:=Hd,p1:=pA,p2:=pB,
		els1:=elsA,els2:=elsB,M1:=MA,M2:=MB));
	merged:=P*Kr([inp.vA],[inp.vB])[1];
	if not IsBound(inp.readout) then
		return rec(projector:=P,merged:=merged,Hd:=Hd);
	fi;
	readout:=inp.readout;
	if not (IsRecord(readout) and IsBound(readout.factor) and
		IsBound(readout.state)) then
		ErrorNoReturn("RoughMergeSplitStep: readout needs factor and state");
	fi;
	if readout.factor=1 and Length(readout.state)=dA then
		out:=List([1..dB],j->Sum([1..dA],i->
			ComplexConjugate(readout.state[i])*merged[(i-1)*dB+j]));
	elif readout.factor=2 and Length(readout.state)=dB then
		out:=List([1..dA],i->Sum([1..dB],j->
			ComplexConjugate(readout.state[j])*merged[(i-1)*dB+j]));
	else
		ErrorNoReturn("RoughMergeSplitStep: readout factor or state has wrong size");
	fi;
	return rec(projector:=P,merged:=merged,Hd:=Hd,state:=out,weight:=Abs2(out));
end;

#RoughMergeSplit: the logical gate produced by two lattice-surgery merges
#in: rec(G,KL,vL,HdL,KR,HdR[,gs,kL,kR,Hr,maxlevel,conductor,show,lab,labKR]), the fields described at the start of the function
#out: rec(U,mu,P,inG,eigenvalues,multiplicities,eigenphases[,Unorm,Dt,clifford,level]) with U*Dag(U)=mu*1 and Unorm=U/Sqrt(mu) the unitary logical action on the right patch (bound only for a rational mu; otherwise eigenvalues are those of U, a common scalar times those of the unitary); inG the merged state, normalized only when its norm is rational; eigenvalues the DISTINCT eigenvalues, in the order returned by Eigenvalues (not fixed), with their algebraic multiplicities (an error asks for inp.conductor if some lie outside CF(m)), and eigenphases=eigenvalues/eigenvalues[1], so for a 2x2 Unorm the relative phase is defined only up to inversion; Dt, clifford (and level with inp.maxlevel) only when KR is cyclic and kR lists the powers of kR[2] in order (the basis of the clock and shift of Dtilde)
RoughMergeSplit:=function(inp)
	local G,gs,KL,kL,vL,KR,kR,Hr,show,lab,labKR,labR,Rv,Lk,
	      GK,eGR,eKR,pGR,pKR,Hdr,first,inG,nrm,
	      Pid,PR,Pd,P,vid,U,n,vin,t,M,mu,Un,m,ev,cp,mult,Dt,res;
	#inp.G the (non-Abelian) code group of the middle patch, inp.gs its ordered elements, identity first (default Elements(G))
	#inp.KL the code group of the left patch, inp.kL its ordered elements, identity first (default Elements(KL)), inp.vL the logical input state in the basis kL
	#inp.HdL generators of K^diag in KL x G as pairs [k,g], inp.HdR generators of K^diag in G x KR as pairs [g,k]
	#inp.KR the code group of the right patch, inp.kR its ordered elements, identity first (default Elements(KR))
	#inp.Hr the boundary subgroup of G projected onto after the second merge (a subgroup or a list of generators, default trivial)
	#inp.maxlevel if bound, also return the Clifford level of the logical action, inp.conductor the m of the field CF(m) in which the eigenvalues are sought (default the conductor of the entries of Unorm)
	#inp.show true prints the intermediate states with the labels inp.lab, inp.labKR
	if not (IsRecord(inp) and ForAll(["G","KL","vL","HdL","KR","HdR"],
		f->IsBound(inp.(f)))) then
		ErrorNoReturn("RoughMergeSplit: inp needs G, KL, vL, HdL, KR and HdR");
	fi;
	G:=inp.G; KL:=inp.KL; KR:=inp.KR;
	if IsBound(inp.gs) then gs:=inp.gs; else gs:=Elements(G); fi;
	if IsBound(inp.kL) then kL:=inp.kL; else kL:=Elements(KL); fi;
	if IsBound(inp.kR) then kR:=inp.kR; else kR:=Elements(KR); fi;
	if not (IsEqualSet(gs,Elements(G)) and IsEqualSet(kL,Elements(KL))
		and IsEqualSet(kR,Elements(KR))) then
		ErrorNoReturn("RoughMergeSplit: gs, kL and kR must list the group elements");
	fi;
	if not (gs[1]=One(G) and kL[1]=One(KL) and kR[1]=One(KR)) then
		ErrorNoReturn("RoughMergeSplit: the identity must come first in gs, kL and kR");
	fi;
	vL:=inp.vL;
	if not Length(vL)=Length(kL) then
		ErrorNoReturn("RoughMergeSplit: vL must be a state in the basis kL");
	fi;
	if IsBound(inp.Hr) then Hr:=inp.Hr; else Hr:=Group(One(G)); fi;
	if not IsGroup(Hr) then Hr:=Group(Hr); fi;
	if IsBound(inp.show) then show:=inp.show; else show:=false; fi;
	if IsBound(inp.lab) then lab:=inp.lab; else lab:=List(gs,String); fi;
	if IsBound(inp.labKR) then labKR:=inp.labKR; else labKR:=List(kR,String); fi;
	labR:=List(Cartesian(lab,labKR),l->Concatenation(String(l[1])," ",String(l[2])));

	Rv:=Rvf(gs); Lk:=Lvf(kR);

	#merge the left patch into the D(G) patch by gauging K^diag <= KL x G
	first:=RoughMergeSplitStep(rec(A:=KL,B:=G,elsA:=kL,elsB:=gs,
		vA:=vL,vB:=id(gs)[1],Hd:=inp.HdL,
		readout:=rec(factor:=1,state:=id(kL)[1])));
	inG:=first.state;
	nrm:=first.weight;
	if nrm=0 then
		ErrorNoReturn("RoughMergeSplit: the merged state has no |1>_KL component");
	fi;
	#normalize only for a rational norm (GAP has no Sqrt of an irrational cyclotomic); U is rescaled by mu below anyway
	if IsRat(nrm) and nrm<>1 then inG:=inG/Sqrt(nrm); fi;
	if show then
		Print("\nstate merged into D(G):\n");
		ShowKet(inG,lab);
	fi;

	#merge the result into the right patch by gauging K^diag <= G x KR
	GK:=DirectProduct(G,KR);
	eGR:=Embedding(GK,1); eKR:=Embedding(GK,2);
	pGR:=Projection(GK,1); pKR:=Projection(GK,2);
	Hdr:=Group(List(inp.HdR,p->Image(eGR,p[1])*Image(eKR,p[2])),One(GK));
	Pd:=DiagProjector(rec(Hd:=Hdr,p1:=pGR,p2:=pKR,
		els1:=gs,els2:=kR,M1:=Rv,M2:=Lk));
	PR:=Kr(GroupProjector(gs,Rv,Hr),id(kR));
	#and measure the D(G) patch in its logical identity state
	vid:=id(gs)[1];
	Pid:=Kr(TransposedMat([vid])*[vid],id(kR));
	P:=Pid*PR*Pd;

	#the logical action on the right patch, one column per logical input
	U:=[];
	for n in [1..Length(kR)] do
		vin:=Kr([inG],[id(kR)[n]])[1];
		t:=P*vin;
		if show then
			Print("\ninput ",Showv(vin,labR),"\noutput ",Showv(t,labR),"\n");
		fi;
		Add(U,t{[1..Length(kR)]});
	od;
	U:=TransposedMat(U);

	M:=U*Dag(U);
	if not M=M[1][1]*id(kR) then
		ErrorNoReturn("RoughMergeSplit: the logical action is not a unitary");
	fi;
	mu:=M[1][1];
	if mu=0 then ErrorNoReturn("RoughMergeSplit: zero logical action"); fi;
	res:=rec(U:=U,mu:=mu,P:=P,inG:=inG);
	#U*Dag(U)=mu*1 was tested above; Unorm=U/Sqrt(mu) only for a rational mu (no Sqrt of an irrational cyclotomic in GAP), otherwise the eigenvalues are those of U (sqrt(mu) times those of the unitary), which leaves the eigenphases unchanged
	if IsRat(mu) then
		Un:=U/Sqrt(mu);
		res.Unorm:=Un;
	else
		Un:=U;
	fi;
	if IsBound(inp.conductor) then m:=inp.conductor; else m:=Conductor(Flat(Un)); fi;
	ev:=Eigenvalues(CF(m),Un);
	#Eigenvalues returns the distinct eigenvalues lying in CF(m): check that their algebraic multiplicities fill the spectrum
	cp:=CharacteristicPolynomial(Un);
	mult:=List(ev,function(e)
		local q,k;
		q:=cp; k:=0;
		while Value(q,e)=0 do k:=k+1; q:=Derivative(q); od;
		return k;
	end);
	if Sum(mult)<>Length(kR) then
		ErrorNoReturn("RoughMergeSplit: some eigenvalues are not in CF(",m,"); pass a larger inp.conductor");
	fi;
	res.eigenvalues:=ev; res.multiplicities:=mult; res.eigenphases:=ev/ev[1];
	#the clock and shift of Dtilde(d,1) act on the basis g^0,...,g^(d-1): only meaningful for kR the powers of a generator in order
	if Length(kR)>1 and kR=List([0..Length(kR)-1],j->kR[2]^j) then
		Dt:=Dtilde(Length(kR),1);
		res.Dt:=Dt;
		res.clifford:=IsClifford(U,Dt);
		if IsBound(inp.maxlevel) then
			res.level:=CliffordLevel(U,Dt,inp.maxlevel);
		fi;
	fi;
	return res;
end;


#############################################################################
##
## Constant-depth logical phase gates from 2-cocycles
##
## A 2-cocycle alpha stacked on a spatial slice, with a 1-cochain counterterm beta on each boundary, gives a topological logical gate. See arXiv:2512.13777.
##
#############################################################################

#IsCounterterm: tests whether a 1-cochain trivializes a 2-cocycle, alpha|_Els = delta beta, the condition for alpha to end on a boundary whose condensed subgroup has element list Els
#in: Els a list of group elements, alpha a 2-cocycle and beta a 1-cochain
#out: true if alpha(g,h)=beta(g)*beta(h)/beta(g*h) for all g,h in Els, false otherwise
IsCounterterm:=function(Els,alpha,beta)
	local g,h;
	#the inverse of the convention of IsTrivial2coc (03): beta=ComplexConjugate(c) for c:=IsTrivial2coc([Els,alpha])
	for g in Els do for h in Els do
		if not alpha(g,h)=beta(g)*beta(h)/beta(g*h) then return false; fi;
	od; od;
	return true;
end;

#LogicalUab: the logical gate of a triangular patch with three boundaries
#in: rec(alpha:=bulk 2-cocycle, beta:=[beta1,beta2,beta3] the boundary counterterms, g:=[g1,g2] the labels of the logical |1>)
#out: the 2x2 matrix diag(1,alpha(g1,g2)*beta3(g1g2)/(beta1(g1)beta2(g2)))
LogicalUab:=function(inp)
	local alpha,beta,g1,g2,one,phase;
	#the logical |0> is the configuration with no boundary-changing labels, the logical |1> the configuration (g1,g2,g1g2)
	if not (IsRecord(inp) and ForAll(["alpha","beta","g"],f->IsBound(inp.(f)))) then
		ErrorNoReturn("LogicalUab: inp needs alpha, beta and g");
	fi;
	alpha:=inp.alpha; beta:=inp.beta;
	if not Length(beta)=3 then ErrorNoReturn("LogicalUab: beta needs three entries"); fi;
	g1:=inp.g[1]; g2:=inp.g[2];
	one:=One(g1);
	if not alpha(one,one)*beta[3](one)/(beta[1](one)*beta[2](one))=1 then
		ErrorNoReturn("LogicalUab: the logical |0> is not left invariant");
	fi;
	phase:=alpha(g1,g2)*beta[3](g1*g2)/(beta[1](g1)*beta[2](g2));
	return DiagMat([1,phase]);
end;

#SPTStackingGate: the logical diagonal gate induced by a bulk 2-cocycle and three boundary counterterms
#in: rec(alpha,beta,g[,K]) with beta three boundary cochains, g two logical labels, and optional K three boundary subgroups
#out: the 2x2 logical gate, after checking supplied boundary counterterms and group membership
SPTStackingGate:=function(inp)
	local K,alpha,beta,g,Els,idx;
	if not (IsRecord(inp) and ForAll(["alpha","beta","g"],f->IsBound(inp.(f)))) then
		ErrorNoReturn("SPTStackingGate: expected rec(alpha,beta,g), optionally K");
	fi;
	alpha:=inp.alpha; beta:=inp.beta; g:=inp.g;
	if not Length(beta)=3 or not Length(g)=2 then
		ErrorNoReturn("SPTStackingGate: beta must have length 3 and g length 2");
	fi;
	if IsBound(inp.K) then
		K:=inp.K;
		if not Length(K)=3 then ErrorNoReturn("SPTStackingGate: K must list the three boundary subgroups"); fi;
		if not (g[1] in K[1] and g[2] in K[2] and g[1]*g[2] in K[3]) then
			ErrorNoReturn("SPTStackingGate: logical labels must lie in the three boundary subgroups");
		fi;
		for idx in [1..3] do
			if IsGroup(K[idx]) then Els:=Elements(K[idx]); else Els:=K[idx]; fi;
			if not IsCounterterm(Els,alpha,beta[idx]) then
				ErrorNoReturn("SPTStackingGate: boundary counterterm ",idx," fails");
			fi;
		od;
	fi;
	return LogicalUab(rec(alpha:=alpha,beta:=beta,g:=g));
end;

#PhaseGate: the single-qubit phase gate diag(1,e^{i pi/m})
#in: m a positive integer
#out: the 2x2 diagonal matrix DiagMat([1,E(2m)]), in level k+1 of the Clifford hierarchy for m=2^k (PhaseGate(1)=Z, PhaseGate(2)=S, PhaseGate(4)=T)
PhaseGate:=function(m)
	if not IsPosInt(m) then ErrorNoReturn("PhaseGate: m must be a positive integer"); fi;
	return DiagMat([1,E(2*m)]);
end;

#CCSgate: the multiply controlled S gate on nq qubits
#in: nq the number of qubits and pos a list of distinct qubits in [1..nq] (any order) that must be excited
#out: the diagonal matrix with E(4) on the basis state whose excited qubits are exactly pos and 1 elsewhere
CCSgate:=function(nq,pos)
	local bb,l,M,spos;
	#for pos other than [1..nq] this is a controlled S with zero-controls on the qubits outside pos (D4NPhaseGate uses pos=[1], the state |1 0...0>)
	if not IsPosInt(nq) then ErrorNoReturn("CCSgate: nq must be a positive integer"); fi;
	spos:=Set(pos);
	if Length(spos)<>Length(pos) or not IsSubset([1..nq],spos) then
		ErrorNoReturn("CCSgate: pos must be a list of distinct qubits in [1..",nq,"]");
	fi;
	bb:=Cartesian(List([1..nq],k->[0,1]));
	M:=[];
	for l in bb do
		if PosNonZero(l)=spos then Add(M,E(4)); else Add(M,1); fi;
	od;
	return DiagMat(M);
end;


#############################################################################
##
## The D_{4N} code family
##
## D_{4N} = < r,s | r^{4N}=s^2=1, s r s=r^{-1} > is the group behind the logical T^{1/N}=diag(1,e^{i pi/(4N)}) gates of arXiv:2510.20890 (by hybrid lattice surgery) and of arXiv:2512.13777 (in constant depth).
##
#############################################################################

#D4NData: the group D_{4N} with its element order, labels and qubit data
#in: N a positive integer
#out: rec(N,G,r,s,El,lab,glG,dits,ElF,gd,gl,n,bits,bb) with El the elements as r^a s^b, [a,b] in Cartesian([0..4N-1],[0,1]) (identity first), and n=log2(8N) the number of qubits of the physical realization when 8N is a power of 2, else fail
D4NData:=function(N)
	local G,Elold,r,s,dits,El,lab,k,str,ElF,n,bits,bb,gd,gl;
	if not IsPosInt(N) then ErrorNoReturn("D4NData: N must be a positive integer"); fi;
	G:=DihedralGroup(8*N);
	Elold:=Elements(G);
	r:=First(Elold,g->Order(g)=4*N);
	if r=fail then ErrorNoReturn("D4NData: no element of order 4N"); fi;
	s:=First(Elold,g->Order(g)=2 and g*r*g=r^-1);
	if s=fail then ErrorNoReturn("D4NData: no reflection inverting r"); fi;
	dits:=Cartesian([0..4*N-1],[0,1]);
	El:=List(dits,k->r^k[1]*s^k[2]);
	if not IsEqualSet(El,Elold) then ErrorNoReturn("D4NData: wrong r,s"); fi;
	lab:=[];
	for k in dits do
		str:="";
		if k[1]=1 then str:="r";
		elif k[1]>1 then str:=Concatenation("r^",String(k[1]));
		fi;
		if k[2]=1 then str:=Concatenation(str,"s"); fi;
		if str="" then str:="id"; fi;
		Add(lab,str);
	od;
	ElF:=List([0..4*N-1],k->r^k);
	gd:=function(g) return dits[Position(El,g)]; end;
	gl:=function(g) return lab[Position(El,g)]; end;
	n:=LogInt(8*N,2);
	if 2^n=8*N then
		bits:=Cartesian(List([1..n],k->[0,1]));
		bb:=Cartesian(List([1..n-1],k->[0,1]));
	else
		n:=fail; bits:=fail; bb:=fail;
	fi;
	return rec(N:=N,G:=G,r:=r,s:=s,El:=El,lab:=lab,glG:=[El,lab],dits:=dits,
		ElF:=ElF,gd:=gd,gl:=gl,n:=n,bits:=bits,bb:=bb);
end;

#D4NRecord: accepts N or an existing D4NData record
#in: N a positive integer, or a record returned by D4NData
#out: that record, computing it when only N is given
D4NRecord:=function(inp)
	if IsRecord(inp) then
		if not ForAll(["N","G","r","s","El","ElF","gd"],f->IsBound(inp.(f))) then
			ErrorNoReturn("expected N or a record returned by D4NData");
		fi;
		return inp;
	fi;
	return D4NData(inp);
end;

#D4NCocycle: the nontrivial class of H^2(D_{4N},U(1))=Z_2 with its counterterm on <r>
#in: N or a D4NData record
#out: rec(data,alpha1,kappa,alpha,br,brf,beta) with alpha=alpha1*delta(kappa) the 2-cocycle, trivial on <s> and on <rs>, and beta its counterterm on <r>, alpha|<r>=delta(beta) with beta(r)=e^{i pi/(4N)}
D4NCocycle:=function(inp)
	local data,N,r,s,El,ElF,gd,alpha1,kappa,alpha,br,brf,beta;
	data:=D4NRecord(inp);
	N:=data.N; r:=data.r; s:=data.s; El:=data.El; ElF:=data.ElF; gd:=data.gd;
	alpha1:=function(g1,g2)
		local l1,a,j,b;
		l1:=gd(g1);
		a:=l1[1];
		j:=l1[2];
		b:=gd(g2)[1];
		if (a+(1-2*j)*b) mod (8*N) >= (4*N) then return -1;
		else return +1;
		fi;
	end;
	if not (alpha1(r^(2*N),r^(2*N))=-1 and alpha1(s,s)=1 and alpha1(r*s,r*s)=1) then
		ErrorNoReturn("D4NCocycle: error in alpha1");
	fi;
	kappa:=function(g)
		local k;
		k:=gd(g);
		if k=[2*N,0] then return -E(4); fi;
		if k[1]>2*N and k[2]=0 then return -1; fi;
		return 1;
	end;
	alpha:=function(g1,g2)
		return alpha1(g1,g2)*kappa(g1)*kappa(g2)/kappa(g1*g2);
	end;
	#the boundary counterterm on <r>, fixed by beta(r)=e^{i pi/(4N)}; IsTrivial2coc reads the fixed value in units of 1/m, m=4 the common root order of alpha on <r>, so -1/(2N) is -1/(8N) turns and br(r)=E(8N) after the conjugation below
	br:=IsTrivial2coc([ElF,alpha,[[r,-1/(2*N)]]]);
	if br=fail then ErrorNoReturn("D4NCocycle: alpha is not trivial on <r>"); fi;
	br:=ComplexConjugate(br);
	brf:=function(g)
		local a;
		a:=gd(g)[1];
		if a<2*N then return E(8*N)^a;
		elif a=2*N then return 1;
		else return -E(8*N)^a;
		fi;
	end;
	if not br=List(ElF,brf) then ErrorNoReturn("D4NCocycle: error in br"); fi;
	beta:=function(g) return br[Position(ElF,g)]; end;
	if not IsCounterterm(ElF,alpha,beta) then
		ErrorNoReturn("D4NCocycle: beta is not a counterterm for alpha on <r>");
	fi;
	return rec(data:=data,alpha1:=alpha1,kappa:=kappa,alpha:=alpha,
		br:=br,brf:=brf,beta:=beta);
end;

#D4NCocycleRecord: accepts N, a D4NData record, or an existing D4NCocycle record
#in: N, a D4NData record, or a D4NCocycle record
#out: the D4NCocycle record, computing it when needed
D4NCocycleRecord:=function(inp)
	if IsRecord(inp) and IsBound(inp.alpha) then return inp; fi;
	return D4NCocycle(inp);
end;

#D4NCocycleTest: the slow cocycle identities for D_{4N}, checked on request
#in: N, a D4NData record, or a D4NCocycle record
#out: true, or an error naming the identity that failed
D4NCocycleTest:=function(inp)
	local coc,data,N,G,r,s,El,ElF,alpha1,alpha,gl,br1,ref,totest,g,g1,g2;
	#the identities of arXiv:2512.13777 too slow for every D4NCocycle call: alpha1 and alpha are 2-cocycles, alpha represents the nontrivial class, is trivial on <s> and on <rs>, and satisfies the two identities of Lemma 5.1
	coc:=D4NCocycleRecord(inp);
	data:=coc.data; N:=data.N; G:=data.G; r:=data.r; s:=data.s;
	El:=data.El; ElF:=data.ElF; gl:=data.gl;
	alpha1:=coc.alpha1; alpha:=coc.alpha;
	#m=2 for alpha1 on <r> (units 1/m, see D4NCocycle), so -1/(4N) is again -1/(8N) turns: br1(r)=E(8N)
	br1:=ComplexConjugate(IsTrivial2coc([ElF,alpha1,[[r,-1/(4*N)]]]));
	if not br1=List([0..(4*N-1)],k->E(8*N)^k) then
		ErrorNoReturn("D4NCocycleTest: error in br1");
	fi;
	if not (2coctest(El,alpha1)=true and 2coctest(El,alpha)=true) then
		ErrorNoReturn("D4NCocycleTest: alpha cocycle check failed");
	fi;
	ref:=gammaf(G)[2];
	totest:=function(g1,g2)
		return alpha(g1,g2)/ref(g1,g2);
	end;
	if IsTrivial2coc([El,totest])=fail then
		ErrorNoReturn("D4NCocycleTest: alpha is not the reference class");
	fi;
	#arXiv:2512.13777 Lemma 5.1: alpha normalized, alpha(g,g^-1)=1 and alpha(g^-1,h^-1)=alpha(h,g)^-1
	for g in El do
		if not (alpha(One(G),g)=1 and alpha(g,One(G))=1) then
			ErrorNoReturn("D4NCocycleTest: Lemma 5.1 normalization failed at ",gl(g));
		fi;
	od;
	for g in El do
		if not alpha(g,g^-1)=1 then
			ErrorNoReturn("D4NCocycleTest: Lemma 5.1 inverse identity failed at ",gl(g));
		fi;
	od;
	for g1 in El do for g2 in El do
		if not alpha(g1^-1,g2^-1)=alpha(g2,g1)^-1 then
			ErrorNoReturn("D4NCocycleTest: Lemma 5.1 reversal identity failed");
		fi;
	od; od;
	if not (IsTrivial2coc([[One(G),s],alpha,[[s,0]]])=[1,1] and
		IsTrivial2coc([[One(G),r*s],alpha,[[r*s,0]]])=[1,1]) then
		ErrorNoReturn("D4NCocycleTest: alpha is not trivial on <s> or <rs>");
	fi;
	if not alpha(r*s,s)=1 then
		ErrorNoReturn("D4NCocycleTest: alpha(rs,s) is not 1");
	fi;
	return true;
end;

#D4NPhaseGate: the constant-depth circuit for the counterterm beta on <r>=Z_{4N} and the logical gate it encodes
#in: N, a D4NData record, or a D4NCocycle record, with 8N a power of 2
#out: rec(coc,n,M1,M2,Mbeta,br,level,U) with Mbeta=M2*M1 the circuit on the n-1=log2(4N) qubits, M1 the tensor product of the phase gates P(2^k), M2=(Z tensor 1)*(multiply controlled S on |1 0...0>), level its Clifford level and U the logical gate U_{alpha,beta} at (g1,g2)=(rs,s)
D4NPhaseGate:=function(inp)
	local coc,data,N,n,br,x,z,CSl,M1,M2,xx,Mbeta,ftriv1,U,lvl;
	coc:=D4NCocycleRecord(inp);
	data:=coc.data; N:=data.N; n:=data.n; br:=coc.br;
	if n=fail then
		ErrorNoReturn("D4NPhaseGate: the qubit circuit needs 8N to be a power of 2");
	fi;
	x:=[[0,1],[1,0]];
	z:=DiagMat([1,-1]);
	#one phase gate per qubit
	M1:=Krl(List([1..n-1],k->PhaseGate(2^k)));
	#the standard multiply controlled S, conjugated onto the state |1 0...0>
	CSl:=List([1..2^(n-1)],k->1);
	CSl[2^(n-1)]:=E(4);
	xx:=Krl(Concatenation([id(2)],List([2..n-1],k->x)));
	M2:=Kr(z,id(2^(n-2)))*xx*DiagMat(CSl)*xx;
	if not M2=Kr(z,id(2^(n-2)))*CCSgate(n-1,[1]) then
		ErrorNoReturn("D4NPhaseGate: wrong controlled-S conjugation");
	fi;
	Mbeta:=M2*M1;
	if not (DiagonalOfMat(Mbeta)=br and Mbeta=DiagMat(br)) then
		ErrorNoReturn("D4NPhaseGate: wrong explicit phase matrix Mbeta");
	fi;
	lvl:=CliffordLevel(Mbeta,Dtilde(2,n-1),n);
	if not lvl=n then
		ErrorNoReturn("D4NPhaseGate: wrong reported Clifford-hierarchy level");
	fi;
	#alpha is trivial on the two reflection boundaries, so beta1=beta2=1
	ftriv1:=function(g) return 1; end;
	U:=SPTStackingGate(rec(alpha:=coc.alpha,beta:=[ftriv1,ftriv1,coc.beta],
		K:=[Group(data.r*data.s),Group(data.s),Group(data.r)],
		g:=[data.r*data.s,data.s]));
	if not U=DiagMat([1,E(8*N)]) then
		ErrorNoReturn("D4NPhaseGate: the logical gate is not T^{1/N}");
	fi;
	if not CliffordLevel(U,Dtilde(2,1),n)=n then
		ErrorNoReturn("D4NPhaseGate: wrong logical Clifford-hierarchy level");
	fi;
	return rec(coc:=coc,n:=n,M1:=M1,M2:=M2,Mbeta:=Mbeta,br:=br,level:=lvl,U:=U);
end;

#QuditSState: the Z_d stabilizer state |S> = (1/sqrt(d)) sum_j e^{i pi j^2/d} |m^j>, the input of the hybrid lattice surgery for d=4N
#in: d an integer >= 2
#out: the vector (1/sqrt(d))*[E(2d)^(j^2)] of length d
QuditSState:=function(d)
	if not IsInt(d) or d<2 then ErrorNoReturn("d must be an integer >= 2"); fi;
	return 1/Sqrt(d)*List([0..d-1],j->E(2*d)^(j^2));
end;

#D4NSurgeryGate: the T^{1/N} logical gate obtained by hybrid lattice surgery (arXiv:2510.20890)
#in: (N[,show]) with N a positive integer and show true to print the intermediate states
#out: the RoughMergeSplit record with the extra field phase=E(8N) or E(8N)^-1 (the same gate up to conjugation by X and a global phase, which one depends on the order of Eigenvalues)
D4NSurgeryGate:=function(arg)
	local N,show,data,G,r,s,d,KL,a,kL,KR,m,kR,res;
	#the protocol: merge a D(Z_{4N}) patch prepared in |S> into a D(D_{4N}) patch by gauging Z_{4N}^diag=<(m,r)>, split, merge the result into a D(Z_2) patch by gauging <(r^{2N},m),(rs,1)>, project on the boundary subgroup <s> and read the D(D_{4N}) patch in <id|
	N:=arg[1];
	if not IsPosInt(N) then ErrorNoReturn("D4NSurgeryGate: N must be a positive integer"); fi;
	if Length(arg)>1 then show:=arg[2]; else show:=false; fi;
	d:=4*N;
	data:=D4NData(N);
	G:=data.G; r:=data.r; s:=data.s;
	KL:=CyclicGroup(d);
	a:=First(Elements(KL),g->Order(g)=d);
	kL:=List([0..d-1],j->a^j);
	KR:=CyclicGroup(2);
	m:=First(Elements(KR),g->Order(g)=2);
	kR:=[One(KR),m];
	res:=RoughMergeSplit(rec(G:=G,gs:=data.El,lab:=data.lab,
		KL:=KL,kL:=kL,vL:=QuditSState(d),HdL:=[[a,r]],
		KR:=KR,kR:=kR,labKR:=["1","m"],
		HdR:=[[r^(2*N),m],[r*s,One(KR)]],
		Hr:=Group(s),show:=show));
	res.phase:=res.eigenphases[2];
	if not (res.phase=E(8*N) or res.phase=ComplexConjugate(E(8*N))) then
		ErrorNoReturn("D4NSurgeryGate: unexpected logical eigenphases");
	fi;
	if not res.clifford=false then
		ErrorNoReturn("D4NSurgeryGate: the logical gate should be non-Clifford");
	fi;
	return res;
end;
