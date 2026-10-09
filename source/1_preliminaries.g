#############################################################################
##
## source/1_preliminaries.g           AlgebrasTQD
##
## Preliminary helpers and labels for group elements.
##
## Functions in this file (the first line of each header):
## - GroupData: the mutable generator and element-label record attached to a group
## - MakeGroupLabels: a readable label for every element of a group, from labelled generators
## - AttachGroupLabels: stores labelled generators with a group while retaining GAP's own generators
## - MakeGroup: a group with labelled generators, from a name, a SmallGroup id or a group
## - GroupElement: the element of a group given by a word in its generator labels
## - GroupLabel: the label of an element of a group
## - RelabelGroup: new labelled generators for a group, given as words in its current labels
## - DisplayGroupLabels: a group by generators and relations
## - ShowGroup: prints a group with its labelled generators, its relations and the labels of all its elements
## - Posinlist: finds the first sublist containing an element
## - Possinlist: finds every sublist containing an element
## - IsNonNegIntv: tests whether a list consists of non-negative integers
## - PosNonZero: positions of the nonzero entries of a vector
## - Reshape: turns a flat list into a matrix with rows of a given length
## - TODO SolveModZ: solves A*x=b mod 1 exactly, by the Hermite normal form of the integer system [A | D*b]
## - id: identity matrix of a given size
## - Kr: Kronecker product of two matrices
## - Krl: iterated Kronecker product of a list of matrices
## - Dag: conjugate transpose of a matrix
## - add1: increments a digit vector whose digits run from 0
##
#############################################################################

#GroupData: the generators and their labels attached to a group by MakeGroup, RelabelGroup or MakeGroupLabels, a mutable record rec(gens,labels), with the fields elements and elementLabels once MakeGroupLabels has labelled every element (mutable, so that new labels replace old ones: a set attribute cannot be set again)
if not IsBound(GroupData) then
	DeclareAttribute("GroupData",IsGroup,"mutable");
fi;

#MakeGroupLabels: a readable label for every element of a group, from labelled generators
#in: [G], or [G,ElG] with ElG the elements of G in a chosen order or [G,gens,labels] with gens the group's generators and labels the strings for their labels
#out: [elements,labels,gens], labels one string per element of G
MakeGroupLabels:=function(inp)
	local G,ElG,gen,pos,i,known,known2,labG,labG2,knownPos,powstr,gel,genkey,genlabs,merge,nin,s,s1,s2,gsl,l,lt,n,g1,g2,g,x,gp,d;
	if not IsList(inp) or not Length(inp) in [1,2,3] or
	   not IsGroup(inp[1]) then
		ErrorNoReturn("MakeGroupLabels: give [G], [G,elements] or [G,generators,labels], e.g. MakeGroupLabels([G,[r,s],[\"r\",\"s\"]]) (or use RelabelGroup)");
	fi;
	G:=inp[1];
	if Length(inp)=1 then
		ElG:=Elements(G);
	elif Length(inp)=2 then
		ElG:=Elements(G);
		if Length(inp[2])<>Size(G) or not IsEqualSet(inp[2],ElG) then
			ErrorNoReturn("MakeGroupLabels: in [G,elements] the list must contain every element of G exactly once");
		fi;
		ElG:=inp[2];
	fi;
	#the labels of every element are stored with the attached generators, and computed only once
	if Length(inp) in [1,2] and HasGroupData(G) and IsBound(GroupData(G).elements) then
		d:=GroupData(G);
		if Length(inp)=1 then
			return [ShallowCopy(d.elements),ShallowCopy(d.elementLabels),ShallowCopy(d.gens)];
		fi;
		return [ShallowCopy(inp[2]),List(inp[2],g->d.elementLabels[Position(d.elements,g)]),ShallowCopy(d.gens)];
	fi;
	if Length(inp) in [1,2] and HasGroupData(G) then
		gen:=GroupData(G).gens;
		labG:=Concatenation(["1"],GroupData(G).labels);
		known:=Concatenation([One(G)],gen);
	elif Length(inp) in [1,2] then
		gen:=GeneratorsOfGroup(G);
		labG:=Concatenation(["1"],List(gen,g->String(g)));
		known:=Concatenation([One(G)],gen);
	elif Length(inp)=3 then
		if (IsEmpty(inp[2]) and not IsTrivial(G)) or (not IsEmpty(inp[2]) and Group(inp[2])<>G) then
			ErrorNoReturn("MakeGroupLabels: the generators ",inp[2]," do not generate G");
		fi;
		if not Length(inp[3])=Length(inp[2]) then
			ErrorNoReturn("MakeGroupLabels: give one label per generator (",Length(inp[2])," generators, ",Length(inp[3])," labels)");
		fi;
		if not ForAll(inp[3],l->IsString(l) and l<>"") then
			ErrorNoReturn("MakeGroupLabels: the labels must be nonempty strings, e.g. [\"r\",\"s\"]");
		fi;
		gen:=inp[2];
		labG:=Concatenation(["1"],inp[3]);
		known:=Concatenation([One(G)],gen);
	fi;

	known2:=[];
	labG2:=[];
	for i in [1..Length(known)] do
		pos:=Position(known2,known[i]);
		if pos=fail then
			Add(known2,known[i]);
			Add(labG2,labG[i]);
		else
			Print("#info: MakeGroupLabels: ",labG[i]," is the same element as ",labG2[pos],", the label ",labG[i]," is not used\n");
		fi;
	od;
	known:=known2;
	labG:=labG2;
	#element -> its position in known, so the search below never calls Position on a list that grows to the whole group.
	knownPos:=NewDictionary(One(G),true,G);
	for i in [1..Length(known)] do AddDictionary(knownPos,known[i],i); od;
	ElG:=Elements(G);
	ElG:=Concatenation(known,Difference(ElG,known));

	if not IsEqualSet(known,ElG) then
		powstr:=function(nin)
			local s;
			return Concatenation("^",String(nin));
		end;
		#genkey: the positions in gen of the generators in the label s, in the order they appear (exponents skipped)
		genlabs:=ShallowCopy(labG{[2..Length(labG)]});
		gsl:=ShallowCopy(genlabs);
		SortBy(gsl,t->-Length(t));
		genkey:=function(s)
			local key,i,t;
			key:=[];
			i:=1;
			while i<=Length(s) do
				if s[i]='^' then
					i:=i+1;
					while i<=Length(s) and (IsDigitChar(s[i]) or s[i]='-') do i:=i+1; od;
				else
					t:=First(gsl,t->i+Length(t)-1<=Length(s) and s{[i..i+Length(t)-1]}=t);
					if t=fail then
						i:=i+1;
					else
						Add(key,Position(genlabs,t));
						i:=i+Length(t);
					fi;
				fi;
			od;
			return key;
		end;
		#gel: true if the label s2 is preferred to s1: shorter, then fewer factors, then the generators in the order given
		gel:=function(s1,s2)
			local k1,k2;
			if Length(s1)<>Length(s2) then return Length(s1)>Length(s2); fi;
			k1:=genkey(s1);
			k2:=genkey(s2);
			if Length(k1)<>Length(k2) then return Length(k1)>Length(k2); fi;
			return k2<k1;
		end;

		repeat
			for g1 in known do
				l:=labG[LookupDictionary(knownPos,g1)];
				if not '^' in l then
					n:=Order(g1);
					for x in [1..n-1] do
						g:=g1^x;
						if l in genlabs then
							lt:=Concatenation(l,powstr(x));
						else
							lt:=Concatenation("(",l,")",powstr(x));
						fi;
						pos:=LookupDictionary(knownPos,g);
						if pos=fail then
							Add(known,g);
							Add(labG,lt);
							AddDictionary(knownPos,g,Length(known));
						elif gel(labG[pos],lt) then
							labG[pos]:=lt;
						fi;
					od;
				fi;
				for g2 in known do
					l:=labG[LookupDictionary(knownPos,g2)];
					if not '^' in l then
						n:=Order(g2);
						for x in [1..n-1] do
							g:=g2^x;
							if l in genlabs then
								lt:=Concatenation(l,powstr(x));
							else
								lt:=Concatenation("(",l,")",powstr(x));
							fi;
							pos:=LookupDictionary(knownPos,g);
							if pos=fail then
								Add(known,g);
								Add(labG,lt);
								AddDictionary(knownPos,g,Length(known));
							elif gel(labG[pos],lt) then
								labG[pos]:=lt;
							fi;
						od;
					fi;

					if IsOne(g1) or IsOne(g2) then continue; fi;
					l:=Concatenation(labG[LookupDictionary(knownPos,g1)],labG[LookupDictionary(knownPos,g2)]);
					g:=g1*g2;
					pos:=LookupDictionary(knownPos,g);
					if pos=fail then
						Add(known,g);
						Add(labG,l);
						AddDictionary(knownPos,g,Length(known));
						if not '^' in l then
							n:=Order(g);
							for x in [1..n-1] do
								gp:=g^x;
								if l in genlabs then
									lt:=Concatenation(l,powstr(x));
								else
									lt:=Concatenation("(",l,")",powstr(x));
								fi;
								pos:=LookupDictionary(knownPos,gp);
								if pos=fail then
									Add(known,gp);
									Add(labG,lt);
									AddDictionary(knownPos,gp,Length(known));
								elif gel(labG[pos],lt) then
									labG[pos]:=lt;
								fi;
							od;
						fi;
					elif gel(labG[pos],l) then
						labG[pos]:=l;
					fi;
				od;
			od;
		until IsEqualSet(known,ElG);
		#a power label is built from the label its base had at that moment, which may have been improved later ("(aab)^2" for a^2b): merge equal neighbouring factors in every label (same element, never longer)
		merge:=function(s)
			local fs,i,depth,j,b,e,out,f;
			#fs: the factors [base,exponent] of s at bracket depth 0
			fs:=[];
			i:=1;
			while i<=Length(s) do
				if s[i]='(' then
					depth:=1; j:=i;
					while depth>0 do
						j:=j+1;
						if s[j]='(' then depth:=depth+1; elif s[j]=')' then depth:=depth-1; fi;
					od;
					b:=Concatenation("(",merge(s{[i+1..j-1]}),")");
					i:=j+1;
				else
					b:=First(gsl,t->i+Length(t)-1<=Length(s) and s{[i..i+Length(t)-1]}=t);
					if b=fail then return s; fi;
					i:=i+Length(b);
				fi;
				e:=1;
				if i<=Length(s) and s[i]='^' then
					j:=i+1;
					if s[j]='-' then j:=j+1; fi;
					while j<=Length(s) and IsDigitChar(s[j]) do j:=j+1; od;
					e:=Int(s{[i+1..j-1]});
					i:=j;
				fi;
				if fs<>[] and Last(fs)[1]=b then Last(fs)[2]:=Last(fs)[2]+e; else Add(fs,[b,e]); fi;
			od;
			out:=[];
			for f in fs do
				if f[2]=1 then Add(out,f[1]); elif f[2]<>0 then Add(out,Concatenation(f[1],"^",String(f[2]))); fi;
			od;
			if out=[] then return "1"; fi;
			return Concatenation(out);
		end;
		for i in [2..Length(labG)] do
			if not labG[i] in genlabs then labG[i]:=merge(labG[i]); fi;
		od;
	fi;
	if Length(known)<>Length(labG) then
		ErrorNoReturn("MakeGroupLabels: internal error (elements and labels of different lengths)");
	fi;
	if Length(known)<>Length(ElG) then
		ErrorNoReturn("MakeGroupLabels: internal error (not every element of G labelled once)");
	fi;
	if Length(Set(labG))<>Length(labG) then
		ErrorNoReturn("MakeGroupLabels: two elements got the same label ",First(labG,l->Number(labG,m->m=l)>1),
			"; choose generator labels whose products cannot be confused (not \"a\" and \"ab\")");
	fi;
	if not IsEqualSet(known,ElG) then
		ErrorNoReturn("MakeGroupLabels: internal error (labelled elements are not the elements of G)");
	fi;
	if Length(inp)=3 and HasGroupData(G) then
		GroupData(G).gens:=ShallowCopy(inp[2]);
		GroupData(G).labels:=ShallowCopy(inp[3]);
	elif Length(inp)=3 then
		SetGroupData(G,rec(gens:=ShallowCopy(inp[2]),labels:=ShallowCopy(inp[3])));
	fi;
	#here the generators are the attached ones (attached just above for [G,gens,labels])
	if HasGroupData(G) then
		GroupData(G).elements:=ShallowCopy(known);
		GroupData(G).elementLabels:=ShallowCopy(labG);
	fi;
	if Length(inp)=2 then
		labG:=List(inp[2],g->labG[LookupDictionary(knownPos,g)]);
		known:=ShallowCopy(inp[2]);
	fi;

	return [known,labG,gen];
end;

#MakeGroupCache: the groups made by MakeGroup from a name or an id, one SmallGroup(id) object per id (so that cocycles, anyons and algebras of different calls match)
if not IsBound(MakeGroupCache) then
	MakeGroupCache:=[];
fi;

#AttachGroupLabels: stores labelled generators with a group, for all labelling; GAP keeps its own generators (the pc generators of a SmallGroup) for the calculations, so the group itself is not changed
#in: (G,gens,labels[,meaning]) with gens elements generating G, labels their labels (strings), meaning optional lines saying what they stand for
#out: G, with GroupData(G).gens = gens and GroupData(G).labels = labels (replacing any stored before)
AttachGroupLabels:=function(arg)
	local G;
	G:=arg[1];
	MakeGroupLabels([G,arg[2],arg[3]]);
	if Length(arg)>3 and arg[4]<>[] then GroupData(G).meaning:=arg[4]; else Unbind(GroupData(G).meaning); fi;
	return G;
end;

#MakeGroup: a group with labelled generators, from a name, a SmallGroup id or a group
#in: (spec[,maxorder][,"gap"][,labels,words]) with spec a name ("C2 x C3" or "C2C3", "D8", "C3 : C4", factors in any order), [n,i] or a group, maxorder (default 32) bounds the search for names that are not direct products, the option "gap" keeps GAP's labels, the option [labels, words] uses the new labels for the old or default words
#out: SmallGroup(n,i), the same object on every call, with the labelled generators in GroupData(G): a, b, ... (cyclic, Sn, An), r, s (dihedral, S3), i, j (quaternion), else a, b, ... on a smallest generating set
MakeGroup:=function(arg)
	local spec,maxorder,gapLabels,a,s,orders,found,G,H,norm,canon,target,factorsOf,productOf,cached,fromProduct,
		letters,gapGens,labelled,n,P;
	norm:=s->Filtered(s,c->c<>' ');
	#factorsOf: the factors [letter,n] of a direct product of Cn, Dn, Qn, Sn, An, with or without x between factors, else fail
	factorsOf:=function(s)
		local fs,c,n,i,j;
		if s="1" then return []; fi;
		fs:=[];
		i:=1;
		while i<=Length(s) do
			if not s[i] in "CDQSA" then return fail; fi;
			c:=s[i];
			i:=i+1;
			j:=i;
			while i<=Length(s) and s[i] in "0123456789" do i:=i+1; od;
			if i=j then return fail; fi;
			n:=Int(s{[j..i-1]});
			if n<1 or (c='D' and (n<4 or IsOddInt(n)))
			   or (c='Q' and (n<8 or n mod 4<>0)) then
				return fail;
			fi;
			Add(fs,[c,n]);
			if i<=Length(s) and s[i]='x' then
				i:=i+1;
				if i>Length(s) then return fail; fi;
			fi;
		od;
		if fs=[] then return fail; fi;
		return fs;
	end;
	#productOf: rec(D,gens,labels,meaning) with D the direct product (a permutation group) of the factors fs, gens their generators in D, labels their labels and meaning the lines naming the permutations of the Sn, An factors
	productOf:=function(fs)
		local letters,nD,nQ,iC,iD,iQ,F,gens,labs,meaning,f,c,n,X,x,y,suf,embs,D,toPerm,iso,g;
		letters:="abcdefghklmnopqtuvwxyz";
		#S2, A3 are cyclic and S3 dihedral; A1, A2, S1, C1 trivial
		fs:=List(fs,function(f)
			if f[1]='S' and f[2]=3 then return ['D',6];
			elif (f[1]='S' and f[2]=2) or (f[1]='A' and f[2]=3) then return ['C',f[2]];
			elif (f[1]='S' and f[2]=1) or (f[1]='A' and f[2]<3) then return ['C',1];
			else return f; fi;
		end);
		nD:=Number(fs,f->f[1]='D');
		nQ:=Number(fs,f->f[1]='Q');
		iC:=0; iD:=0; iQ:=0;
		F:=[]; gens:=[]; labs:=[]; meaning:=[];
		#toPerm: a permutation group isomorphic to X, and the images of the elements xs
		toPerm:=function(X,xs)
			iso:=IsomorphismPermGroup(X);
			return [Image(iso),List(xs,g->Image(iso,g))];
		end;
		for f in fs do
			c:=f[1]; n:=f[2];
			if c='C' and n=1 then
				Add(F,Group(()));
				Add(gens,[]); Add(labs,[]);
			elif c='C' then
				if iC+1>Length(letters) then return fail; fi;
				iC:=iC+1;
				X:=CyclicGroup(IsPermGroup,n);
				Add(F,X); Add(gens,[MinimalGeneratingSet(X)[1]]); Add(labs,[[letters[iC]]]);
			elif c='D' then
				iD:=iD+1;
				if nD>1 then suf:=String(iD); else suf:=""; fi;
				X:=DihedralGroup(IsPermGroup,n);
				#r: a rotation (order n/2, for D4 any element of order 2), s: a reflection (order 2, outside <r>)
				x:=First(Elements(X),g->Order(g)=n/2);
				y:=First(Elements(X),g->Order(g)=2 and not g in Group(x));
				Add(F,X); Add(gens,[x,y]); Add(labs,[Concatenation("r",suf),Concatenation("s",suf)]);
			elif c='Q' then
				iQ:=iQ+1;
				if nQ>1 then suf:=String(iQ); else suf:=""; fi;
				X:=QuaternionGroup(IsPcGroup,n);
				#i: an element of order n/2, j: an element of order 4 outside <i>
				x:=First(Elements(X),g->Order(g)=n/2);
				y:=First(Elements(X),g->Order(g)=4 and not g in Group(x));
				X:=toPerm(X,[x,y]);
				Add(F,X[1]); Add(gens,X[2]); Add(labs,[Concatenation("i",suf),Concatenation("j",suf)]);
			else
				if c='S' then X:=SymmetricGroup(n); else X:=AlternatingGroup(n); fi;
				x:=GeneratorsOfGroup(X);
				if iC+Length(x)>Length(letters) then return fail; fi;
				y:=List([1..Length(x)],k->[letters[iC+k]]);
				iC:=iC+Length(x);
				Add(meaning,Concatenation(JoinStringsWithSeparator(List([1..Length(x)],k->Concatenation(y[k]," = ",String(x[k]))),", ")," in ",[c],String(n)));
				Add(F,X); Add(gens,x); Add(labs,y);
			fi;
		od;
		if Length(F)=0 then
			D:=Group(());
			embs:=[];
		elif Length(F)=1 then
			D:=F[1];
			embs:=[IdentityMapping(D)];
		else
			D:=DirectProduct(F);
			embs:=List([1..Length(F)],k->Embedding(D,k));
		fi;
		return rec(D:=D,gens:=Concatenation(List([1..Length(F)],k->List(gens[k],g->Image(embs[k],g)))),
			labels:=Concatenation(labs),meaning:=meaning);
	end;
	#cached: SmallGroup(id), the same object on every call (MakeGroupCache)
	cached:=function(id)
		local H;
		H:=First(MakeGroupCache,H->IdGroup(H)=id);
		if H=fail then
			H:=SmallGroup(id);
			Add(MakeGroupCache,H);
		fi;
		return H;
	end;
	#each of the following returns rec(gens,labels,meaning) for the generators of G
	#fromProduct: the generators of the factors of the product P (rec as returned by productOf, D isomorphic to G)
	fromProduct:=function(G,P)
		local iso;
		iso:=IsomorphismGroups(P.D,G);
		return rec(gens:=List(P.gens,g->Image(iso,g)),labels:=P.labels,meaning:=P.meaning);
	end;
	#letters: a smallest generating set of G labelled a, b, c, ..., with what the letters stand for
	letters:=function(G)
		local abc,gens,labs;
		if IsSolvableGroup(G) then gens:=MinimalGeneratingSet(G); else gens:=SmallGeneratingSet(G); fi;
		abc:="abcdefghklmnopqtuvwxyz";
		labs:=List([1..Length(gens)],k->[abc[k]]);
		if gens=[] then return rec(gens:=[],labels:=[],meaning:=[]); fi;
		return rec(gens:=gens,labels:=labs,meaning:=[JoinStringsWithSeparator(List([1..Length(gens)],k->Concatenation(labs[k],
			" = ",String(gens[k])," of order ",String(Order(gens[k])))),", ")]);
	end;
	#gapGens: GAP's generators of G (the pcgs f1, f2, ... for a pc-group) labelled as GAP prints them
	gapGens:=function(G)
		local gens;
		if IsPcGroup(G) then gens:=AsList(Pcgs(G)); else gens:=GeneratorsOfGroup(G); fi;
		return rec(gens:=gens,labels:=List(gens,String),meaning:=[]);
	end;
	#labelled: G with the labelled generators for its name s (without spaces) stored: the factors of a direct product, else letters, or GAP's generators with "gap"
	labelled:=function(G,s)
		local P,L,l;
		if gapLabels then
			L:=gapGens(G);
		else
			P:=factorsOf(s);
			if P<>fail then P:=productOf(P); fi;
			if P<>fail then
				#generators already stored with these labels and orders are kept (IsomorphismGroups may choose other generators of the same orders on every call)
				if HasGroupData(G) and GroupData(G).labels=P.labels and
				   List(GroupData(G).gens,Order)=List(P.gens,Order) then
					for L in P.meaning do Print("#I  MakeGroup: ",L,"\n"); od;
					return G;
				fi;
				L:=fromProduct(G,P);
			else
				L:=letters(G);
			fi;
		fi;
		for l in L.meaning do Print("#I  MakeGroup: ",l,"\n"); od;
		return AttachGroupLabels(G,L.gens,L.labels,L.meaning);
	end;
	#new generators as words: MakeGroup(spec,...,labels,words) is MakeGroup(spec,...) followed by RelabelGroup
	if Length(arg)>=3 and IsList(arg[Length(arg)-1]) and not IsString(arg[Length(arg)-1])
	   and IsList(Last(arg)) and not IsString(Last(arg)) then
		G:=CallFuncList(MakeGroup,arg{[1..Length(arg)-2]});
		return RelabelGroup(G,arg[Length(arg)-1],Last(arg));
	fi;
	spec:=arg[1];
	maxorder:=32;
	gapLabels:=false;
	for a in arg{[2..Length(arg)]} do
		if a="gap" then gapLabels:=true;
		elif IsPosInt(a) then maxorder:=a;
		else ErrorNoReturn("MakeGroup: the options are a maximal order (a positive integer), \"gap\", and new labels with their words (two lists), not ",a);
		fi;
	od;
	if IsGroup(spec) then
		if HasGroupData(spec) and not gapLabels then return spec; fi;
		return labelled(spec,norm(StructureDescription(spec)));
	fi;
	if IsList(spec) and Length(spec)=2 and ForAll(spec,IsPosInt) then
		G:=cached(spec);
		return labelled(G,norm(StructureDescription(G)));
	fi;
	if not IsString(spec) then
		ErrorNoReturn("MakeGroup: give a group, [n,i] or a name such as \"D8\" or \"C2 x C3\"");
	fi;
	s:=norm(spec);
	#a direct product of Cn, Dn, Qn, Sn, An: built from its factors, so that any spelling is accepted
	P:=factorsOf(s);
	if P<>fail then P:=productOf(P); fi;
	if P<>fail then
		if not IdGroupsAvailable(Size(P.D)) then
			#no SmallGroup id for this order: the product itself
			G:=P.D;
		else
			G:=cached(IdGroup(P.D));
		fi;
		return labelled(G,s);
	fi;
	#any other name: compared with StructureDescription, the factors of every direct product in any order
	#canon: a name without spaces with the factors of every direct product sorted; a level with a ':' or '.' outside brackets is not reordered
	canon:=function(s)
		local parts,cur,mixed,depth,i,j;
		parts:=[];
		cur:="";
		mixed:=false;
		i:=1;
		while i<=Length(s) do
			if s[i]='(' then
				depth:=1;
				j:=i;
				while depth>0 and j<Length(s) do
					j:=j+1;
					if s[j]='(' then depth:=depth+1; elif s[j]=')' then depth:=depth-1; fi;
				od;
				if depth>0 then return s; fi;
				Append(cur,Concatenation("(",canon(s{[i+1..j-1]}),")"));
				i:=j+1;
			else
				if s[i]='x' then
					Add(parts,cur);
					cur:="";
				else
					if s[i] in ":." then mixed:=true; fi;
					Add(cur,s[i]);
				fi;
				i:=i+1;
			fi;
		od;
		Add(parts,cur);
		if mixed then return JoinStringsWithSeparator(parts,"x"); fi;
		return JoinStringsWithSeparator(SortedList(parts),"x");
	end;
	target:=canon(s);
	found:=[];
	for n in [1..maxorder] do
		for H in AllSmallGroups(n) do
			if canon(norm(StructureDescription(H)))=target then Add(found,H); fi;
		od;
		if found<>[] then break; fi;
	od;
	if Length(found)=1 then
		return labelled(cached(IdGroup(found[1])),s);
	fi;
	if found=[] then
		ErrorNoReturn("MakeGroup: no group of order at most ",maxorder," has the name ",spec,
			" (give a direct product such as \"C2 x D8\", GAP's name as printed by StructureDescription, e.g. \"C3 : C4\",",
			" or MakeGroup(name,maxorder) to search larger orders)");
	fi;
	ErrorNoReturn("MakeGroup: the name ",spec," is ambiguous, use one of the ids ",List(found,IdGroup));
end;

#GroupElement: the element of a group given by a word in its generator labels
#in: (G,word) with word a string in the labels of the generators of G (see MakeGroupLabels([G])[3]), "1", products (written as MakeGroupLabels writes them, without *, or with *), powers ^n (n may be negative) and brackets, e.g. "cab", "r^2s", "(rs)^-1", "c*a*b"; spaces ignored
#out: the element of G labelled by word
GroupElement:=function(G,word)
	local gl,gens,labs,order,w,i,x,fail_at,expr,term,atom,int;
	gl:=MakeGroupLabels([G]);
	gens:=gl[3];
	labs:=gl[2]{List(gens,g->Position(gl[1],g))};
	#longest labels first, so that r10 is not read as r1 followed by 0
	order:=ShallowCopy([1..Length(labs)]);
	SortBy(order,k->-Length(labs[k]));
	w:=Filtered(word,c->c<>' ');
	i:=1;
	fail_at:=function()
		ErrorNoReturn("GroupElement: cannot read \"",word,"\" at \"",w{[i..Length(w)]},"\"; the generators of G are ",labs);
	end;
	int:=function()
		local j,sgn;
		if i<=Length(w) and w[i]='{' then i:=i+1; fi;
		sgn:=1;
		if i<=Length(w) and w[i]='-' then sgn:=-1; i:=i+1; fi;
		j:=i;
		while i<=Length(w) and IsDigitChar(w[i]) do i:=i+1; od;
		if i=j then fail_at(); fi;
		j:=sgn*Int(w{[j..i-1]});
		if i<=Length(w) and w[i]='}' then i:=i+1; fi;
		return j;
	end;
	atom:=function()
		local x,k;
		if i<=Length(w) and w[i]='(' then
			i:=i+1;
			x:=expr();
			if i>Length(w) or w[i]<>')' then fail_at(); fi;
			i:=i+1;
			return x;
		fi;
		k:=First(order,k->i+Length(labs[k])-1<=Length(w) and w{[i..i+Length(labs[k])-1]}=labs[k]);
		if k<>fail then
			i:=i+Length(labs[k]);
			return gens[k];
		elif i<=Length(w) and w[i]='1' then
			i:=i+1;
			return One(G);
		fi;
		fail_at();
	end;
	term:=function()
		local x;
		x:=atom();
		while i<=Length(w) and w[i]='^' do
			i:=i+1;
			x:=x^int();
		od;
		return x;
	end;
	expr:=function()
		local x;
		x:=term();
		#a product is written without * ("cab", as MakeGroupLabels writes it) or with it ("c*a*b")
		while i<=Length(w) and (w[i]='*' or w[i]='(' or IsAlphaChar(w[i])) do
			if w[i]='*' then i:=i+1; fi;
			x:=x*term();
		od;
		return x;
	end;
	if w="" then fail_at(); fi;
	x:=expr();
	if i<=Length(w) then fail_at(); fi;
	return x;
end;

#GroupLabel: the label of an element of a group
#in: (G,g) with g an element of G
#out: the label of g, as in MakeGroupLabels([G]) (from the generators attached by MakeGroup or RelabelGroup)
GroupLabel:=function(G,g)
	local gl,pos;
	gl:=MakeGroupLabels([G]);
	pos:=Position(gl[1],g);
	if pos=fail then ErrorNoReturn("GroupLabel: ",g," is not an element of G"); fi;
	return gl[2][pos];
end;

#RelabelGroup: new labelled generators for a group, given as words in its current labels
#in: (G,"gap") for GAP's generators and labels, or (G,labels,words) with labels the new generator labels, e.g. ["c","a","b"] (letters and digits, starting with a letter; no label another label followed by letters), and words the generators, each a word in the current labels of G (see GroupElement) or an element of G, e.g. ["sr","s","sr^2"]; when two labels of an element are equally short, the one following the order of labels is used, so list first the generator to be written on the left
#out: G, with the new generators and labels stored in GroupData(G) (used for all labelling; GAP keeps its own generators for the calculations)
RelabelGroup:=function(arg)
	local G,labels,words,gens;
	G:=arg[1];
	if Length(arg)=2 and arg[2]="gap" then
		if IsPcGroup(G) then gens:=AsList(Pcgs(G)); else gens:=GeneratorsOfGroup(G); fi;
		return AttachGroupLabels(G,gens,List(gens,String));
	fi;
	if Length(arg)<>3 then
		ErrorNoReturn("RelabelGroup: use RelabelGroup(G,labels,words), e.g. RelabelGroup(G,[\"c\",\"a\",\"b\"],[\"sr\",\"s\",\"sr^2\"]), or RelabelGroup(G,\"gap\")");
	fi;
	labels:=arg[2];
	words:=arg[3];
	if not IsList(labels) or not IsList(words) or Length(labels)<>Length(words) then
		ErrorNoReturn("RelabelGroup: give as many labels as words, e.g. RelabelGroup(G,[\"c\",\"a\",\"b\"],[\"sr\",\"s\",\"sr^2\"])");
	fi;
	if not ForAll(labels,l->IsString(l) and l<>"" and IsAlphaChar(l[1]) and ForAll(l,c->IsAlphaChar(c) or IsDigitChar(c))) then
		ErrorNoReturn("RelabelGroup: a label must be letters and digits starting with a letter, not ",labels);
	fi;
	if Length(Set(labels))<>Length(labels) then
		ErrorNoReturn("RelabelGroup: the labels ",labels," are not distinct");
	fi;
	#products are written without *, so no label may be another label followed by more letters ("a", "ab")
	if ForAny(labels,l1->ForAny(labels,l2->Length(l2)>Length(l1) and l2{[1..Length(l1)]}=l1 and IsAlphaChar(l2[Length(l1)+1]))) then
		ErrorNoReturn("RelabelGroup: the labels ",labels," are ambiguous in products such as ab (no label may be another label followed by letters)");
	fi;
	gens:=List(words,function(w) if IsString(w) then return GroupElement(G,w); else return w; fi; end);
	if not ForAll(gens,g->g in G) then
		ErrorNoReturn("RelabelGroup: not every generator is an element of G");
	fi;
	if Length(Set(gens))<>Length(gens) or One(G) in gens then
		ErrorNoReturn("RelabelGroup: the generators must be distinct and not 1");
	fi;
	if Group(gens)<>G then
		ErrorNoReturn("RelabelGroup: the generators ",words," do not generate G");
	fi;
	return AttachGroupLabels(G,gens,ShallowCopy(labels));
end;

#DisplayGroupLabels: a group by generators and relations
#in: (inp[,pcgs]) with inp a group G, or [G,[elements,labels]] (labels strings, optionally [elements,labels,gens] as returned by MakeGroupLabels), and pcgs a pcgs of G (default Pcgs(G))
#out: a string printing G by generators and relations; for a pc-group the relations are those of pcgs written in the labels (a power relation whose two sides are the same label is not printed); for a permutation or fp-group the labels are not used
DisplayGroupLabels:=function(arg)
	local inp,G,Gstr,El,lab,gl,isAtom,parts,pcgs,n,F,gens,rels,i,pis,exp,t,h,commPower,j,trivialCommutators;
	inp:=arg[1];
	if not IsGroup(inp) and
	   (not IsList(inp) or Length(inp)<>2 or not IsGroup(inp[1]) or
	    not IsList(inp[2]) or Length(inp[2])<2 or
	    Length(inp[2][1])<>Length(inp[2][2]) or
	    not IsEqualSet(inp[2][1],Elements(inp[1]))) then
		ErrorNoReturn("DisplayGroupLabels: invalid group-label data");
	fi;
	if IsGroup(inp) then 
		G:=inp;
	else
		G:=inp[1];
		El:=inp[2][1];
		lab:=inp[2][2];
		if not IsString(lab[1]) then lab:=List(lab,x->String(x)); lab[1]:="1"; fi;
	fi;
	#the SmallGroup id, when GAP's library has one for this order
	if IdGroupsAvailable(Size(G)) then
		Gstr:=Concatenation("G_{",String(IdGroup(G)[1]),",",String(IdGroup(G)[2]),"}");
	else
		Gstr:=Concatenation("G (order ",String(Size(G)),")");
	fi;
	#fragments are collected here and joined once at the end, instead of copying the whole string with Concatenation at every step
	parts:=[Gstr," = ",StructureDescription(G)];
	if IsTrivial(G) then
		Add(parts,"\ntrivial group\n");
		return Concatenation(parts);
	elif IsPermGroup(G) and IsList(inp) and Length(inp[2])>2 then
		#labelled generators, with the permutations they stand for
		gens:=inp[2][3];
		Append(parts,[" = < ",JoinStringsWithSeparator(List(gens,g->lab[Position(El,g)]),", ")," >\npermutation group, "]);
		Append(parts,[JoinStringsWithSeparator(List(gens,g->Concatenation(lab[Position(El,g)]," = ",String(g))),", "),"\n"]);
		return Concatenation(parts);
	elif IsPermGroup(G) then
		gens:=SmallGeneratingSet(G);
		n:=Length(gens);
		Add(parts," = < ");
		for i in [1..(n-1)] do Append(parts,[String(gens[i]),", "]); od;
		Append(parts,[String(gens[n])," >\npermutation group\n"]);
		return Concatenation(parts);
	elif IsFpGroup(G) then
		#fp custom labels can be created using IsomorphismFpGroupByGenerators but all generators will have same symbol with number
		gens := FreeGeneratorsOfFpGroup( G );
		n:=Length(gens);
    		rels := RelatorsOfFpGroup( G );
		Add(parts," = < ");
		for i in [1..(n-1)] do Append(parts,[String(gens[i]),", "]); od;
		Append(parts,[String(gens[n])," >\nfp-group with relations:\n"]);
		for i in [1..(Length(rels))] do Append(parts,[String(rels[i]),"=1\n"]); od;
		return Concatenation(parts);
	else
	#Pc-groups
	if Length(arg)>1 then pcgs:=arg[2]; else pcgs:=Pcgs(G); fi;
	gl:=function(g)
		if IsBound(lab) then return lab[Position(El,g)];
		elif IsOne(g) then return "1";
		else return String(g);
		fi;
	end;
	#isAtom: true for the label of a single generator (one of the labelled generators, or a letter and digits such as f1), written without brackets in a power
	isAtom:=function(l)
		if IsList(inp) and Length(inp[2])>2 and l in List(inp[2][3],gl) then return true; fi;
		return l<>"" and IsAlphaChar(l[1]) and ForAll(l{[2..Length(l)]},IsDigitChar);
	end;
	if not pcgs=fail then
		n:=Length(pcgs);
		pis  := RelativeOrders( pcgs );
		if IsOne(n) then
			Append(parts,[" = < ",gl(pcgs[1])," >\npc-group with relation:\n"]);
		else
			Add(parts," = < ");
			if (IsList(inp) and Length(inp[2])>2 and Group(inp[2][3])=G) then
				gens:=inp[2][3]; 
				for i in [1..(Length(gens)-1)] do Append(parts,[gl(gens[i]),", "]); od;
				Append(parts,[gl(Last(gens))," >\npc-group with relations:\n"]);
			else
				for i in [1..(n-1)] do Append(parts,[gl(pcgs[i]),", "]); od;
				Append(parts,[gl(pcgs[n])," >\npc-group with relations:\n"]);
			fi;			
		fi;
		# compute the orders of the pc-generators
		for i in [1..n] do
			exp := ExponentsOfRelativePower( pcgs, i ){[i+1..n]};
			t:=One(G);
			for h in [i+1..n] do
				t := t * pcgs[h]^exp[h-i];
			od;
			#with custom labels the right-hand side can carry the same label as the left-hand side (D8 with r,s: r^2 = r^2)
			if isAtom(gl(pcgs[i])) then
				if Concatenation(gl(pcgs[i]),"^",String(pis[i]))<>gl(t) then
					Append(parts,[" ",gl(pcgs[i]), "^", String(pis[i]), " = ", gl(t), "\n"]);
				fi;
			else
				Append(parts,["(",gl(pcgs[i]), ")^", String(pis[i]), " = ", gl(t), "\n"]);
			fi;
		od;
		# compute the commutators / conjugation of all pairs of pc-generators
		trivialCommutators := false;
		for i in [1..n] do
			for j in [i+1..n] do
				if pcgs[j] * pcgs[i] = pcgs[i] * pcgs[j] then
					trivialCommutators := true;
					continue;
				fi;
				commPower := Comm( pcgs[j], pcgs[i] );
				exp := ExponentsOfPcElement( pcgs, commPower ){[i+1..n]};
				t:=One(G);
				for h in [i+1..n] do
					t := t * pcgs[h]^exp[h-i];
				od;
				Append(parts,["[", gl(pcgs[j]), ", ", gl(pcgs[i]) , "]"]);
				Append(parts,[" = ", gl(t), "\n"]);
			od;
		od;
		if IsAbelian(G) then
		  Add(parts,"all generators commute, the group is abelian\n");
		elif trivialCommutators then
		  Add(parts,"all other pairs of generators commute\n");
		fi;
		return Concatenation(parts);
		else
			ErrorNoReturn("different method needed in DisplayGroupLabels");
		fi;
	fi;
end;

#ShowGroup: prints a group with its labelled generators, its relations and the labels of all its elements
#in: G a group (labels from MakeGroup or RelabelGroup, otherwise GAP's)
#out: none; prints the generators (and what they stand for), the relations as DisplayGroupLabels does, for a solvable group in a pcgs made of the labelled generators and their powers when there is one (D8 with r,s: r, r^2, s; a solvable permutation group through an isomorphic pc-group), and every element with its label
ShowGroup:=function(G)
	local gl,glH,Hp,iso,gens,cands,extra,g,p,m,pcseq,search,steps,pcgs,l,line,lab;
	gl:=MakeGroupLabels([G]);
	#a solvable permutation group is shown through an isomorphic pc-group H, with the same labels
	Hp:=G;
	glH:=gl;
	if IsPermGroup(G) and IsSolvableGroup(G) and not IsTrivial(G) then
		iso:=IsomorphismPcGroup(G);
		Hp:=Image(iso);
		glH:=[List(gl[1],g->Image(iso,g)),gl[2],List(gl[3],g->Image(iso,g))];
	fi;
	gens:=glH[3];
	pcgs:=fail;
	if IsPcGroup(Hp) and not IsTrivial(Hp) then
		#candidates: each generator g followed by its powers g^p, g^(p*q), ... (p, q, ... the prime factors of its order)
		cands:=[];
		for g in gens do
			m:=g;
			for p in Factors(Order(g)) do
				if not m in cands and not IsOne(m) then Add(cands,m); fi;
				m:=m^p;
			od;
		od;
		#search: a pc sequence [s_1..s_n] of candidates, built from the end: every <s_i..s_n> is normal of prime index in <s_(i-1)..s_n>; the later candidates are tried last positions first, so that the order of the generators is kept; at most 20000 steps
		steps:=0;
		search:=function(seq,H)
			local c,K,res;
			if Size(H)=Size(Hp) then return seq; fi;
			for c in cands do
				steps:=steps+1;
				if steps>20000 then return fail; fi;
				if not c in seq then
					K:=ClosureGroup(H,c);
					if IsPrimeInt(Size(K)/Size(H)) and IsNormal(K,H) then
						res:=search(Concatenation([c],seq),K);
						if res<>fail then return res; fi;
					fi;
				fi;
			od;
			return fail;
		end;
		cands:=Reversed(cands);
		pcseq:=search([],TrivialSubgroup(Hp));
		if pcseq=fail then
			#not enough: then also the other elements, shortest labels first
			extra:=Filtered(glH[1],g->not g in cands and not IsOne(g));
			SortBy(extra,g->Length(glH[2][Position(glH[1],g)]));
			cands:=Concatenation(cands,extra);
			steps:=0;
			pcseq:=search([],TrivialSubgroup(Hp));
		fi;
		if pcseq<>fail then pcgs:=PcgsByPcSequence(FamilyObj(One(Hp)),pcseq); fi;
	fi;
	if pcgs=fail and IsPermGroup(Hp) and HasGroupData(G) and IsBound(GroupData(G).meaning) then
		#the permutations of the labels are printed below, as MakeGroup gave them
		l:=DisplayGroupLabels([Hp,glH]);
		Print(l{[1..PositionSublist(l,"permutation group")+16]},"\n");
	elif pcgs=fail then
		Print(DisplayGroupLabels([Hp,glH]));
	else
		Print(DisplayGroupLabels([Hp,glH],pcgs));
	fi;
	if HasGroupData(G) and IsBound(GroupData(G).meaning) then
		for l in GroupData(G).meaning do Print("where ",l,"\n"); od;
	fi;
	#the elements, with line breaks before GAP's own at 80 characters
	Print("elements (",String(Size(G)),"):\n");
	line:=" ";
	for lab in gl[2] do
		if Length(line)+Length(lab)+2>76 then
			Print(line,"\n");
			line:=" ";
		fi;
		Append(line,Concatenation(" ",lab,","));
	od;
	Print(line{[1..Length(line)-1]},"\n");
end;

#Posinlist: finds the first sublist containing an element
#in: list a list of lists, el any object
#out: the index of the first sublist containing el, or fail
Posinlist:=function(list,el)
	local k;
	for k in [1..Length(list)] do
		if el in list[k] then
			return k;
		fi;
	od;
	return fail;
end;

#Possinlist: finds every sublist containing an element
#in: list a list of lists, el any object
#out: the list of indices of all sublists containing el, or []
Possinlist:=function(list,el)
	local k,toret;
	toret:=[];
	for k in [1..Length(list)] do
		if el in list[k] then
			Add(toret,k);
		fi;
	od;
	return toret;
end;

#IsNonNegIntv: tests whether a list consists of non-negative integers
#in: v a list
#out: true if every entry is an integer >= 0, false otherwise
IsNonNegIntv:=function(v)
	local n;
	for n in v do
		if not IsInt(n) then return false; 
		elif n<0 then return false; fi;
	od;
	return true;
end;

#PosNonZero: positions of the nonzero entries of a vector
#in: v a list of numbers
#out: the ascending list of positions of the nonzero entries
PosNonZero:=function(v)
	return Filtered([1..Length(v)],i->v[i]<>0);
end;

#Reshape: turns a flat list into a matrix with rows of a given length
#in: list a flat list, l1 a positive integer dividing its length
#out: list rewritten as a matrix with rows of length l1
Reshape:=function(list,l1)
	local t,k,m;
	if not IsPosInt(l1) or Length(list) mod l1 <> 0 then 
		ErrorNoReturn("row length must be positive and divide the list length"); 
	fi;
	m:=[];
	k:=0;
	while k<Length(list)/l1 do
		Add(m,List([1..l1],n->list[k*l1+n]));
		k:=k+1;
	od;
	return m;
end;

#SolveModZ: solves A*x=b mod 1 exactly, by the Hermite normal form of the integer system [A | D*b]
#in: A an integer matrix (r rows), b a list of r rationals, D a positive integer with D*b integral (e.g. the common denominator of b)
#out: a rational vector x with every entry of A*x-b an integer, or fail if there is none
SolveModZ:=function(A,b,D)
	local n,Mv,Herm,Hermt,v,sol,x;
	#HermiteNormalFormIntegerMat of [A | n*b], right-hand column reduced mod n, then SolutionMat: U[A|B]=[H|B'] with U unimodular, so A*x=b mod 1 iff H*y=B' mod n for y=n*x (y rational). The zero rows of H give B'_i=0 mod n and the other rows are solved over Q.
	n:=D;
	#no unknowns: solvable iff b is already integral
	if ForAll(A,IsEmpty) then
		if ForAll(b,IsInt) then return []; else return fail; fi;
	fi;
	#HermiteNormalFormIntegerMat needs an integer matrix
	if not ForAll(b,q->IsInt(q*n)) then
		ErrorNoReturn("SolveModZ: D*b must be integral");
	fi;
	Mv:=List([1..Length(A)],i->Concatenation(A[i],[b[i]*n]));
	Herm:=HermiteNormalFormIntegerMat(Mv);
	Hermt:=ShallowCopy(TransposedMat(Herm));
	v:=Last(Hermt) mod n;
	Remove(Hermt);
	sol:=SolutionMat(Hermt,v);
	if sol=fail then
		return fail;
	fi;
	x:=sol/n;
	if not ForAll(A*x-b,IsInt) then
		ErrorNoReturn("SolveModZ: internal error");
	fi;
	return x;
end;

#id: identity matrix of a given size
#in: v a positive integer or a list
#out: the identity matrix of size v, respectively of size Length(v)
id:=function(v)
	if IsPosInt(v) then
		return IdentityMat(v);
	elif IsList(v) and Length(v)>0 then
		return IdentityMat(Length(v));
	fi;
	ErrorNoReturn("id: expected a positive integer or a nonempty list");
end;

#Kr: Kronecker product of two matrices
#in: M1,M2 matrices
#out: their Kronecker product M1 (x) M2
Kr:=function(M1,M2)
	return KroneckerProduct(M1,M2);
end;

#Krl: iterated Kronecker product of a list of matrices
#in: lin a nonempty list of matrices
#out: their iterated Kronecker product, lin[1] (x) lin[2] (x) ...
Krl:=function(lin)
	local l,M;
	l:=lin;
	if Length(l)=0 then
		ErrorNoReturn("tensor-product input must be nonempty");
	elif Length(l)=1 then
		return l[1];
	fi;
	if Length(l)=2 then
		return Kr(l[1],l[2]);
	else
		M:=Kr(l[1],l[2]);
		l:=Concatenation([M],List([3..Length(l)],k->l[k]));
		return Krl(l);		
	fi;
end;

#Dag: conjugate transpose of a matrix
#in: M a matrix
#out: its conjugate transpose M^dagger
Dag:=function(M)
	return ComplexConjugate(TransposedMat(M));
end;

#add1: increments a digit vector whose digits run from 0
#in: vec,nmax integer vectors of equal length, digits running from 0
#out: the next vector in odometer order, wrapping to all zeros after nmax
add1:=function(vec,nmax)
	local head,nmaxhead,res;
	if not Length(vec)=Length(nmax) then
		ErrorNoReturn("vec and nmax must be of same length");
	fi;
	if vec=nmax then return List([1..Length(vec)],x->0); fi;
	head:=ShallowCopy(vec); #copy of input vector
	nmaxhead:=ShallowCopy(nmax); 
	Remove(head); #now it is all but last digit
	Remove(nmaxhead);
	if Last(vec)<Last(nmax) then
		Add(head,Last(vec)+1);
		return head;
	fi;
	if Last(vec)=Last(nmax) then 
		res:=Concatenation(add1(head,nmaxhead),[0]);
		return res;
	else ErrorNoReturn("vec[n]>nmax[n]");
	fi;
end;
