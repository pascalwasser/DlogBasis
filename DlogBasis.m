(* ::Package:: *)

(* Mathematica Package *)

BeginPackage["DlogBasis`"];
(* Exported symbols added here with SymbolName::usage *)  

InitializeDlogbasis::usage = "InitializeDlogbasis[]\nInitializes the dlogbasis - package. External, Internal and Propagators have to be defined in advance.
	Parametrization can be defined in advance or be defined later using SetParametrization[...]. Defining Replacements is optional,\n
	Massless box example:
	External={p1, p2, p3};
	Internal={k};
	Propagators={k^2, (k+p1)^2, (k+p1+p2)^2, (k+p1+p2+p3)^2};
	Replacements={p1 p2->s/2, p2.p3->t/2, p1*p3->-(s+t)/2, p1^2->0, p2.p2->0, p3^2->0}};
	Parametrization={{a1,a2,a3,a4},{k^2==(a1 a2-a3 a4)s, (k+p1)^2==s((1+a1)a2-a3 a4), k.p2==s/2 a1, (k-p3)^2 == t(a1-a2-a3+a4)+s(a1+a1 a2+a4-a3 a4)}, s^2};
	InitializeDlogbasis[]";
	
Parametrize::usage = "Can only be applied after 
a parametrization was defined. Converts any Lorentz invariant 
expression of internal and external momenta into the defined parametrization.
Converts integrands defined as \"G[fam, inds_List]\". Here \"fam\"
is a label of the integral family that can be chosen by the user and
\"inds\" is the list of propagator indices, which have to be integer numbers.";

SetParametrization::usage="SetParametrization[variables, equations, jacobian] or SetParametrization=[{variables, equations, jacobian}];
	Example: SetParametrization[{a1,a2,a3,a4},{k^2==(a1 a2-a3 a4)s, (k+p1)^2==s((1+a1)a2-a3 a4), k.p2==s/2 a1, (k-p3)^2 == t(a1-a2-a3+a4)+s(a1+a1 a2+a4-a3 a4)}, s^2];";
ToSpinorHelicity::usage="ToSpinorHelicity[term] converts a term to spinor helicity variables. 
	SpinorHelicity[...] must be called before using this function";
SpinorHelicityParametrization::usage="can be invoked after calling \"Initialiaze[]\" and SpinorHelicity[...] and gives back the SpinorHelicityParametrization";
IntegrandAnsatz::usage="IntegrandAnsatz[G[_,{1,1,1,....,0,0}]] gives the list of all integrals, subintegrals and integrals with numerators in the integral family "<>
	"defined by G[_{1,1,1,...,0,0}] which serves as an ansatz to find all dlog integrals of this family. Using an additional parameter IntegrandAnsatz[G[_,{1,1,1,....,0,0}], n] "<>
	"defines an ansatz corresponding to a numerator up to power order \"n\".";
LeadingSingularities::usage="LeadingSingularities[func, vars, n]: Computes the leading singularites for a rational function \"func\" with integral variables \"vars\"."<>
	"LeadingSingularities[func, vars, n]: Computes the leading singularities of \"func\", which is parametrized with parameters e. g. n[1], n[2], ..., n[max] and gives back a list of two lists. The first list are the leading singularities"<> 
	"and the second list are the constraints on the parameters n[i] in order to avoid non-logarithmic singularities";
lam::usage="lam[p1,p2] is a complex momentum built from the spinor and the dual spinor of the massless vectors p1 and p2.";
IntegrandVariables::usage="Returns the list of integrand variables defined in the parametrization";
GenerateDlogbasis::usage="GenerateDlogbasis[gmax, lsings, n] gives a list of dlog-Integrals taking as arguments a list of integrals gmax={G[...],G[...],...} and "<>
 "lsings = {\"leading singularities\", \"parameter constrains\"}, where the parameters are n[1], n[2], ... ";
SHParam::usage;



GtoFunction::usage;
epsil;
ContractLams::usage;
Filter::usage;
GetPowers::usage;
SetPowers::usage;
GetInfo::usage;
GtoFunction::usage;

SpinorHelicityRules::usage="SpinorHelicityRules[] gives the spinor helicity rules defined with SpinorHelicity[...]";
SpinorHelicity::usage;
ExpandVectors::usage;

BaikovParametrization::usage;

NewParametrization::usage;
VectorSolution::usage;
SetOutputLevel::usage="Sets the amount of output printed out during the calculation";
DlogBasis::usage="DlogBasis[{G[...],G[...]}] takes a list of integrals in the G[_,{...}]-form and computes a dlog-base taking the G's as ansatz."<>
	"If the list {G[...],G[...]} is not a complete ansatz for this family, \"DlogBasis\" might not be able to convert to a dlogbasis";
Jac::usage;
GtermToFunction::usage="Converts a term that is a linear combination of G[...]-terms into the internal parametrization (e.g. Spinor-Helicity parametrization).";
GetParametrization::usage;
FactorCompletelyList::usage;
DlogBasisMixed::usage;
GetDlogListRaw::usage;
GetDlogListMixed::usage;
GetLinsOrd::usage;
GetLinsN::usage;
ExINT::usage;
GetCores::usage;
GetLinsTiz::usage;
SetApartTimeConstrain::usage;
UseMacaulayQ::usage;
SetPropagatorIndices::usage;
GetFunc::usage;
ExSQRT::usage;
FindSubTops::usage;
FindDoublePoles::usage;
ExSqrtList::usage;
FindTransformation::usage;
ChangeVars::usage;
PlugInRules::usage;
ListFactor::usage;
GetSimplifiedDlogList::usage;
Terms::usage;
InTerms::usage;
ExSqrt::usage;
ExSquareRoot::usage;
GetGFunc::usage;
SumToList::usage;
ProductToList::usage;
FactorCollect::usage;
ApartListSQRT::usage;
ApartList::usage;
MatrixInverse::usage;
GetDlogListInv::usage;
MyListApartNew::usage;
Wellshaped::usage;
FunctionToList::usage;
MyFLInsertFunc::usage;
ProductFactorLists::usage;
ListFactorWhole::usage;
ListToFunction::usage;
CleanFactorList::usage;
ListCancel::usage;
FindSimplestVariable::usage;
ConvertQuadratic::usage;
(*sqrt::usage;*)
MyFactor::usage;
GtermToNumerator::usage;
TransformGs::usage;
MyCancel::usage;
SetN::usage;
Test::usage;
GetN::usage;
SetTimeConstrains::usage="SetTimeConstrains[constrain1, constrain2] sets time constrains for intermediate computation steps. If the limit is reached, the result will "<>
	"probably be incomplet";
SetMacaulay::usage;
IterativeSolve::usage;
DlogViaCuts::usage;
GetSubcuts::usage;
GetSeeds::usage;
LsingCut::usage;
GetAllCuts::usage;
CombineRules::usage;
DlogBasisViaCuts::usage;
ComputeCut::usage;
GetCutSolutions::usage;
SetCutSolutions::usage;
GtoFunctionOld::usage;
SetGmax::usage;
SetDlogs::usage;
SetSeeds::usage;
DlogViaCuts2::usage;
GetSimplifiedDlogList2::usage;
SetSpinorHelicityRules::usage;
ChooseLinearInd::usage;
GetGram::usage;
GetDlogs::usage;
EpsilonCon::usage;
ExpandEpsilonCon::usage;
GramDet::usage;
BaikovCut::usage;
ReplaceKinematics::usage;
LinIndep::usage;
Leadsing::usage;
spprojection::usage;
MyCollect::usage;
CollectVN::usage;
GetSimplifiedDlogList3::usage;
FindSimpleCombination::usage;
SortDlogs::usage;
JoinLsings::usage;
SetCuts::usage;
GetSector::usage;
MaxPosition::usage;
CorrectOnCut::usage;
Sps::usage;
SpsToP::usage;
PowCount::usage;
UnsolvedTerm::usage;
ExSquareRootQuad::usage;
ExSquareRootQuad2::usage;
SimplifyNestedRoot::usage;


Begin["`Private`"] (* Begin Private Context *)
external={};
internal={};
replacements={};
propagators={}; 
parametrization={};
massless={};
initialized = False;
parametrized = False;
spinorhelicity=False;
spinorhelicityvars={};
spinorhelicityjac=1;
shrules={};
toparametrization={};
vars={};
lsingvars={};
pareqs={};
jac=1;
powers = {};
unsolved={};
remainunsolved={};
pri = 0;
UseMacaulay=False;
datapath=Global`Datapath;
MacaulayPath=Global`M2path;
random=RandomInteger[1000000];
MyListApartTimeConstrain = 1000000;
SQRTTimeConstrain = 1000000;
propagatorInds=Null;
allcuts={};
cuts={};
gmax={};
dlogs={};
seeds={};
sqrtlsing=False;

SetGmax[gm_]:=gmax=gm;
SetDlogs[dl_]:=dlogs=dl;
SetSeeds[sds_]:=seeds=sds;

GetDlogs[] := dlogs;

UseMacaulayQ[]:= UseMacaulay;
SetApartTimeConstrain[time_]:=MyListApartTimeConstrain = time;

SetMacaulay[mac_] := Module[{}, UseMacaulay = mac]

SetOutputLevel[prio_]:=pri=prio;

SetTimeConstrains[ap_, sq_] := Module[{},
	MyListApartTimeConstrain = ap;
	SQRTTimeConstrain = sq;	
]

InitializeDlogbasis::External="External not properly defined. \nInitialization failed.";
InitializeDlogbasis::Internal="Internal not properly defined. \nInitialization failed.";
InitializeDlogbasis::Propagators="Propagators not properly defined. \nInitialization failed.";
InitializeDlogbasis::Replacements="Replacements not properly defined. \nInitialization failed.";
InitializeDlogbasis[]:=Module[{},
	external={};
	internal={};
	replacements={};
	propagators={}; 
	parametrization={};
	massless={};
	initialized = False;
	parametrized = False;
	toparametrization={};
	vars={};
	pareqs={};
	jac=1;
	powers = {};
	If[!MatchQ[Global`External, {a___}],
		Message[InitializeDlogbasis::External];
		Return[];
		,
		external=Global`External;
	];
	If[!MatchQ[Global`Internal, {a__}],
		Message[InitializeDlogbasis::Internal];
		Return[];
		,
		internal=Global`Internal;
	];	
	If[!MatchQ[Global`Propagators, {a__}] || 
		!FreeQ[ExpandVectors[Global`Propagators,Join[internal,external]]
			/.Dot[_?(MemberQ[Join[internal,external],#]&),_?(MemberQ[Join[internal,external],#]&)]:>0, Alternatives@@(Join@@{internal,external})],
		Message[InitializeDlogbasis::Propagators];
		Return[];
		,
		propagators=Global`Propagators;
	];
	If[Head[Global`Replacements]===Symbol,
		replacements={},
		If[!MatchQ[Global`Replacements, {___Rule}] ||
			Or@@(!MatchQ[#,Dot[_,_]]&/@ExpandVectors[Global`Replacements[[All,1]],external]),
			Message[InitializeDlogbasis::Replacements];
			Return[];
			,
			replacements=ExpandVectors[Global`Replacements, Join[internal,external]];
		];
	];
	
	(*If[!MatchQ[Global`Parametrization, {{a__},{b__},c_}],
		Print["No parametrization specified."];
		,
		SetParametrization[Global`Parametrization];
		
	];*)
	
	massless = Cases[replacements, ((Dot[a_, a_] -> 0) | (Dot[a_, a_] -> 0))][[All,1,1]];
	(*If[MatchQ[Length[massless],2|3],
		SpinorHelicity[internal,C,massless];
		,
		If[Length[massless]>3,
			SpinorHelicity[internal,C,massless[[1;;3]]]
		];
	];*)
	initialized = True;
	If[pri>0,Print["Initialization successful."]];
		
];



ContractLams[expr_]/;initialized :=  Module[{ml, i, j},
	ExpandVectors[
		expr/.Table[lam[massless[[i]],b_]->lam[ml[i],b],{i,1,Length[massless]}]
			/.Table[lam[a_,massless[[i]]]->lam[a,ml[i]],{i,1,Length[massless]}]
			/.Table[AngleBracket[massless[[i]],b_]->AngleBracket[ml[i],b],{i,1,Length[massless]}]
			/.Table[AngleBracket[a_,massless[[i]]]->AngleBracket[a,ml[i]],{i,1,Length[massless]}]
			/.Table[massless[[i]]->lam[massless[[i]],massless[[i]]],{i,1,Length[massless]}]
			/.Table[ml[i]->massless[[i]],{i,1,Length[massless]}],
			Flatten[Join[Cases[expr, lam[_,_],Infinity],Table[lam[massless[[i]], massless[[j]]],{i,1,Length[massless]},{j,1,Length[massless]}]]]]
	/.{lam[a_, b_].lam[a_, d_] :> 0, lam[a_, b_].lam[c_, b_] :> 0(*, lam[a_].lam[a_,b_]:>0*)}
	/. {lam[a_, b_].lam[c_, d_] :>     AngleBracket[a, c]/AngleBracket[b, d]*b.d(*,
	lam[a_].lam[b_,c_]:=AngleBracket[a,b]til[c]*)}
     /.Dot[a_,b_]/;Order[a,b]<0:>b.a
     /. ExpandVectors[
   replacements, external] /. {AngleBracket[a_, b_] /; 
    Order[a, b] < 0 :> -AngleBracket[b, a]}
]

ToSpinorHelicity[term_]/;(spinorhelicity&&initialized):= ContractLams[term/.shrules];

SpinorHelicityRules[]/;spinorhelicity := shrules;

SetSpinorHelicityRules[rules_]:= shrules=rules;

SpinorHelicityParametrization[Internal_List, vars_, ps_List]/;(initialized) := Module[{},
	SpinorHelicity[Internal, vars, ps];
	SpinorHelicityParametrization[]
];

SpinorHelicityParametrization[]/;(spinorhelicity&&initialized) := 
	{spinorhelicityvars, #==ToSpinorHelicity[#]&/@propagators, spinorhelicityjac}/.replacements

SpinorHelicity[momenta_List, vars_, ps_List]/;initialized:=Module[{vs, i, j, pp},
	If[Head[vars]===List && Length[momenta] != Length[vars], Print["First and second argument must have same length"]; Return[]];
	If[Head[ps[[1]]]===List && Length[ps] != Length[vars], Print["First and last argument must have same size"]; Return[]];
	If[Head[vars]=!=List, vs = Table[vars[i,j],{i,1,Length[momenta]},{j,1,4}],
		vs = Table[If[Head[vars[[i]]]===List, vars[[i]], vars[[i]]/@Range[4]],{i,1,Length[momenta]}];
	];
	If[Head[ps[[1]]]===List, pp=ps, pp=ps&/@Range[Length[momenta]]];
	shrules = Table[momenta[[i]] -> If[Length[pp[[i]]] == 2, 
		vs[[i,1]]lam[pp[[i,1]],pp[[i,1]]]+vs[[i,2]]lam[pp[[i,2]],pp[[i,2]]]+vs[[i,3]]lam[pp[[i,1]],pp[[i,2]]]+vs[[i,4]]lam[pp[[i,2]],pp[[i,1]]],
		vs[[i,1]]lam[pp[[i,1]],pp[[i,1]]]+vs[[i,2]]lam[pp[[i,2]],pp[[i,2]]]
			+vs[[i,3]]lam[pp[[i,1]],pp[[i,2]]]AngleBracket[pp[[i,2]],pp[[i,3]]]/AngleBracket[pp[[i,1]],pp[[i,3]]]
			+vs[[i,4]]lam[pp[[i,2]],pp[[i,1]]]AngleBracket[pp[[i,1]],pp[[i,3]]]/AngleBracket[pp[[i,2]],pp[[i,3]]]
		]
		,{i,1,Length[momenta]}
	];
	spinorhelicityjac = Times@@Table[If[MemberQ[internal,momenta[[i]]],(2pp[[i,1]].pp[[i,2]]/.replacements)^2,1],{i,Length[pp]}];
	spinorhelicityvars= Join@@vs[[Flatten[Position[momenta,a_/;MemberQ[internal,a],{1}]]]];
	spinorhelicity = True;
	shrules			
]

Sps[]/;initialized:=Union@Cases[ExpandVectors[propagators,Join[internal,external]],Dot[a_,b_]/;(MemberQ[internal,a]||MemberQ[internal,b]),All]

SetParametrization[a_,b_,c_]:=SetParametrization[{a,b,c}];
SetParametrization[Parametrization_]:=Module[{scalarproducts},
	parametrization = Parametrization;
	vars = parametrization[[1]];
	pareqs = parametrization[[2]];
	jac = parametrization[[3]];

	scalarproducts = Cases[Variables[ExpandVectors[propagators, Join[internal, external]]], 
		(Dot[a_,b_]/;MemberQ[internal,a]) | (Dot[c_,d_]/;MemberQ[internal,d])];
	toparametrization = Solve[ExpandVectors[pareqs, Join[internal, external]], scalarproducts];
	(*Print[toparametrization];*)
	If[Length[toparametrization] != 1, Print["Parametrization not valid"], 
		toparametrization = Dispatch[Factor[toparametrization[[1]]/.replacements]]];
	parametrized = True;
]

SHParam[vars_]/;initialized:=SHParam[internal,external,replacements,vars]

SHParam[internal_, external_, replacements_, vars_] :=
    Module[ {sps, ma, mv, massless, ms, re, ss, param1, param2, param3, a,
       b, c, paramtot, sol, extra, param, R, paramr, q, q1, q2, ksps, 
      jac,reps},
        reps=ExpandVectors[replacements,Join[internal,external]];
        massless = Cases[external, u_ /; (u.u /. reps) == 0];
        ms = Join[internal, external];
        sps = Join @@ 
          Table[ms[[i]].ms[[j]], {i, Length[ms]}, {j, i, Length[ms]}];
        If[ Length[massless] >= 2,
            ma = massless[[1 ;; 2]];
            re = DeleteCases[ms, Alternatives @@ ma];
            ss = 2 massless[[1]].massless[[2]] /. reps;
            param1 = Join @@ Table[r1.r2 ->
                Factor[(1/
                     2 ss (a[2] b[1] + a[1] b[2] - a[4] b[3] - 
                      a[3] b[4]) /. {a[h_] :> c[r1, h], 
                    b[h_] :> c[r2, h]})], {r1, re}, {r2, re}];
            param2 = 
             Join @@ Table[r.ma[[i]] -> 1/2 c[r, 3 - i] ss, {r, re}, {i, 2}];
            param3 = 
             Join @@ Table[
               m.n -> (ExpandVectors[m.n, ms] /. reps), {m, ma}, {n, 
                ma}];
            paramtot = 
             DeleteDuplicates[
              ExpandVectors[Join[param1, param2, param3], ms]];
            sol = Quiet@
               Solve[(reps[[All, 1]] /. 
                    paramtot) == (reps[[All, 2]]), 
                 Join @@ Table[c[p, i], {p, external}, {i, 4}]][[1]] //  Factor;
            extra = 
             Intersection[Join @@ Table[c[p, i], {p, external}, {i, 4}], 
              Variables[sol[[All, 2]]]];
            param = 
             Factor[paramtot /. sol/.MapThread[Rule,{extra,C/@Range[Length[extra]]/
              ss}]];
            jac = (2 ma[[1]].ma[[2]] /. reps);
        ];
        If[ Length[massless] == 1,
            ma = massless[[1]];
            If[ Length[external] == 1,
                Print["Paramtrization failed. Not enough external momenta"]
            ];
            mv = FirstCase[external, u_ /; (u.u /. reps) =!= 0];
            paramr = 
             SHParam[internal, external /. mv -> q, 
              MapThread[
               Rule, {reps[[All, 1]] /. mv -> q, 
                Factor[ExpandVectors[(reps[[All, 1]] /. 
                      mv -> mv - mv.mv/ExpandVectors[2 mv.ma, {mv, ma}] ma /. 
                     reps), Join[internal, external, {q}]] /. 
                  reps]}], vars];
            paramr = 
             MapThread[Rule, {paramr[[2, All, 1]], paramr[[2, All, 2]]}];
            param = 
             MapThread[
              Rule, {sps, 
               ExpandVectors[
                  sps /. mv -> mv.mv/ExpandVectors[2 mv.ma, {mv, ma}] ma + q, 
                  Join[internal, external, {q}]] /. paramr /. reps}];
            jac = (2 ma.q /. paramr);
        ];
        If[ Length[massless] == 0,
            If[ Length[external] == 0,
                Print["Parametrization failed. Not enough external momenta"]
            ];
            mv = FirstCase[external, u_ /; (u.u /. reps) =!= 0];
            paramr = 
             SHParam[internal, external /. mv -> Sequence[q1, q2], 
              ExpandVectors[
                DeleteCases[
                 Join[reps /. Rule -> R, {R[q1.q1, 0], R[q2.q2, 0], 
                   R[q1.q2, (mv.mv /. reps)/2]}
                  , 
                  Join @@ Table[{R[q1.p, q1.p], 
                     R[q2.p, (ExpandVectors[mv.p, {mv, p}] /. reps) - 
                       q1.p]}, {p, DeleteCases[external, mv]}]], 
                 R[Dot[mv, _], _] | R[Dot[_, mv]]], 
                Join[external, {q1, q2}]] /. R -> Rule, vars];
            paramr = 
             MapThread[Rule, {paramr[[2, All, 1]], paramr[[2, All, 2]]}];
            param = 
             MapThread[
              Rule, {sps, 
               ExpandVectors[sps /. mv -> q1 + q2, 
                  Join[internal, external, {q1, q2}]] /. paramr /. 
                reps}];
            jac = mv.mv /. reps;
        ];
        param = 
         param /. 
          Join @@ Table[
            c[internal[[i]], j] -> vars[[i]][j], {i, Length[internal]}, {j, 
             4}];
        ksps = Cases[sps, 
          Dot[u_, v_] /; MemberQ[internal, u] || MemberQ[internal, v]];
        {Join @@ Table[vars[[i]][j], {i, Length[internal]}, {j, 4}], 
         MapThread[Equal, {ksps, ksps /. param}], jac^(2 Length[internal])}
    ]

GetParametrization[]:=toparametrization;

Parametrize[expr_]/;(initialized&&parametrized) := Module[{exp, i, j},
	exp=expr/.epsil[a__]/;Length[{a}]==4:>PowerExpand[Sqrt[-MyFactor[Det[Table[Factor[Parametrize[{a}[[i]].{a}[[j]]]],{i,4},{j,4}]]]]];
	exp=ExpandVectors[exp, Join[internal, external]];
	exp=exp/.toparametrization;
	exp=exp/.Dispatch[replacements];
	exp/.Global`G[_,inds_List]/;Length[inds]==Length[propagators]:>GtoFunction[Global`G[1,inds]]
]

Parametrize[expr_List,n_]/;(initialized&&parametrized) := 
	If[FreeQ[expr,Alternatives@@Join[internal,external]],GtoFunction[expr,n],(Parametrize/@expr).Array[n,Length[expr]]]

IntegrandVariables[] := vars;

Jac[]/;(initialized&&parametrized):= jac;

ExpandVectors[term_, vectors_] := Module[{tt, vvv, V, i},
  tt = term /. 
    Dispatch[Table[vectors[[i]] -> V[vectors[[i]]], {i, 1, Length[vectors]}]];
  tt = tt /. {Dot[a_,b_]:>Dot[Expand[a],Expand[b]],q_^pow_/;Mod[pow,2]==0&&(Exponent[q/.V[qqq_]:>V[qqq]*vvv,vvv]==1):>Expand[q]^pow};
  tt=tt/. Dispatch[V[a_]*V[b_] :> V[a].V[b]];
  tt=tt /. Dispatch[{a_^n_Integer /; (((Exponent[a /. V[qqq_] :> V[qqq]*vvv, vvv] == 1) &&
               (Mod[n, 2] == 0))):> (Expand[a].Expand[a])^(n/2)}];

  tt=tt //. 
        Dispatch[Dot[a_ + b_, c_] :> a.c + b.c];

  tt=tt //. 
       Dispatch[Dot[a_, b_ + c_] :> a.b + a.c];

  tt=tt/.Dispatch[ {(q_*a_V).b_ :>  q*a.b}] /. Dispatch[{Dot[a_, q_*b_V] :> q*a.b}] /. Dispatch[{Dot[a_V, b_V] /; 
       Order[a, b] == -1 :> b.a}] /.Dispatch[ V[a_] :> a]
];







GtoFunction[term_]:=Module[{},
	GtoFunction[{term},n]/.n[1]->1	
]

GtoFunction[g_List, nn_]/;initialized :=Module[{maxa, i, j, func, glist},
	n=nn;
	If[Length[g]==0, Return[0]];
	glist=Union[Cases[g,Global`G[__],Infinity]];
	maxa= Table[Max[Table[glist[[i,2,j]],{i,1,Length[g]}]],{j,1,Length[propagators]}];
	(*Print[maxa];*)
	(*func = Sum[n[i]*Times@@(Factor[Parametrize[propagators]]^(-g[[i,2]]+maxa)),{i,1,Length[g]}]*	
		(Times@@(Factor[Parametrize[propagators]]^(-maxa))*jac);*)
	
	func = Collect[((n/@Range[Length[g]]).(g/.Global`G[_,ind_]:>Times@@(Factor[Parametrize[propagators]]^(-ind+maxa)))),n[_],Factor]
		*(Times@@(Factor[Parametrize[propagators]]^(-maxa))*jac);
	(*fl = FunctionToList[func, n, Length[g]];
	ListToFunction[fl, n]*)
	FactorCollect[func]
]	



(*IntegrandAnsatz[G_[_, pinds_]] := IntegrandAnsatz[G[1, pinds], 15];*)
IntegrandAnsatz[G_[fam_, pinds_], dim_:4] :=
    Module[ {sps, proppow, pow, pp, oans, nans, count, kk,  
      spspow, allpws, propexp, spsexp, intexp, intpow, res, rawG, const, 
      ig, Gs, toUnit, SP, P, SPtoP, i, pr, j, powinds, digs,ret, max},
      
    max=15; (*Maximum recursions*)
	sps = Union@Cases[ExpandVectors[propagators,Join[internal,external]],Dot[a_,b_]/;(MemberQ[internal,a]||MemberQ[internal,b]),All];
    ret=Null;
    propexp = 
	Table[Exponent[
             ExpandVectors[#, 
               Join[internal, 
                external]] /. ({internal[[i]].a_ :> 
                 kk[i] internal[[i]].a, (a_).internal[[i]] :> 
                 kk[i] a.internal[[i]]}), kk[i]], {i, Length[internal]}] & /@ propagators;

	intexp = Sum[propexp[[i]] pinds[[i]], {i, Length[propagators]}];
	spsexp = 
	Table[Exponent[
             ExpandVectors[#, 
               Join[internal, 
                external]] /. ({internal[[i]].a_ :> 
                 kk[i] internal[[i]].a, (a_).internal[[i]] :> 
                 kk[i] a.internal[[i]]}), kk[i]], {i, Length[internal]}] & /@ sps;

	proppow = 
	Table[pow @@ (Union[
             Cases[pr, Alternatives @@ internal, Infinity]]), {pr, 
           propagators}];


	spspow = 
	Table[pow @@ (Union[
             Cases[pr, Alternatives @@ internal, Infinity]]), {pr, sps}];
	allpws = Union[Cases[spspow, pow[__], Infinity]];
	digs = IntegerDigits[#, 2, Length[internal]] & /@ Range[2^Length[internal] - 1];
	allpws=(pow@@DeleteCases[internal^#,1])&/@digs;


	intpow = (Times @@ (#^(dim-2) & /@ (pow /@ internal)))/(Times @@ (proppow^pinds));
	intpow=1/(Times @@ (proppow^pinds));
	oans = {};
	nans = {1};
	count = 0;
	(*The power counting criterium is implented through the list powinds. It is a list of
	integers (or half integers) specifying the minimal number of propagators depending on either of the momenta
	that are specified in allpws*)
	(*One-loop criterium only*)
	powinds=allpws/.pow[a__]:>(dim-1);
	(*Multi-loop criterium*)
	powinds=allpws/.pow[a__]:>dim/2 (Length[pow[a]]+1)-1;
	SP=Global`SP;
	While[Length[oans] != Length[nans],

        
		If[ count++;
             count > max,
             If[max==15,Print["Maximal number of recursions reached in IntegrandAnsatz"]];
             ret=Global`Failed[];
             Break[];

		];

		oans = nans;
		nans = 
		Prepend[Join @@ Table[oans[[i]] SP[j], {i, Length[oans]}, {j, Length[sps]}],   1];
        nans = DeleteDuplicates[
        	DeleteCases[nans,
            (*q_ /; Max[PowCount[intpow q /. SP[in_] :> spspow[[in]], pow]] >=  0]];*)
            q_ /; Max[PowCount[intpow q /. SP[in_] :> spspow[[in]], pow]+powinds] >  0]
        ];
	];
	If[ret===Global`Failed[],Return[ret]];
	If[pri>2,Print[nans/.SP[r_]:>sps[[r]]]];
	If[Length[nans]==0, Return[{}]];

	SPtoP = 
	Solve[ExpandVectors[#, Join[internal, external]] & /@ 
               propagators == P /@ Range[Length[propagators]], 
             sps][[1]] /. (sps[[#]] -> SP[#] & /@ Range[Length[propagators]]) /. replacements;
	ig = G[fam, pinds];
	pp = nans /. SPtoP;
	res = Expand[pp] //. {P[a_]^n_ :> P @@ (a & /@ Range[n]), 
            P[a__] P[b__] :> P[a, b]} /. P[q__] :> Head[ig][fam, ig[[2]] 
            	- Sum[UnitVector[Length[ig[[2]]], P[q][[i]]], {i, 1, Length[P[q]]}]];

	const = res /. Head[ig][__] :> 0;
	rawG = res - const + const*Head[ig][fam, ig[[2]]];
	Gs = Union[Cases[rawG, G[__], Infinity]];    
	toUnit = Table[Gs[[i]] -> UnitVector[Length[Gs], i], {i, Length[Gs]}];
	graw=RowReduce[rawG /. toUnit].Gs;
	GetSimplifiedDlogList3[graw]
]

PowCount[ex_, pow_] :=  Module[ {digs},
	digs = IntegerDigits[#, 2, Length[internal]] & /@ Range[2^Length[internal] - 1];
	Exponent[#, q] & /@ (((ex /. pow[a__] /; !FreeQ[{a}, Alternatives @@ internal[[Flatten[Position[#, 1]]]]] :>  q) & /@ digs) /. pow[__] :> 1)
]


GetDlogListRaw[Gs_, Ls_, n_] := Module[{i,tab, status, sol},
	status=True;
	tab=Table[Print[i," of ",Length[Ls[[1]]]];sol=Quiet@Solve[Ls[[1]] == UnitVector[Length[Ls[[1]]], i], 
      Cases[Variables[Ls[[1]]], n[_]]]; If[Length[sol]!=1, status=False; Nothing,  sol[[1]]], {i, 1, Length[Ls[[1]]]}];
     
  
    If[status===False,     
        Print["No solution found for inverting the system. Possible reasons: Leading singularities are not linear independent"
        <>" or integrand ansatz is not complete"];
        Return[Global`Failed[]]
    ];  
	(n /@ Range[Length[Gs]].Gs) /. Ls[[2]] /. tab
]

GetDlogListInv[Gs_, Ls_, n_] := Module[{i, j, cmat, reps, inv, ns},
	ns = Union[Cases[Ls[[1]], n[_], Infinity]];
	(*Print[ns];*)
	cmat = Table[Coefficient[Ls[[1, i]], ns[[j]]], {i, Length[Ls[[1]]]}, {j, Length[Ls[[1]]]}];
	inv = MatrixInverse[cmat];
	reps = Table[ns[[i]] -> inv[[i, j]], {j, Length[ns]}, {i, Length[inv]}];
	Gs.n /@ Range[Length[Gs]] /. Ls[[2]] /. reps
]

GenerateDlogbasis::args="First arguments must be a list (integrand ansatz). Second argument must be a list with two entries."<>
	"The first entry is the list of linear independent leading singularities, the second entry is the list of parameter constraints."<>
	"The third argument 'n' labels the free parameter of the ansatz: {n[1], ..., n[m]}";
GenerateDlogbasis[__]:=Message[GenerateDlogbasis::args];
GenerateDlogbasis[Gs_List, Ls_List, n_]:=Module[{sol},
	If[Length[Ls]!=2||!MatchQ[(Union[Head/@Ls[[2]]]), {Rule}|{}]
		,
		Message[GenerateDlogbasis::args];Return[Null]
	];
	If[Length[Gs] != Total[Length/@Ls]
		, 
		Print["Solution contains free parameters."];
		sol=GetDlogListRaw[Gs, Ls, n];
		,	
		If[Length[Ls[[1]]]==0, Return[{}]];
		sol = GetDlogListInv[Gs, Ls, n];
	];
	If[sol===Global`Failed[] || FreeQ[sol,_Global`G], sol, GetSimplifiedDlogList3[sol]]
]

GetDlogListMixed[Gs_, Ls_, n_]:=Module[{gdlog, nn},
	gdlog = Gs.n /@ Range[Length[Gs]] /. Ls[[2]];
	DeleteDuplicates[DeleteCases[Table[Coefficient[gdlog, nn], {nn,  Sort[DeleteDuplicates[Cases[gdlog, n[_], Infinity]]]}],0]]
		
]


LeadingSingularities[func_,vars_]:=Module[{lsing},
	lsing=LeadingSingularities[func npar[1],vars,npar];
	If[lsing===Null,Return[Null]];
	If[Head[lsing]===UnsolvedTerm,Return[lsing]];
	If[Length[lsing[[2]]]==1,Fail["DoublePole"],lsing[[1]]/.npar[1]->1]
]

LeadingSingularities::vars="Second argument must be list.";
LeadingSingularities::func="First argument must be linear in all parameter variables";
LeadingSingularities[func_,vars_,nn_]:=Module[{len, ns},
	n=nn;
	If[Head[vars]=!=List,
		Message[LeadingSingularities::vars];
		Return[Null]		
	];
	ns=Cases[Variables[func],_nn];
	If[Union[Exponent[func,#]&/@ns]!={1},
		Message[LeadingSingularities::func];
		Return[Null]
	];	
	len=(Cases[func,_nn,All]//Union)[[-1,1]];
	Catch[LeadingSingularities[func,vars,nn,len],UnsolvedTerm]
]
    
LeadingSingularities[func_,vars_,nn_,len_]:=Module[{flist},
	lsingvars=vars;
	If[!FreeQ[func,Power[_,-1/2]],
		lsingsqrt=True;
		ExSQRT[func,vars,nn]/.sqrt->Sqrt
		,
		lsingsqrt=False;
		n=nn;
		flist=FunctionToList[func,n,len];
		ExALL[flist,vars,{},n/@Range[len]]/.sqrt->Sqrt
	]
]

FunctionToList[func_,nn_,len_]:=Module[{coflist,flist},
	n=nn;
	coflist=MyFactorList[Coefficient[Numerator[func],#]]&/@(n/@Range[len]);
	flist={{{{1,1}},MyFactorList[Denominator[func]]},coflist};
	flist=CleanMinusListPlusFactorOut[flist];
	If[!PossibleZeroQ[ListToFunction[flist,n]-func],Throw[FunctionToListError[]]];
	flist
];




ExALL[func_,vari_,pr_,ns_]:=Module[{exl,i,nn,sols,ex,x,nexl,rules,rules2, res, exInt, unsolvedReplaced, joinedSols},
	unsolved={};
	remainunsolved={};
	nn=ns;
	exl={{{func},vari,pr}};
	sols={};
	For[i=1,i<=Length[vari],i++,
		(*If[i>=Length[vari]-1, Print["EXXLLL"];Print[exl]];*)
		If[pri>-1,PrintTemporary["Variable ",i," of ",Length[vari]]];
		exl=SortBy[exl,Length[#[[1]]]&];
		If[pri>1,Print["exl",Length[#[[1]]]&/@exl]];
		If[Length[exl]==0, (*Print["No solution"];*) Break[];  (*Return[{{},(#->0)&/@ns}]*)];
		nexl=Catch[ExLlist[exl]];
		If[pri>3,Print["Finished ExLlist"]];
		If[Head[nexl]===NonLog1 || Head[nexl]===NonLog2 || Head[nexl]===NonLog3 || Head[nexl]===NoTrafo,
			If[pri>-1,PrintTemporary["Double pole"]];
			ex=nexl[[1]];
			x=nexl[[2]];
			If[Head[nexl]===NonLog1,
				If[pri>1,Print["nonlog1"]];
				(*Print[ex];*)
				(*rules2=Catch1[ex,x,vari,ns];*)
				
				rules=Catch1New[ex,x,vari,ns];
			];
			If[Head[nexl]===NonLog2,
				If[pri>1,Print["nonlog2"]];
				(*Print[ex];*)
				rules=Catch2[ex,x,vari,ns];
				(*Print["soo"];*)
				(*rules2="nix";*)
			];
			If[Head[nexl]===NonLog3,
				If[pri>1,Print["nonlog3"]];
				(*Print[ex];*)
				(*rules=Catch3[ex,x,vari,ns][[1]];*)
				rules=Catch3New[ex,x,vari,ns];
			];
			If[Head[nexl]===NoTrafo,
				If[pri>1,Print["NoTrafo"]];
				rules=CatchNoTrafo[nexl[[1]], vari];
			];
			If[pri>1,Print[rules]];
			(*Print["rules2"];
			Print[rules2];*)
			sols=Append[sols,rules];
			If[Length[rules]==0,
				
				Throw[NoRules]];
			rules = (#[[1]] -> FactorCollect[#[[2]]]) & /@ rules;
			If[pri>2,Print["New Rules: "]; Print[rules]];
			If[pri>3,Print["Plugin Rules"]];
			exl=PlugInRules[exl,rules];
			If[pri>3,Print["After plug in rules"]];
			(*Print[CheckEnergyDimension[exl]];
			Print[exl];*)
			If[pri>3,Print["ListFactorWhole: Length exl: ",Length[exl]]];
			exl={ListFactorWhole/@#[[1]],#[[2]],#[[3]]}&/@exl;
			
			
			If[pri>3,Print["After list-factor"]];
			(*Print[CheckEnergyDimension[exl]];
			Print[exl];*)
			
			If[pri>3,Print["DeleteCases"]];
			
			exl=DeleteCases[exl,{{{{0,1}},_},_},{3}];
			exl=DeleteCases[exl,{{},_,_},{1}];
			i--;
	(*Print[CheckEnergyDimension[exl]];
			Print[exl];*)
			,
			If[Head[nexl]=!=List,Throw[nexl]];
			exl=nexl;
			(*Print[CheckEnergyDimension[exl]];*)
			(*Print["exlllllllllllllllllllllllll"];
			Print[exl];*)
		];
	];
	res= MakeNicer[ResToFunc[{exl,sols},n]];
	If[pri>0,Print["raw Result"]];
	If[pri>0,Print[res]];
	(*Print[unsolved];
	Print[Cases[Variables[unsolved/.res[[2]]],n[_]]];
	Print[Intersection[vari,Variables[unsolved/.res[[2]]]]];
	Print[Numerator/@(unsolved/.res[[2]])];
	Abort[];*)
	(*Put[unsolved,"~/workspace/lsing/UnsolvedCases/unsolved.txt"];
	Abort[];*)
	While[Length[unsolved]>0,
		If[pri>-1,PrintTemporary["Solve square root term: ",Length[unsolved]," term"<>If[Length[unsolved]==1,"","s"]<>" left."]];
		(*Print[unsolved];*)
		(*Print[ExIINT[unsolved/.res[[2]],Intersection[vari,Variables[unsolved]],n]];*)	
		unsolvedReplaced = DeleteCases[unsolved/.res[[2]],{0,__}];
		If[Length[unsolvedReplaced]==0, Return[res]];
		exInt=TimeConstrained[ExSQRT[{unsolved[[-1,1]]/.res[[2]]},unsolved[[-1,2]],n],SQRTTimeConstrain,
			remainunsolved=Append[remainunsolved,{unsolved[[-1,1]]/.res[[2]]}];
			Print["SQRT time constrain exceeded  (",SQRTTimeConstrain," s). Solution will probably be incomplete."]; {{},{}}];
		unsolved=Delete[unsolved,-1];
		joinedSols=(#[[1]] -> (#[[2]] //.Join[res[[2]],exInt[[2]]])) & /@ Join[res[[2]],exInt[[2]]];
		res={Join[exInt[[1]]/.joinedSols,res[[1]]/.joinedSols][[GetLinsOrd[Join[exInt[[1]]/.joinedSols,res[[1]]/.joinedSols]  ][[1]]]],joinedSols};
		If[pri>2,Print["New solution"];Print[res];];	
	];
	res[[1]]=Join[res[[1]],Global`Unsolved&/@remainunsolved];
	res
];

ResToFunc[res_, n_] := 
	 {{{If[Length[res[[1]]]>0,ListToFunction[#, n] & /@ res[[1, 1, 1]], {}], {}, {}}}, res[[2]]};

MakeNicer[res_] := Module[{rules,i, r},
	r = If[Length[res[[2]]] > 0,
		rules = res[[2, -1]];
		Do[rules = Join[#[[1]]->(CleanExpr[#[[2]]/.rules])&/@res[[2,-i]], rules ], {i, 2, Length[res[[2]]]}];
   			{res[[1, 1, 1]], rules}
   		,
   		{res[[1, 1, 1]], {}}];
   	{CleanExpr/@r[[1]], SortBy[r[[2]],#[[1,1]]&]}
]


ExLlist[fl_]:=Module[{tab,i,j},
	(*fl={{{func,func,func},vari,pr},{{func,func},vari,pr},{{func},vari,pr}}*)
	If[pri>2,Print["Start ExLsList. Length fl: ", Length[fl]]];
	tab=Join@@Table[If[pri>1,Print["term ",i," of ",Length[fl]]];ExLsList[fl[[i]]],{i,1,Length[fl]}];
	If[pri>3,Print["Finished ExLsList"]];
	Do[
		For[j=1,j<=Length[tab[[i,3]]],j++,
			If[FreeQ[tab[[i,2]],tab[[i,3,j,1]]],
				tab[[i,3]]=Delete[tab[[i,3]],j];
				j--;
			]
		],
		{i,1,Length[tab]}
	];
	tab=Gather[tab, #1[[2 ;;]] == #2[[2 ;;]] &];
	tab=Prepend[#[[1, 2 ;;]], Join @@ #[[All, 1]]] & /@ tab;
	If[pri>3,Print["Before ExLlist Lins"]];
	Do[tab[[i,1]]=tab[[i,1,GetLinsOrd[ListToFunction[#,n]&/@tab[[i,1]]][[1]]]],{i,1,Length[tab]}];
	If[pri>2,Print["Finished 2nd part ExLlist"]];
	tab
]

FindSuitedListList[list_,vars_]:=Times@@(FindSuitedList[#,vars]&)/@list;

FindSuitedList[list_,vars_]:=Module[{den,ext,i,j},
	(*Print["Enter FindSuitedList"];
	Print[list];*)
	(*If[Head[list[[1,2,1,1]]]===List,Return[Times@@(FindSuitedList[#,vars]&)/@list]];*)
	den=list[[1,2,All,1]];
	ext=Table[Exponent[den[[j]],vars[[i]]],{i,1,Length[vars]},{j,1,Length[den]}];
	If[Max[#]<2,1,0]&/@ext
];


TransTwoSquaresSingleTerm[term_, v1_, v2_] := Module[{a, b, c},
	If[Head[term]===Missing,Return[NoTrafo]];
	{a, b, c} = Coefficient[term, #] & /@ {v1^2, v2^2, v1*v2};
	v1 -> v1 + (-c - Sqrt[-4 a b + c^2])/(2 a)*v2
];

TransTwoSquares[term_, v1_, v2_, sqrt_] := Module[{tr},
	tr = TransTwoSquaresSingleTerm[FirstCase[FactorList[term][[All, 1]], x_ /; (Exponent[x, v2] == 2&&Exponent[x, v1] == 2)], v1, v2];
	(term /. tr // Factor) /. Sqrt[x_] :> sqrt[x] // Factor
]

TransTwoSquaresRepl[term_, v1_, v2_, sqrt_] := Module[{tr},
	tr = TransTwoSquaresSingleTerm[FirstCase[FactorList[term][[All, 1]], x_ /; (Exponent[x, v2] == 2&&Exponent[x, v1] == 2)], v1, v2];
	tr/.Sqrt[x_]:>sqrt[x]
]



ExLsList[flst_]:=Module[{fls,fs,pos,g,pl,rest,gr,ret,zer,prob,at,egl,i,j,k,trans, st,uns},
	(*fls={{func,func,func},vari,pr}*)
	(*Print[fls];*)
	fls=flst;
	(*If[Length[flst[[2]]]==1,fls=FactorCompletelyFLST[flst], fls = flst];*)
	fs=FindSuitedListList[fls[[1]],fls[[2]]];
	ret={};
	If[pri>1,Print["fs",fs]];
	If[Plus@@fs!=0,
		pos=Position[fs,1][[1,1]];
		g=ExGlist[fls[[1]],fls[[2,pos]]];
		uns={#[[1]],fls[[2]]}&/@Cases[g,Unsolved[__]];
		If[Length[uns]>0,
			unsolved=Join[unsolved,uns];
			g=DeleteCases[g,Unsolved[__]];
			Print["Length of unsolved terms: ", Length[unsolved]];
		];
		Return[{{g,Delete[fls[[2]],pos],fls[[3]]}}];
		,
		fs=FindSuitedList[#,fls[[2]]]&/@fls[[1]];
		If[pri>1,Print["fs2",fs]];
		zer= Position[ fs,0*  Range[Length[fls[[2]]]]  ] ;
		If[pri>1,Print["zer2",zer]];
		prob=fls[[1,Flatten[zer]]];
		(*prob={func,func,func}*)
		(*Print[prob];*)
		Do[
			If[pri>3,Print["prob ",i," of ",Length[prob]]];
			at=Join@@AllTransformations[fls[[2]],fls[[3]]];
			If[pri>3,Print["at"]];
			If[pri>3,Print[at]];
			(*st = Join@@Table[{TransTwoSquaresRepl[ListToFunction[prob[[i]], n],fls[[2,j]],fls[[2,k]],Global`sqrt],1,{nothing}}
				,{j,1,Length[fls[[2]]]},{k,Delete[Range[Length[fls[[2]]]], j]}];
			st = DeleteCases[st,{NoTrafo,__}];
			If[pri>3,Print["st"]];
			If[pri>3,Print[st]];*)
			st={};
			at = Join[at, Cases[st, q_/;FreeQ[q,Global`sqrt|ComplexInfinity|Indeterminate]]];
			If[pri>3,Print["atalles"]];
			If[pri>3,Print[at]];
			If[pri>5,Print["prob",i]];			
			If[pri>5,Print[prob[[i]]]];
			trans=If[Length[at]>0, TransformProb[prob[[i]],fls[[2]],at], NoTrafo[prob[[i]]]];
			(*trans[[1]]=func,trans[[2]]=number of succesful transformation, trans[[3]]=index of next variable*)
			If[Head[trans]===NoTrafo,
				If[pri>0,Print["+++++++++++++++No trafo found++++++++++++++++++++++++++++"]];
				If[pri>0,Print[ListToFunction[prob[[i]],n]]];
				unsolved=Append[unsolved,{ListToFunction[prob[[i]],n],flst[[2]]}];
				If[pri>-1,PrintTemporary["Square root term: ",Length[unsolved]]	];
				(*Throw[NoTrafo[prob[[i]]]];*)
				,
				If[pri>1,Print["Trafo found"]];
				(*Print[trans];*)
				j=trans[[2]];
				If[pri>3,Print["Before ExGlist"]];
				egl=ExGlist[{trans[[1]]},fls[[2,trans[[3]]]]];
				uns={#[[1]],fls[[2]]}&/@Cases[egl,Unsolved[__]];
				Print["asdfsd"];
				If[Length[uns]>0,
					unsolved=Join[unsolved,uns];
					egl=DeleteCases[egl,Unsolved[__]];
					Print["Length of unsolved terms: ", Length[unsolved]];
				];		
				If[pri>3,Print["After ExGlist"]];
				ret=Append[ret,{egl,Delete[fls[[2]],trans[[3]]],fls[[3]]/.{at[[j,3,1]],_,_}:>at[[j,3]]}];
			];
			,{i,1,Length[prob]}
		];
		
		rest=Delete[fls[[1]],zer];
		While[Length[rest]>0,
			fs=FindSuitedList[#,fls[[2]]]&/@rest;
			pl=Plus@@fs;
			pos=Position[pl,Max[pl]][[1,1]];
			gr=Position[fs[[All,pos]],1];
			g=ExGlist[rest[[Flatten[gr]]],fls[[2,pos]]];
			uns={#[[1]],fls[[2]]}&/@Cases[g,Unsolved[__]];
			If[Length[uns]>0,
				unsolved=Join[unsolved,uns];
				g=DeleteCases[g,Unsolved[__]];
				Print["Length of unsolved terms: ", Length[unsolved]];
			];	
			rest=Delete[rest,gr];
			ret=Append[ret,{g,Delete[fls[[2]],pos],fls[[3]]}];
		];
		Return[ret];
	];
	
]

ExGlist[list_,x_]:=
Module[{qp,i,pp,gel,ltf,exgunsolved},
	
	exgunsolved={};
	qp=Table[If[pri>1,Print["---Term ",i," of ",Length[list]]];
		TimeConstrained[
			mml=MyListApartNew[list[[i]],x];
		 	(*Print[mml];*)
		 	mml
		 	,
			MyListApartTimeConstrain, 
			Print["Apart-time constrain limit reached (",MyListApartTimeConstrain," s). Added to unsolved terms."];
			exgunsolved=Append[exgunsolved,Unsolved[ListToFunction[list[[i]],n]]];
			Nothing
		],
		{i,1,Length[list]}
	];
	(*qp=Table[If[pri>1,Print["---Term ",i," of ",Length[list]]];MyListApartNew[list[[i]],x],{i,1,Length[list]}];*)
	If[pri>3,Print["---Apart finished"]];
	pp=Join@@qp[[All,All,1]];
	If[pri>0,Print["BeforeGetLinsN"]];
	ltf=ListToFunction[#,n]&/@pp;
	If[pri>3,Print["After ListToFunction. Length[pp]: ",Length[pp]]];
	gel=GetLinsOrd[ltf];
	If[pri>3,Print["AfterGetLinsN"]];
	Join[pp[[gel[[1]]]],exgunsolved]
];


TransformProb[prob_,vars_,at_]:=Module[{transden,fs,j,trans,pos,ind,error},
	(*prob=func,vars=vari,at={{{a[2]->a[2]^2+1,a[3]->a[4]},s+t,{a,1,3}},{...}}*)
	ind=0;
	error=False;
	Do[
		transden=1/Factor[Times@@Power@@@prob[[1,2]]/.at[[j,1]]];
		(*Print[transden];*)
		fs=FindSuited2[transden,vars];
		If[pri>4,Print[fs]];
		If[Plus@@fs!=0,	
			pos=Position[fs,1][[1,1]];
			trans=Map[{MyFactorList[#[[1]]], #[[2]]} &, ({{Append[prob[[1,1]],{at[[j,2]],1}],prob[[1,2]]},prob[[2]]})/. at[[j, 1]], {3}];
			trans=Map[CleanFactorList, trans, {2}];
			(*egl=ExGl[{trans},fls[[2,Position[fs,1][[1,1]]]]];
			Print[egl];
			ret=Append[ret,{egl,Delete[fls[[2]],Position[fs,1][[1,1]]],fls[[3]]/.{at[[j,3,1]],_,_}:>at[[j,3]]}];
			(*ret=Append[ret,ExGl[{trans},fls[[2,Position[fs,1][[1,1]]]]]];*)*)
			ind=j;
			Break[];
		];
		If[pri>4,Print[j," of ",Length[at]]];
		If[j==Length[at],
			Print["No transformation was found"];
			error=NoTrafo[prob];
		];
		,{j,1,Length[at]}
	];
	If[error=!=False,Return[error]];
	(*trans=func,ind=number of succesful transformation, pos=index of next variable*)
	{CleanMinusListPlusFactorOut[trans],ind,pos}
];

FindSuited2[f_,vars_]:=Module[{den,ext,i,j},
	If[Head[f]===List,Return[Times@@(FindSuited2[#,vars]&)/@f]];
	den=Denominator[f];
	den=FactorList[den][[All,1]];
	(*den=ProductToList[den];*)
	(*den=If[Head[den]===Times,den=List@@den,{den}];*)
	ext=Table[Exponent[den[[j]],vars[[i]]],{i,1,Length[vars]},{j,1,Length[den]}];
	If[Max[#]<2,1,0]&/@ext
];

GetLinsOrd[funcs_]:=Module[{ord, gl, iord, gl2, ord2, gl3, time},
	If[!FreeQ[funcs,sqrt],Return[GetLinsN[funcs/.sqrt->Sqrt]]];
	ord = Ordering[funcs, All, ByteCount[#1]<ByteCount[#2]&];
	iord = InversePermutation[ord];
	{time, gl} = AbsoluteTiming[GetLinsTiz[funcs[[ord]]]];
	If[pri > 2, Print["GetLinsTiz ", Length[funcs], "   ", time]];
	gl2 = {ord[[gl[[1]]]],gl[[2,iord]]};
	ord2 = Ordering[gl2[[1]]];
	gl3={gl2[[1,ord2]],#[[ord2]]&/@gl2[[2]]};
	(*If[!CheckLinsInt[funcs, Variables[funcs], gl3]
		,Print["Error in GetLinsOrd"]];*)
	gl3
	
]

(*Rearrange nested Factor-Lists and summarize same factors*)
CleanFactorList[list_] := Module[{lis,i},
  lis = list;
  lis = If[Head[#[[1]]] === List, 
      Table[{#[[1, i, 1]], #[[1, i, 2]]*#[[2]]}, {i, 1, 
        Length[#[[1]]]}], #] & /@ lis;
  lis = Join @@ (If[Head[#[[1]]] === List, #, {#}] & /@lis);
  lis = GatherBy[lis, NumericQ@First@# &];
  lis = 
    Join@@Table[If[
      NumericQ[lis[[i, 1, 1]]], {{Times @@ Power @@@ lis[[i]], 1}}, 
      lis[[i]]], {i, 1, Length[lis]}];
  lis = GatherBy[lis, First];
  lis={#[[1, 1]], Plus @@ #[[All, 2]]} & /@ lis;
  DeleteCases[lis,{_,0}]
]


  
NormalizeRule[rule_, n_] := Module[{},
  Solve[rule[[1]] == rule[[2]], 
    Union[Cases[rule, n[_], Infinity]][[-1]]][[1, 1]]
  ]





   
Trafo[ov_, nv_, a_] := 
  Module[{he, gl, i, j, l, k, tab, pref, tabs, reps, ind},
   he = If[Min[i, j] == 1, If[Max[i, j] == 2, 3, 2], 1];
   gl = a[1] v[i, i] + (
     a[3] AngleBracket[ j, he] v[i,j])/ AngleBracket[i, he]  + (
     a[4] AngleBracket[ i, he] v[j,i])/ AngleBracket[j, he] + 
     a[2] v[j, j];
   tab = Table[
     Expand[(2*ToSpinorHelicity[gl /. {i -> nv[[1]], j -> nv[[2]]}]*
         v @@ ind)] // 
      ToSpinorHelicity, {ind, {{l, l}, {k, k}, {l, k}, {k, l}} /. {k -> 
         ov[[1]], l -> ov[[2]]}}];
   pref = 
    Table[Expand[(2*
         ToSpinorHelicity[gl /. {i -> ov[[1]], j -> ov[[2]]}]*
         v @@ ind)] // 
      ToSpinorHelicity, {ind, {{l, l}, {k, k}, {l, k}, {k, l}} /. {k -> 
         ov[[1]], l -> ov[[2]]}}];
   pref = Table[D[pref[[i]], a[i]], {i, 1, 4}];
   tabs = 
    Expand[tab/pref] /. 
     AngleBracket[p_, q_] /; p > q :> -AngleBracket[q, p];
   reps = Table[a[i] -> tabs[[i]] /. abfourpointrule, {i, 1, 4}]
];

abfourpointrule = {AngleBracket[2,4]->(AngleBracket[1, 4]*AngleBracket[2, 3]*(s+ t)/(AngleBracket[1, 3]*t)),
	AngleBracket[3, 4] -> AngleBracket[1, 4]*AngleBracket[2, 3]*s/(AngleBracket[1, 2]*t)}

AllTransformations[vari_, pv_] := 
	Module[{vc, i, j, k, l, trafs, jacs, trafos, perm, trvar},
	trafos = {};
	Do[
		vc = Cases[vari, pv[[i, 1]][_]];
   		trafs = {};
   		jacs = {};
   		If[Length[vc] == 2,
	    	If[vc[[1, 1]] == 1 && (vc[[2, 1]] == 3 || vc[[2,1]] == 4),
	     		trafs = 
	      		Table[Trafo[{pv[[i, 2]], pv[[i, 3]]}, {j, pv[[i, 3]]}, 
	        		pv[[i, 1]]], {j, 
	        		Delete[Range[4], {{pv[[i, 3]]}, {pv[[i, 2]]}}]}
	        	];
	     		jacs = 
	      			Table[Det[
	        			Table[D[trafs[[j, k, 2]], 
	          			pv[[i, 1]][l]], {k, {1, vc[[2,1]]}}, {l, {1, vc[[2,1]]}}]], {j, 1, 
	        			Length[trafs]}];
	        	trvar = Table[{pv[[i,1]],j, pv[[i,3]]}, {j, Delete[Range[4], {{pv[[i, 3]]}, {pv[[i, 2]]}}]}];
	      		trafs=trafs[[All,{1,vc[[2,1]]}]];
	      		trafos = Append[trafos, Transpose[{trafs,jacs,trvar}]];
	     	];
	    	If[vc[[1, 1]] == 2 && (vc[[2,1]] == 3 ||vc[[2, 1]] == 4),
	     		trafs = 
	      			Table[Trafo[{pv[[i, 2]], pv[[i, 3]]}, {pv[[i, 2]], j}, 
	        			pv[[i, 1]]], {j, 
	        			Delete[Range[4], {{pv[[i, 3]]}, {pv[[i, 2]]}}]}];
	     
	     		jacs = 
	      			Table[Det[
	        			Table[D[trafs[[j, k, 2]], 
	          				pv[[i, 1]][l]], {k, {2, vc[[2,1]]}}, {l, {2, vc[[2,1]]}}]], {j, 1, Length[trafs]}];
	          	trvar = Table[{pv[[i,1]], pv[[i,2]], j}, {j, Delete[Range[4], {{pv[[i, 3]]}, {pv[[i, 2]]}}]}];
	      		trafs=trafs[[All,{2,vc[[2,1]]}]];
	      		trafos = Append[trafos, Transpose[{trafs,jacs,trvar}]];
	     	];
	    	
	    ];
	    If[Length[vc] == 4,
	    	trafs = Table[Trafo[{pv[[i,2]],pv[[i,3]]},perm,pv[[i,1]]],{perm,DeleteCases[{{1,2},{1,3},{1,4},{2,3},{2,4},{3,4}},{pv[[i,2]],pv[[i,3]]}]}];
	    	jacs = Table[Together[Det[
						Table[D[trafs[[j, k, 2]], pv[[i, 1]][l]], {k, 1, 4}, {l, 1, 4}]
	    		]],
				{j, 1, Length[trafs]}
	        ];
	    	trvar = Table[Prepend[perm,pv[[i,1]]], {perm,DeleteCases[{{1,2},{1,3},{1,4},{2,3},{2,4},{3,4}},{pv[[i,2]],pv[[i,3]]}]}];
	    	(* Table[ms@@perm^2/ms@@{pv[[i,2]],pv[[i,3]]}/.{ms[[1,2]]->s,ms[[1,3]]->-s-t,ms[[1,4]]->t,ms[[2,3]]->t,ms[[2,4]]->-s-t,ms[[3,4]]->s},
	    		{perm,DeleteCases[{{1,2},{1,3},{1,4},{2,3},{2,4},{3,4}},{pv[[i,2]],pv[[i,3]]}]}];*)
	    	trafos = Append[trafos, Transpose[{trafs,jacs,trvar}]];
	    ];
    	,
    	{i, 1, Length[pv]}
   	];
	trafos
]

(*Double Pole*)
Catch1[ex_,x_,vars_,nn_]:=Module[{fn,pd,pred},
	(*Print["CatchCommand"];*)
	(*Print[Catch11[ex,x,vars,nn]];*)
	fn=ListToFunction[{{ex[[1,1]],{}},ex[[2]]},n];
	If[pri>3,Print["fn:"]];
	If[pri>3,Print[fn]];
	pd=Select[ex[[1,2]],#[[2]]>=2&];
	If[pri>3,Print["pd:"]];
	If[pri>3,Print[pd]];
	pd=Times@@(Power[#[[1]],#[[2]]-1]&/@pd);
	If[pri>3,Print[pd]];
	pred=PolynomialRemainder[fn,pd,x];
	If[pri>3,Print[pred]];
	pred=DeleteCases[Flatten[CoefficientList[pred,vars]],0];
	If[pri>3,Print[pred]];
	RearrangeRules[Quiet[Solve[pred==0*Range[Length[pred]],nn][[1]]]]
];

Catch1New[ex_,x_,vars_,nn_]:=Module[{pd,pred,i},
	(*Print[Catch11[ex,x,vars,nn]];*)
	pd=Select[ex[[1,2]],#[[2]]>=2&];
	If[pri>3,Print["pd:"]];
	If[pri>3,Print[pd]];
	pd=Times@@(Power[#[[1]],#[[2]]-1]&/@pd);
	If[pri>3,Print[pd]];
	pred=Table[If[pri>1&&Mod[i,10] === 0, Print["PolynomialReduce: ",i]]; 
		PolynomialReduce[Times@@Power@@@ex[[2,i]], {pd}, vars][[2]], {i, 1, Length[ex[[2]]]}];
	pred=pred.nn;
	If[pri>4,Print[pred]];
	pred=DeleteCases[Flatten[CoefficientList[pred,vars]],0];
	If[pri>3,Print[pred]];
	RearrangeRules[Quiet[Solve[pred==0*Range[Length[pred]],nn][[1]]]]	
];

(*expression independent of x => Numerator exponent too high*)
Catch2[ex_,x_,vars_,nn_]:=Module[{fn,pred,rr,sol},
	(*Print["Catch2_start"];*)
	fn=ListToFunction[{{ex[[1,1]],{}},ex[[2]]},n];
	(*Print["Catch2_1"];*)
	pred=DeleteCases[Flatten[CoefficientList[fn,vars]],0];
	(*Print["Catch2_2"];*)
	sol=Quiet[Solve[pred==0*Range[Length[pred]],nn][[1]]];
	(*Print["Catch2_3"];*)
	rr=RearrangeRules[sol];
	(*Print["Catch2_end"];*)
	rr
];


(*Exponent in numerator too big*)
Catch3[ex_,x_,vars_,nn_]:=Module[{fn,pd,pred},
	fn=ListToFunction[{{ex[[1,1]],{}},ex[[2]]},n];
	Print["fn"];
	Print[fn];
	pd=Times@@Power@@@ex[[1,2]];
	(*Print["pd"];
	Print[pd];*)	
	pred=Numerator[Together[PolynomialQuotient[fn,pd,x]]];
	(*Print["pred"];
	Print[pred];*)
	pred=DeleteCases[Flatten[CoefficientList[pred,vars]],0];
	Print["after deletecases in nonlog3"];
	RearrangeRules[Quiet[Solve[pred==0*Range[Length[pred]],nn][[1]]]]
]

RearrangeRules[rules_, nn_] := Module[{},n=nn; RearrangeRules[rules]]

RearrangeRules[rules_]:=Module[{newrules, i, term, index, rul},
	rul=rules;
	newrules={};
	Do[
		term=-rul[[i,1]]+rul[[i,2]];
		index=Max[Cases[Variables[term],n[_]][[All,1]]];
		If[rul[[i,1,1]]=!=index,
			newrules=Append[newrules, Solve[term==0,n[index]][[1,1]]];
			newrules[[;;-1,2]]=newrules[[;;-1,2]]/.newrules[[-1]]//CleanExpr;
			rul[[i+1;;,2]]=rul[[i+1;;,2]]/.newrules[[-1]]//CleanExpr;
			,
			newrules=Append[newrules, rul[[i]]];
		]
		,{i,1,Length[rules]}];
		newrules[[All,2]]=CleanExpr[newrules[[All,2]]];
		SortBy[newrules,#[[1,1]]&]
];

CleanExpr[term_]:=Module[{ns, i, res},
	ns=Cases[Variables[term],n[_]];
	res = Sum[ns[[i]]*Together[Coefficient[term,ns[[i]]]],{i,1,Length[ns]}];
	If[!PossibleZeroQ[res-term],Throw[CleanExprError[term]]];
	res
];

Catch3New[ex_,x_,vars_,nn_]:=Module[{fn,pd,expon,cl,pred},
	fn=ListToFunction[{{ex[[1,1]],{}},ex[[2]]},n];	
	pd=Times@@Power@@@ex[[1,2]];
	expon=Exponent[pd,x];
	If[pri>3,Print["expon ",expon]];
	cl=CoefficientList[fn,x][[(expon+1);;]];
	(*Print["cl"];
	Print[cl];*)
	pred=DeleteCases[Flatten[CoefficientList[#,vars]&/@cl],0];
	(*Print["predd"];
	Print[pred];*)
	RearrangeRules[Quiet[Solve[pred==0*Range[Length[pred]],nn][[1]]]]
]

ListFactorWhole[fl_]:=Module[{lf,nl},
	nl=fl;
	lf=ListFactor[nl[[2]]];
	If[lf[[1,1,1]]==={0,1},Return[lf]];
	nl[[2]]=lf[[2]];
	nl[[1,1]]=CleanFactorList[Join[lf[[1,1]],nl[[1,1]]]];
	nl[[1,2]]=CleanFactorList[Join[lf[[1,2]],nl[[1,2]]]];
	nl[[1]]=ListCancel[nl[[1]]];
	nl
];


PlugInRules[exl_,rules_]:=Module[{nexl,i,j,k,l,m,rvar,cf},
	rvar={#,{}}&/@Cases[Variables[rules[[All,2]]],n[_]];
	nexl=exl;
	Do[
		cf=Coefficient[rules[[k,2]],rvar[[l,1]]];
		If[cf=!=0,
			rvar[[l,2]]=Append[rvar[[l,2]],{rules[[k,1,1]],cf}]];
		,{k,1,Length[rules]},{l,1,Length[rvar]}
	];
	Do[
		Do[
			nexl[[i,1,j,2,rvar[[l,1,1]]]]=
				SumFactorLists[Join[{nexl[[i,1,j,2,rvar[[l,1,1]]]]},Table[ProductFactorLists[{nexl[[i,1,j,2,rvar[[l,2,m,1]]]],MyFactorList[rvar[[l,2,m,2]]]}],{m,1,Length[rvar[[l,2]]]}]]];
			,{l,1,Length[rvar]}];
		Do[
			nexl[[i,1,j,2,rules[[k,1,1]]]]={{0,1}};
			,{k,1,Length[rules]}];
		(*nexl[[i,1,j]] = ListFactorWhole[nexl[[i,1,j]]];*)
		,{i,1,Length[exl]},{j,1,Length[exl[[i,1]]]}
	];
	(*Print[rvar];*)
	nexl
];


(*Assumes Factorlists with unique signs and without double elements*)
ListFactor[list_] := Module[{int, pows, minus, ls, pref, pos,i,j,res},
	ls = If[# === {},{{1,1}},If[Length[Cases[#,{0,_}]]>0,{{0,1}},If[ !NumericQ[#[[1,1]]], Prepend[#,{1,1}], #] ] ]&/@list;
	If[ls[[All,1,1]]===0*Range[Length[ls]],Return[{{{{0,1}},{{1,1}}},ls}]];
   ls =  If[#[[1, 1]] === 0, {{0, 1}}, #] & /@ ls;
   pos = Complement[Range[Length[ls]], 
     Flatten[Position[ls, {{0, 1}}]]];
   int = Intersection @@ ls[[pos, 2 ;;, 1]];
   pows = 
    Function[x, 
      Min[(FirstCase[#, {x, _}] & /@ ls[[pos]])[[All, 2]]]] /@ int;
   ls[[pos]] = 
    DeleteCases[#, {_, 
        0}] & /@ (ls[[pos]] /. ({#[[1]], q_} :> {#[[1]], 
            q - #[[2]]} & /@ Transpose[{int, pows}]));
   minus = GatherBy[Cases[Join @@ ls, {_, n_ /; n < 0}], First];
   minus = {#[[1, 1]], Min[#[[All, 2]]]} & /@ minus;
   Do[
    ls[[pos]] = 
     Table[If[MemberQ[ls[[i]], {minus[[j, 1]], _}], 
       ls[[i]] /. {minus[[j, 1]], q_} :> {minus[[j, 1]], 
          q - minus[[j, 2]]}, 
       Append[ls[[i]], {minus[[j, 1]], -minus[[j, 2]]}]], {i, pos}],
    {j, 1, Length[minus]}
    ];
   pref = DeleteCases[Join[minus, Transpose[{int, pows}]], {_, 0}];
   ls = DeleteCases[#, {_, 0}] & /@ ls;
   res={{Select[pref, #[[2]] > 0 &], {#[[1]],-#[[2]]}&/@Select[pref, #[[2]] < 0 &]}, ls};
   If[res[[1,1]]==={},res[[1,1]]={{1,1}}];
   If[res[[1,2]]==={},res[[1,2]]={{1,1}}];
   Do[If[res[[2,i]]==={},res[[2,i]]={{1,1}}],{i,Length[res[[2]]]}];
   If[!NumericQ[res[[1,1,1,1]]],res[[1,1]]=Prepend[res[[1,1]],{1,1}]];
   If[!NumericQ[res[[1,2,1,1]]],res[[1,2]]=Prepend[res[[1,2]],{1,1}]];
   Do[If[!NumericQ[res[[2,i,1,1]]],res[[2,i]]=Prepend[res[[2,i]],{1,1}]],{i,Length[res[[2]]]}];
   res
];

SumFactorLists[lists_] := Module[{lfa, i, res},
	lfa = ListFactor[lists];
	lfa = Join @@ {lfa[[1, 1]], {#[[1]],-#[[2]]}&/@lfa[[1,2]],
    	MyFactorList[
      		Sum[Times @@ Power @@@ lfa[[2, i]], {i, 1, Length[lfa[[2]]]}]]};	
	lfa=GatherBy[lfa,First];
	lfa={#[[1,1]],Plus@@#[[All,2]]}&/@lfa;
	lfa = Join[MyFactorList[Times @@ Power @@@ Select[lfa, NumericQ[#[[1]]] &]], 
   		Select[lfa, ! NumericQ[#[[1]]] &]];
   	res=If[lfa[[1,1]]==0,{{0,1}},lfa];
   	If[Length[res]<1 || !NumericQ[res[[1,1]]], Print["SumToFactor Error"]; Print[SummFactorLists[lists]]];
   	res
]

Wellshaped[flist_]:= Min[Length/@Join[flist[[1]],flist[[2]]]]>=1

MyListApartNew[flist_,x_]:=Module[{num,den,nums,denlist,tab,cl,i,pos,nlist},
	If[pri>8,Print[MyListtApartNew[flist,x]]];
	(*Print[MyListtApartNew[flist,x]];*)
	If[!Wellshaped[flist], Print["Not well shaped"]; Print[flist]];
	num=flist[[1,1]];
	den=flist[[1,2]];
	nums=flist[[2]];
	pos=Position[den,{q_,_}/;!FreeQ[q,x]];
	denlist=den[[Flatten[pos]]];
	If[Length[denlist]==0,Throw[NonLog2[flist,x]]];
	If[Max[Select[den,!FreeQ[#,x]&][[All,2]]]>=2,Throw[NonLog1[flist,x]]];
	If[Max[Plus @@@ Map[Exponent[#[[1]], x]*#[[2]] &, nums, {2}]]+Plus @@ Map[Exponent[#[[1]], x]*#[[2]] &, num, {1}]>=Plus @@ Map[Exponent[#[[1]], x]*#[[2]] &, den, {1}],
		Throw[NonLog3[flist,x]]];
	tab=Table[
		cl=CoefficientList[denlist[[i,1]],x];
		If[Length[cl]>2,Throw[GetSquareRoot[flist,x]]];
		nlist=flist;
		nlist[[1,2]]=ProductFactorLists[{Delete[nlist[[1,2]],pos[[i,1]]],MyFactorList[cl[[2]]]}];
		nlist=MyFLInsertFunc[nlist,x->-cl[[1]]/cl[[2]]];
		{nlist,Power@@denlist[[i]]}
		,{i,1,Length[denlist]}];
	tab	
	
]

(*searches for double poles and returns a list of rules or the residues*)
MyListApartDB[flist_,x_]:=Module[{num,den,nums,denlist,tab,cl,i,pos,nlist},
	If[pri>8,Print[MyListtApartNew[flist,x]]];
	(*Print[MyListtApartNew[flist,x]];*)
	If[!Wellshaped[flist], Print["Not well shaped"]; Print[flist]];
	num=flist[[1,1]];
	den=flist[[1,2]];
	nums=flist[[2]];
	pos=Position[den,{q_,_}/;!FreeQ[q,x]];
	denlist=den[[Flatten[pos]]];
	If[Length[denlist]==0,Throw[NonLog2[flist,x]]];
	If[Max[Select[den,!FreeQ[#,x]&][[All,2]]]>=2,Throw[NonLog1[flist,x]]];
	If[Max[Plus @@@ Map[Exponent[#[[1]], x]*#[[2]] &, nums, {2}]]+Plus @@ Map[Exponent[#[[1]], x]*#[[2]] &, num, {1}]>=Plus @@ Map[Exponent[#[[1]], x]*#[[2]] &, den, {1}],
		Throw[NonLog3[flist,x]]];
	tab=Table[
		cl=CoefficientList[denlist[[i,1]],x];
		If[Length[cl]>2,Throw[GetSquareRoot[flist,x]]];
		nlist=flist;
		nlist[[1,2]]=ProductFactorLists[{Delete[nlist[[1,2]],pos[[i,1]]],MyFactorList[cl[[2]]]}];
		nlist=MyFLInsertFunc[nlist,x->-cl[[1]]/cl[[2]]];
		{nlist,Power@@denlist[[i]]}
		,{i,1,Length[denlist]}];
	tab	
	
]

ProductFactorLists[lists_]:=Module[{lis},
	lis=Join@@lists;
	lis=GatherBy[lis,First];
	lis={#[[1,1]],Plus@@#[[All,2]]}&/@lis;
	lis=DeleteCases[lis,{_,0}];
	lis=Join[MyFactorList[Times @@ Power @@@ Select[lis, NumericQ[#[[1]]] &]], 
   		Select[lis, ! NumericQ[#[[1]]] &]];
   	If[lis[[1,1]]===0,{{0,1}},lis]
];

MyFLInsertList[list_, rep_] := 
 Module[{res, i}, 
  res = ProductFactorLists[
    Append[Table[{#[[1]], #[[2]]*list[[i, 2]]} & /@ 
       MyFLInsert[list[[i, 1]], rep], {i, 2, 
       Length[list]}], {list[[1]]}]];
  (*If[! PossibleZeroQ[
     Times @@ Power @@@ res - (Times @@ Power @@@ list /. rep)], 
   Throw[MyFLInsertErrorList[list, rep]]];*)
   (*If[Or@@(Head[Factor[#[[1]]]]===Times&/@res),Throw[NotMyFLInsertListFactored[list,rep]]];*)
  res
]

MyFLInsert[fac_, rep_] := Module[{},
	MyFactorList[fac/.rep]
]

MyFLInsertFunc[flist_, rep_] := Module[{res},
	If[!Wellshaped[flist], Print["Input not well shaped"]; Print[MyyFLInsertFunc[flist, rep]]];
  	res = Map[MyFLInsertList[#, rep] &, flist, {2}];
  	res = CleanMinusListPlusFactorOut[res];
  	If[!Wellshaped[res], Print["Output not well shaped"]; Print[MyyFLInsertFunc[flist, rep]]];
  (*If[! PossibleZeroQ[
     ListToFunction[res, n] - (ListToFunction[flist, n] /. rep)], 
   Throw[MyFLInsertErrorFunc[flist, rep]]];*)
   (*Do[If[And@@(Head[Factor[#[[1]]]]===Times&/@res[[i,j]]),Throw[NotMyFLInsertFunc[flist,rep]]];,{i,1,Length[res]},{j,1,Length[res[[i]]]}];*)
  	res
]

MyFactorList[expr_] := Module[{fl, m, i, factored, time},
  (*Print[MyyFactorList[expr]];*)
  If[(UseMacaulay===True)&&(ByteCount[expr]>10000),
  	fl=TimeConstrained[FactorList[expr],2,Fail];
  	If[fl===Fail,
  		If[pri>-1,Print["Use M2. file: ",random,", size: ",ByteCount[expr]]];
  		{time,factored}=AbsoluteTiming[M2Factor[expr]];
  		If[pri>-1,Print["M2-time : ",time]];
  		(*{time,factored}=AbsoluteTiming[Factor[expr]];
  		Print["MA-time : ",time];*)
  		If[Head[factored]===Times,fl=List@@factored,fl={factored}];
  		fl=If[Head[#]===Power,{#[[1]],#[[2]]},{#,1}]&/@fl;
  		If[Length[fl]<1,Print["short"]; Print[fl],If[Length[fl[[1]]]<1,Print["other short"];Print[fl]]];
  		If[!IntegerQ[fl[[1,1]]],
  			If[Head[fl[[1,1]]]===Rational,fl=Prepend[fl,{Numerator[fl[[1,1]]],fl[[1,2]]}];fl[[2]]={Denominator[fl[[2,1]]],-fl[[2,2]]};
  				,
  				fl=Prepend[fl,{1,1}];
  			]
  		];
  	];
  	,
  	(*Print["Not using M2 ",ByteCount[expr]];*)
  	fl=FactorList[expr];
  ];
  (*fl = FactorList[expr];*)
  m = 0;
  Prepend[
   Table[If[Order[fl[[i, 1]], -fl[[i, 1]]] == 1, 
     If[Mod[fl[[i,2]],2]==1,m++]; {-fl[[i, 1]], fl[[i, 2]]}, fl[[i]]],
      {i, 2, Length[fl]}],
    {fl[[1, 1]]*(-1)^m, fl[[1, 2]]}]
]

MyFactor[expr_]:=Module[{fac, time(*, exp*)},
	If[UseMacaulay=!=True, Return[Factor[expr]]];
	fac=TimeConstrained[Factor[expr],2,Fail];	
  	If[fac===Fail,
  		(*exp=TimeConstrained[Cancel[expr],20,Print["no cancel"];expr];
  		Print["cancel worked"]; Print[ByteCount[expr]]; Print[ByteCount[exp]];*) 
  		If[pri>-1,Print["Use M2. file: ",random,", size: ",ByteCount[expr]]];
  		{time,fac}=AbsoluteTiming[M2Factor[expr]];
  		If[pri>-1,Print["M2-time : ",time]];
  		(*{time,factored}=AbsoluteTiming[Factor[expr]];
  		Print["MA-time : ",time];*)
  	];
  	fac	
]

M2Factor[term_] := Module[{vars, repl, irepl, string, str, out},
  vars = Variables[term];
  repl = Table[
    vars[[i]] -> ToExpression["v" <> ToString[i]], {i, 1, 
     Length[vars]}];
  irepl = 
   Table[ToExpression["v" <> ToString[i]] -> vars[[i]], {i, 1, 
     Length[vars]}];
  Put[term /. repl, datapath <> "/unfactored"<>ToString[random]<>".m"];
  str = OpenWrite[datapath <> "/temp"<>ToString[random]<>".m2"];
  WriteString[str, 
   "S=QQ[" <> StringTake[ToString[vars /. repl], {2, -2}] <> "];\n"];
  WriteString[str, "file=\"" <> datapath <> "/unfactored"<>ToString[random]<>".m\";\n"];
  WriteString[str, "prob = value get file;\n"];
  WriteString[str, "factored = factor prob;\n"];
       WriteString[str, 
   "\"" <> datapath <> 
    "/factored"<>ToString[random]<>".txt\"<<toString(factored)<<endl<<close;\n exit();\n"];
  Close[str];
  Run[MacaulayPath <> " " <> datapath <> "/temp"<>ToString[random]<>".m2 --silent --stop"];
  str = OpenRead[datapath <> "/factored"<>ToString[random]<>".txt"];
  string = Read[str, Word];
  out = ToExpression[string] /. irepl;
  out
]

(*remove all fractions from n-coefficients and put common factors into overall numerator*)
CleanMinusListPlusFactorOut[flist_]:=Module[{i, tab, lcm, clean, gcd},
	clean={{{},{}},{}};
	tab=Table[Cases[flist[[2,i]],x_/;x[[2]]<0],{i,1,Length[flist[[2]]]}];
	lcm=LCMlist[Table[{#[[1]],-#[[2]]}&/@tab[[i]],{i,1,Length[tab]}]];
	clean[[2]]=ProductFactorLists[{#,lcm}]&/@flist[[2]];
	gcd=GCDlist[clean[[2]]];
	clean[[2]]=ProductFactorLists[{#,InvFL[gcd]}]&/@clean[[2]];
	clean[[1,2]]=ProductFactorLists[{flist[[1,2]],lcm}];
	clean[[1,1]]=ProductFactorLists[{flist[[1,1]],gcd}];
	clean[[1]]=ListCancel[clean[[1]]];
	If[!PossibleZeroQ[ListToFunction[clean,n]-ListToFunction[flist,n]],Throw[CleanMinusLFOFail[flist]];];
	clean
	
];


InvFL[list_]:=If[#[[1]]===1,{1,1},{#[[1]],-#[[2]]}]&/@list;

LCMlist[lists_]:=Module[{l,lcm,i},
	l=Join@@lists;
	lcm={{1,1}};
	For[i=1,i<=Length[l],i++,
		If[NumericQ[l[[i,1]]],
			lcm[[1,1]]=LCM[lcm[[1,1]],l[[i,1]]^l[[i,2]]],
			If[ MemberQ[lcm[[All,1]],l[[i,1]]],
				lcm=Append[ DeleteCases[lcm,{l[[i,1]],_}], {l[[i,1]],Max[l[[i,2]],FirstCase[lcm,{l[[i,1]],_}][[2]]]}],
				lcm=Append[lcm,l[[i]]];
			];
		];
	];
	lcm
];

(*expects the first factor to be numeric*)
GCDlist[lists_]:=Module[{clists, res, inters, i, mins},
	If[Min@@lists[[All,All,2]]<1,Throw[InvalidGCDInput[lists]]];
	clists=DeleteCases[lists,{{0,1},___}];
	res={{GCD@@(clists[[All,1,1]]^clists[[All,1,2]]),1}};
	inters=Intersection@@clists[[All,2;;,1]];
	mins=Min@@(Table[FirstCase[clists[[i,2;;]],{#,_}][[2]],{i,1,Length[clists]}])&/@inters;
	res=Join[res,Transpose[{inters,mins}]]
];

ListCancel[{num_,den_}]:=Module[{gat,res,gcd},
	gat=GatherBy[Join[num,{#[[1]], -#[[2]]} & /@ den],First];
	gat={#[[1,1]],Total[#[[All,2]]]}&/@gat;
	res={Select[gat,#[[2]]>0&],{#[[1]],-#[[2]]}&/@Select[gat,#[[2]]<0&]};
	res[[1]]=Join[MyFactorList[Times @@ Power @@@ Select[res[[1]], NumericQ[#[[1]]] &]], 
   		Select[res[[1]], ! NumericQ[#[[1]]] &]];
    res[[2]]=Join[MyFactorList[Times @@ Power @@@ Select[res[[2]], NumericQ[#[[1]]] &]], 
   		Select[res[[2]], ! NumericQ[#[[1]]] &]];
   	If[res[[2,1]]==0,Throw[ZeroNumerator[{num,den}]]];
   	If[res[[1,1]]==0,Return[{{{0,1}},{{1,1}}}]];
   	gcd=GCD[Power@@res[[2,1]],Power@@res[[1,1]]];
   	res[[2,1]]={Power@@res[[2,1]]/gcd,1};
   	res[[1,1]]={Power@@res[[1,1]]/gcd,1};
   	res
];

ListToFunction[list_,n_]:=Module[{i},
	Times@@Power@@@list[[1,1]]/Times@@Power@@@list[[1,2]]*Sum[n[i]*Times@@Power@@@list[[2,i]],{i,1,Length[list[[2]]]}]
];



insertNewRandom[list_,n_]:=Module[{r,i},
	r=Table[RandomComplex[WorkingPrecision->n],{i,1,Length[list]}];
	Table[list[[i]]->r[[i]],{i,1,Length[list]}]
];


MinSub[mat_,order_]:=Module[{base,l,ind},
	ind={};
	l=0;
	base={};
	For[i=1,i<=Length[mat],i++,
		base=Append[base,mat[[order[[i]]]]];
		l++;
		If[MatrixRank[base]<l,
			base=Delete[base,-1];
			l--;
			,
			ind=Append[ind,order[[i]]];
		];
	];
	{base,ind}
]

GetLinsN[list_, vars_]:=Module[{allv,lis,sl,rl,ar,ir,n,ms,mat,b,ind,ls,j,q,i,k,gl},

	allv=vars;
	n=Length[list]*10+25;
(*n=60;*)
	ir=insertNewRandom[allv,n+2];
	(*Print["GetLinsN: Before insert"];*)
	lis=list/.ir;
	(*Print["GetLinsN: After insert"];*)
	rl=Round[Re[#]*10^n]&/@lis;
(*Print[rl];*)
	ar=Transpose[Append[IdentityMatrix[Length[lis]],rl]];
	(*Print["Before Lattice Reduce"];*)
	ar=LatticeReduce[ar];
	(*Print["After Lattice Reduce"];*)
	rl=Round[Im[#]*10^n]&/@lis;
	(*ai=Transpose[Append[IdentityMatrix[Length[lis]],rl]];
	ai=LatticeReduce[ai];*)
	ar=Sort[Select[ar,Norm[#]< 50&]];
	ar=#[[;;-2]]&/@ar;	
	If[Length[ar]==0,Return[{Range[Length[list]],IdentityMatrix[Length[list]]}]];
	sl=Reverse[Sort[Transpose[{ByteCount[#]&/@list,Range[Length[list]]}]]];
	ms=MinSub[Transpose[ar],sl[[All,2]]];
	mat=ar[[All,Sort[ms[[2]]]]];
	ind=Select[Range[Length[list]],!MemberQ[ms[[2]],#]&];
	b=Table[-Sum[ar[[i,ind[[j]]]]*q[j],{j,1,Length[ind]}],{i,1,Length[ar]}];
	ls=LinearSolve[ar[[All,Sort[ms[[2]]]]],b];
	j=0;
	gl={ind,Table[If[MemberQ[ind,i],UnitVector[Length[ind],Position[ind,i][[1,1]]],
		j++;Table[Coefficient[ls[[j]],q[k]],{k,1,Length[ind]}]],
		{i,1,Length[list]}]};
	(*If[!CheckLinsInt[list,vars,gl],Throw[ErrorInGetLinsN[list,gl]]];*)
	gl
]

GetLinsN[list_]:=GetLinsN[list,Variables[list]];


GetLinsOrd2[funcs_]:=Module[{nfuncs, df, i, res},
	nfuncs=(Sort[{#,-#}][[1]])&/@funcs;
	df=DeleteDuplicates[nfuncs];
	res={Table[Position[nfuncs,df[[i]]][[1,1]],{i,Length[df]}],{}};
	Print["Delete Duplicates: ", Length[funcs], ", -> ", Length[res[[1]]]];
	res
]

GetLinsTiz[funcs_]:=Module[
	{vars,nvars,nfuncs,extra,sampletable,newvars,repl,newfuncs,func,h,i,j,
		coeffs,system,sol,indep,coeff,dep,indepcoeffs, zero, fun, rels, (*trues, *)table},
	If[pri>3, Print["GetLinsTiz ", Length[funcs]]];
	If[pri>13, Print[GetLinsTizz[funcs]]];
	vars = Variables[funcs];
	nvars = Length[vars];
	nfuncs = Length[funcs];
	(* Extra samplings added for safety *)
	extra = 5;
	
	newvars=ToExpression["v"<>ToString[#]]&/@Range[nvars];
	repl=Dispatch[(vars[[#]]->newvars[[#]])&/@Range[nvars]];
	newfuncs=funcs/.repl;
	Do[func[i]=Function[Evaluate[newvars],Evaluate[newfuncs[[i]]]],{i,nfuncs}];
	coeffs=Table[coeff[i],{i,nfuncs}];
	(*system=(coeffs.#==0)&/@Table[funcs/.samples[[ii]],{ii,Length[samples]}];*)
	(*samples = Table[Dispatch[Table[vars[[i]]->Prime[7+2 i+j],{i,1,nvars}]],{j,1,nfuncs+extra}];*)
	Do[
		If[pri>3, Print["k ", h]];
		SeedRandom[nfuncs];
		sampletable=Table[RandomSample[Table[Prime[7+10*h+(2+h)i+j],{i,1,nvars}]],{j,1,nfuncs+extra}];	
		(*Print[Table[func[i],{i,nfuncs}]];*)
		table = Quiet[Table[func[i]@@sampletable[[j]],{j,Length[sampletable]},{i,nfuncs}], {Power::infy, Infinity::indet}];
		If[MemberQ[Flatten[table], Indeterminate|ComplexInfinity], Continue[]];
		system= (coeffs.#==0)&/@table;	
		If[h==25, Print["GetLinsTikz Failed by division to zero"]; Put[funcs, "~/workspace/lsing/GetLinsN/GetLinsTizError.txt"]; Abort[];];
		Break[];
		,
		{h,0,30}
	];
	sol=Quiet[Solve[system,Reverse[coeffs]],Solve::svars][[1]];
	(* This should be the list of independent functions *)
	indep=Reverse[#[[1,1]]&/@sol];
	(* This should be the list of NOT independent functions *)
	dep = Complement[Range[Length[funcs]],indep];
	(* indep. coefficients = NOT indep. functions *)
	indepcoeffs = coeff/@dep;
	zero = Sum[coeff[i]fun[i],{i,1,nfuncs}]/. sol;
	rels=Solve[Table[Coefficient[zero,indepcoeffs[[i]]]==0,{i,1,Length[indepcoeffs]}],fun/@dep][[1]];
	(*trues=Table[PossibleZeroQ[funcs[[j]]-(fun[j]/.rels/.fun[k_]:>funcs[[k]])],{j,nfuncs}];
	If[!(And@@trues), Print["Error in GetLinsTiz"]; Put[funcs, "~/workspace/lsing/GetLinsN/GetLinsTizError.txt"]; Abort[]];*)
	{indep, Table[ConstantArray[0,Length[indep]]+(fun[i]/.rels/.(fun[k_]:>UnitVector[Length[indep],FirstPosition[indep,k][[1]]])),{i,nfuncs}]}
]

CatchNoTrafo[prob_, vars_]:=Module[{pd},
	(*prob:=flist*)
	Print["No Trafo"];
	Abort[];
	pd=Cases[prob[[1,2]],q_/;And@@(Exponent[q[[1]],#]>=2&/@vars)];
	If[pri>0,Print["pd:"]];
	If[pri>0,Print[pd]];
	Abort[];
	pd=Times@@(Power[#[[1]],#[[2]]-1]&/@pd);
	If[pri>3,Print[pd]];
	pred=Table[If[pri>1&&Mod[i,10] === 0, Print["PolynomialReduce: ",i]]; 
		PolynomialReduce[Times@@Power@@@ex[[2,i]], {pd}, vars][[2]], {i, 1, Length[ex[[2]]]}];
	pred=pred.nn;
	If[pri>4,Print[pred]];
	pred=DeleteCases[Flatten[CoefficientList[pred,vars]],0];
	If[pri>3,Print[pred]];
	RearrangeRules[Quiet[Solve[pred==0*Range[Length[pred]],nn][[1]]]]
]

(*Warning: Handling of sqrt[__] in the numerator is not fully resolved*)
FactorCollect[term_]:=Module[{res, t1, num, den, ns, nds, collnum, lcm, gcd, ii, faclist},
	(*Put[term,"~/workspace/lsing/UnsolvedCases/FactorCollect.txt"];*)
	If[PossibleZeroQ[term], Return[0]];
	If[pri>7, Print["FactorCollect1"]];
	t1= term/.sqrt[av_] :> sqrt[MyFactor[av]] //.sqrt[av_^i_ bv_.]/;i<0:>sqrt[bv]/sqrt[av^(-i)]//.(sqrt[av_ bv_.]/av_):>sqrt[bv]/sqrt[av]
		/.sqrt[Rational[av_,bv_]cv_.]:>sqrt[av cv]/sqrt[bv]//. sqrt[av_^i_ bv_.]/;Mod[i,2]==0 :> av^(i/2) sqrt[bv] /. 
     sqrt[av_?(NumericQ)] :> Sqrt[av] 
     /.sqrt[av_]^iv_/;iv>0:>av^Quotient[iv,2]sqrt[av]^Mod[iv,2] /.sqrt[av_]^iv_/;iv<0:>av^(-Quotient[-iv,2])sqrt[av]^(-Mod[-iv,2])
     /.sqrt[av_]/av_:>1/sqrt[av]/.av_/sqrt[av_]:>sqrt[av]
     /.sqrt[a_]:>Times@@(sqrt/@(ProductToList[MyFactor[a]]))
      //.sqrt[av_]^(-1) sqrt[bv_]^(-1):>sqrt[av bv]^(-1);
    (*Print[t1];*)
    faclist = ProductToList[t1];
	num=Times@@Cases[faclist, _?(!FreeQ[#,n[_]]&)];
	den = Times@@Cases[faclist, _?(FreeQ[#,n[_]]&)];
	ns=Union[Cases[{t1},n[_], Infinity]];
	If[pri>7, Print["FactorCollect2"]];
	collnum = Collect[num, n[_], MyFactor];
	If[pri>7, Print["FactorCollect3a"]];
	nds = {Numerator[#], Denominator[#]} & /@ (Coefficient[collnum, #] & /@ ns);
	If[pri>7, Print["FactorCollect3b"]];
	If[Length[nds]==0, Print[term]];
	If[pri>7, Print["FactorCollect3c"]];
    lcm = PolynomialLCM @@ nds[[All, 2]];
    If[pri>7, Print["FactorCollect3d"]];
    gcd = PolynomialGCD@@ nds[[All,1]];
    If[pri>7, Print["FactorCollect3e"]];
	res=Sum[MyFactor[nds[[ii, 1]]/gcd] MyFactor[lcm/nds[[ii, 2]]] ns[[ii]], {ii, Length[nds]}] MyFactor[gcd den/lcm];
	If[pri>7, Print["FactorCollect4"]];
	If[!PossibleZeroQ[t1-res], Print["FactorCollect test failed"]; Print[term];Abort[]];
	If[pri>7, Print["FactorCollect5"]];	
	res	
]


ExSQRT[terms_, vars_, nn_] :=
    Module[ {vs, nterms, rules, nex, next, gl, i, lsings},
        If[Length[vars]==0,Return[{{terms},{}}]];
    	n=nn;
    	lsingvars=vars;
        If[ pri>1,
            Print[ExxSQRT[terms, vars, n]]
        ];
        
        If[ pri>0,
            Print["ExSQRT"];
        ];
        vs = vars;
        
        If[ Head[terms] === List,
            nterms = {#, vs} & /@ terms,
            nterms = {{terms, vars}}
        ];
        nterms=nterms/.Power[a_,-1/2]:>1/sqrt[a];
        rules = {};
        Do[
         If[ sqrtlsing,
             PrintTemporary["Variable ", i, " of ", Length[vars]];
         ];
         (*Print[nterms];*)
         nex = Table[
           If[ pri>1,
               Print["Term ", i, " of ", Length[nterms]]
           ];	
           next = 
            ExSqrtList[FactorCollect[nterms[[i, 1]] /. rules], nterms[[i, 2]], n];
           
           rules = Union[rules /. next[[2]], next[[2]]];
           next,
           {i, Length[nterms]}];
         (*Print["nex"];*)
         (*Print[nex];*)
         nterms = nex[[All, {1, 3}]] /. rules;
         nterms = 
          Join @@ Table[{nterms[[i, 1, j]], nterms[[i, 2]]}, {i, 
             Length[nterms]}, {j, Length[nterms[[i, 1]]]}];
         lsings=FactorCollect/@(nterms[[All,1]]);
         gl = GetLinsOrd[lsings][[1]];
        
         lsings = lsings[[gl]];
         gl = GetLinsOrd[lsings][[1]];

         (*Print[nterms];*)
         , {i, Length[vars]}];
        {lsings, rules}
    ]

ExSqrtList[term_, vars_, nn_] :=
    Module[ {nterm, rules, nrules, i, fsv, xxx, probs, rest, sqr, ls},
    	n=nn;
    	(*Print[ExxSqrtList[term,vars,n]];*)
    	If[pri>4,Print["ExSqrtList"]];
        nterm = term;
        rules = {};
        Do[
        	nterm = FactorCollect[nterm /. rules];
         	nrules = FindDoublePoles[nterm, vars, n][[1]];
         	If[pri>0 && Length[nrules>0], Print["nrules: ",nrules]];
         	If[ Length[nrules] == 0,
            	Break[],
             	rules = Union[rules /. nrules, nrules];
         	];
         	If[ i == 20,
             	Print["Too many iteration searching for double poles"]
         	]
         	,
         	{i, 20}
        ];
        If[pri>2, Print["nrules"];Print[nrules];];
        If[ nterm === 0,
            Return[{{}, rules, {}}]
        ];
        fsv = FindSimplestVariable[nterm, vars];
        If[ Min[fsv] > 10000,
            nterm = FindTransformation[nterm, vars];
            If[pri>1,Print["Found"]];
            If[pri>1,Print[nterm]];
        ];
        (*Search again for double poles after possible transformation*)
        Do[
        	nterm = FactorCollect[nterm /. rules];
         	nrules = FindDoublePoles[nterm, vars, n][[1]];
         	If[pri>0 && Length[nrules>0], Print["nrules: ",nrules]];
         	If[ Length[nrules] == 0,
            	Break[],
             	rules = Union[rules /. nrules, nrules];
         	];
         	If[ i == 20,
             	Print["Too many iteration searching for double poles"]
         	]
         	,
         	{i, 20}
        ];
        
        If[ nterm === Failed[_],
            Print["No simple variable found and no transformation found"];
            Throw[UnsolvedTerm[term/.sqrt->Sqrt/.npar[1]:>1,vars],UnsolvedTerm];
            Return[Failed[]],
            fsv = FindSimplestVariable[nterm, vars];
        ];
        If[ Min[fsv] > 10000,
            Print["Failed after transformation"];
            (*Print[nterm];*)
            Throw[UnsolvedTerm[term/.sqrt->Sqrt/.npar[1]:>1,vars],UnsolvedTerm];
        ];
        xxx = vars[[Ordering[fsv][[1]]]];
        (*
        Print["xxx"];
        Print[xxx];
        Print[Variables[term]];*)
        sqr = Cases[{nterm}, sqrt[_]^(-1), Infinity];
        If[ Length[sqr] > 1,
            Print["Too many square roots in one term"];
            Throw[UnsolvedTerm[term/.sqrt->Sqrt/.npar[1]:>1,vars],UnsolvedTerm];
        ];
        (*Print[nterm];*)
        If[ Length[sqr] == 0,
		        
            rest = nterm;
            sqr = 1,
            sqr = 1/sqr[[1]];
            rest = nterm*sqr
        ];
        (*Print[sqr];*)
        (*probs = ((*Join@@(ConvertQuadratic[#,xxx,vars]&/@*)(#/sqr&)/@ApartListSQRT[rest,xxx]);(*FactorCollect/@SumToList[Apart[rest, xxx]];*)*)
        probs =Join@@(ConvertQuadratic[#,xxx,vars]&/@ (#/sqr&)/@ApartListSQRT[rest,xxx]);(*FactorCollect/@SumToList[Apart[rest, xxx]];*)
        (*Print[probs];*)
        (*Print[sqr];*)

        ls = If[ sqr === 1 || Exponent[sqr[[1]], xxx] == 0,

                 (*(ExSqrt[#, xxx]/sqr /. sqrt[1] -> 1) & /@ probs;
                 probs = (#/sqr & /@ probs);*)
                 ExSqrt[#, xxx] & /@ probs
                 ,
                 (*probs = (#/sqr & /@ probs);*)
                 ExSquareRoot[#, xxx] & /@ probs
                (* ExSqrt[#,xxx]&/@probs,
                 ExSquareRoot[#,xxx] &/@probs;*)
             ];
         If[!FreeQ[ls,Failed[]],Print["Failed with nested square root"];Throw[UnsolvedTerm[term/.sqrt->Sqrt/.npar[1]:>1,vars],UnsolvedTerm];];
         (*Print[Length/@ls];*)
        {Join @@ ls, rules, DeleteCases[vars, xxx]}
    ]

ApartListSQRT[term_, xx_] :=
    Module[ {diff, quo, rem, st, out},
		(*Put[ApartListSQRTT[term, xx],"~/workspace/lsing/UnsolvedCases/ApartList.txt"];*)
    	If[pri>2,Print["ApartListSQRT1"]];
        diff = Exponent[Numerator[term], xx] - 
          Exponent[Denominator[term], xx];
        If[pri>4,Print["ApartListSQRT2"]];
        If[ diff > 0,
            Print["Double Pole in Apart List"];
            Print[ApartListSQRTT[term,xx]];
            Abort[]
        ];
        If[pri>4,Print["ApartListSQRT3"]];
        If[ diff == 0,
        	If[pri>1,Print["ply"]];
            {quo, rem} = 
            PolynomialQuotientRemainder[Numerator[term], Denominator[term], xx];
            If[pri>1,Print["ply fin"]];
            rem = rem/Denominator[term],
            rem = term;
            quo = 0
        ];
        If[pri>4,Print["ApartListSQRT4"]];
        If[pri>4,Print[xx]];
        st = FactorCollect /@ ApartList[rem, xx];
        If[pri>4,Print["ApartListSQRT5"]];
        Do[If[ Exponent[Numerator[st], xx] - Exponent[Denominator[st], xx] >=
             0 || Exponent[Denominator[st], xx] > 2,
               Print["Apart Error!"];
               Abort[]
           ], {i, Length[st]}];
        If[pri>4,Print["ApartListSQRT6"]];
        out =
            DeleteCases[Prepend[st, FactorCollect[quo]], 0];
		If[pri>4,Print["ApartListSQRT7"]];
        If[!PossibleZeroQ[out-term], Print["ApartListSQRT test failed"]; Print[term]; Print[xx]; Abort[]];
        If[pri>2,Print["ApartListSQRT fin"]];
        out
    ]

ApartList[term_, x_] :=
    Module[ {dens, lins, squares, a, b, c, p, s, rad, g, u, v, i, const, 
      con, muster, linstable, squarestable, t1, t2, tsum, res, reps, 
      clnum, cl,varstozeta,zetatovars},
      If[pri>10,Print["ApartList"]];
      If[pri>10,Print[ApartListt[term, x]]];
        dens = ProductToList[Denominator[term]];
        lins = Cases[dens, _?(Exponent[#, x] == 1 &)];
        squares = Cases[dens, _?(Exponent[#, x] == 2 &)];
        const = Times @@ Complement[dens, Join[lins, squares]];
        If[ ! FreeQ[const, x],
            Print["Apart Error"];
            Abort[]
        ];
        muster = 
         Sum[g[i] x^i, {i, 0, 
            Exponent[Numerator[term], x]}]/(Product[
             u[i] x + v[i], {i, Length[lins]}] Product[
             a[i] x^2 + b[i] x + c[i], {i, Length[squares]}] con);
        linstable = 
         Table[MyFactor[(muster (u[i] x + v[i]) /. x -> -v[i]/u[i])/ (u[i] x +
               v[i])], {i, Length[lins]}];
        If[Length[squares]>0,
        	squarestable = 
         		Table[t1 = (muster (a[i] x^2 + b[i] x + 
                  	c[i])/(a[i] (x - (p + s)/(2 a[i]))) /. 
              				x -> (p - s)/(2 a[i]))/(x - (p - s)/(2 a[i]));
              (* t2 = (muster (a[i] x^2 + b[i] x + 
                       c[i])/(a[i] (x - (p - s)/(2 a[i]))) /. 
                   x -> (p + s)/(2 a[i]))/(x - (p + s)/(2 a[i]));*)
               varstozeta=Table[DeleteCases[Variables[t1], s][[i]] -> Zeta[100+2*i + 1], {i, Length[Variables[t1]] - 1}];
               zetatovars=Table[varstozeta[[i, 2]] -> varstozeta[[i, 1]], {i, Length[varstozeta]}];
               tsum=Factor[2 Re[t1/.varstozeta/.s->I Zeta[99]]]/.zetatovars/.Zeta[99]^j_/;Mod[j,2]==0:>(-rad)^(j/2);
               If[ ! FreeQ[tsum, Zeta[99]],
                   Print["Apart Error s"];
                   Abort[]
               ];
               tsum /. {p -> -b[i], s -> b[i]^2 - 4 a[i] c[i], 
                 rad -> (b[i]^2 - 4 a[i] c[i])}, {i, Length[squares]-1}];
        	,
        	squarestable={};
    	];	
        (*linstable=MyFactor/@linstable;*)
        (*squarestable=MyFactor/@squarestable;*)
       (* Print[linstable/.{a->Global`a,b->Global`b,c->Global`c,u->Global`u,v->Global`v,g->Global`g,con->Global`con}];
        Print[squarestable/.{a->Global`a,b->Global`b,c->Global`cc,u->Global`u,v->Global`v,g->Global`g,con->Global`con}];*)
		If[pri>10, Print["Before cl"]];		
        clnum = CollectVN@CoefficientList[Numerator[term], x];
        reps = Join[
          Join @@ Table[
            cl = CollectVN@CoefficientList[squares[[i]], x];
            {a[i] -> cl[[3]], b[i] -> cl[[2]], c[i] -> cl[[1]]}, {i, Length[squares]}], 
          Join @@ Table[
            cl = CollectVN@CoefficientList[lins[[i]], x];
            {u[i] -> cl[[2]], 
            v[i] -> cl[[1]]}, {i, Length[lins]}], 
          Table[g[i - 1] -> clnum[[i]], {i, Length[clnum]}]
          ];
		(*Put[reps/.{a->Global`a,b->Global`b,c->Global`cc,u->Global`u,v->Global`v,g->Global`g,con->Global`con},"~/Downloads/reps.txt"];
        Put[const/.{a->Global`a,b->Global`b,c->Global`cc,u->Global`u,v->Global`v,g->Global`g,con->Global`con},"~/Downloads/const.txt"];
        Put[squarestable/.{a->Global`a,b->Global`b,c->Global`cc,u->Global`u,v->Global`v,g->Global`g,con->Global`con},"~/Downloads/squarestable.txt"];*)
		If[pri>10, Print["After cl"]];        
        res = Join[linstable, squarestable] /. reps /. con -> const;
        If[pri>2,Print["res"];Print[res]];

        res = MyCancel/@res;
        If[Length[squares]>0,
        	res=Append[res,MyFactor[term-Total[res]]];
        	If[Exponent[Denominator[res[[-1]]],x]!=2,
        		 Print["Apart error. Quadratic term wrong shape"];
        		 Print[res[[-1]]]
        	];
        ];
        If[pri>2,Print["Canceled"]];
        If[pri>10,Print[res]];
        
        If[ ! PossibleZeroQ[Total[res] - term],
            Print["Apart test failed"];
            Abort[]
        ];
        res
    ]

CollectVN[expr_]:=Module[{ns,vs},
	ns=Union@Cases[expr,n[_],Infinity];
	vs=Union[vars,lsingvars];
	If[Length[vs]==0,Return[expr]];
	If[Length[ns]==0,Return[MyCollect[expr,vs,MyFactor]]];
	MyCollect[expr,	ns, MyCollect[#,vs,MyFactor]&]
]

MyCollect[expr_, vars_, func_] := Module[{Ruler},
 FromCoefficientRules[CoefficientRules[expr, vars]/.Rule->Ruler/.Ruler[a_,b_]:>Rule[a,func[b]], vars]
]

MyCancel[term_] := Module[{num, den, ns, coeffs, factored, i, newnum, newden, bc, can},
	num = Numerator[term];
	den = Denominator[term];
	ns = Union[Cases[{term}, n[_], Infinity]];
	(*if not paramrized with n in the numerator use normal cancel routine*)
	If[!PossibleZeroQ[num/.n[_]:>0],Print["SetN[] not initialized or term not parametrized with n. Use normal cancel"];Return[Cancel[term]]];
	coeffs = Coefficient[num, #]&/@ns;
	bc=ByteCount/@coeffs;
	If[Max[bc]>10000000, Print["Cancel contains big terms: ",bc]];
	factored = Table[
		If[Max[bc]>10000000,Print["Cancel term ",i," of ",Length[coeffs]]];
		If[
			PossibleZeroQ[coeffs[[i]]]
			,
			0
			,
			can = TimeConstrained[Cancel[#], 10, TimeConstrained[Factor[#], 10, #]] &@ (coeffs[[i]]/den);
			MyFactor[Cancel[can]]
		]
		,
		{i,Length[coeffs]}
	];
	newden=PolynomialLCM@@(Denominator/@factored);
	newnum=Sum[ns[[i]]Numerator[factored[[i]]](newden/Denominator[factored[[i]]]),{i,Length[factored]}];
	newnum/newden
]

ConvertQuadratic[term_,x_,vars_]:=Module[{den, y, fac, cl, a, b, c, d, trans, al, sqr, newy},
	den= Denominator[term];
	sqr=Cases[ProductToList[den], sqrt[_]];
	If[Length[sqr]>1, Print["Too many sqrts in convert quadratic"]; Abort[]];
	If[Length[sqr]==0, sqr=1, sqr=sqr[[1]]];
	den=den/.sqrt[_]:>1;
	If[Exponent[den,x]==1,Return[{term}]];
	fac=Cases[ProductToList[den],_?(!FreeQ[#,x]&)];
	If[Length[fac]==0&&FreeQ[sqr,x], Print["Convert quadratic discovered double pole"]; Print[term]; Abort[]];
	If[Length[fac]==0, Return[{term}]];
	If[Length[fac]>1,Print["Convert quadratic failed. More than two factors"]; Print[term];Print[x];Abort[], fac=fac[[1]]];
	If[Exponent[fac,x]!=2,Print["Convert quadratic failed"]; Print[term];Print[x];Abort[]];
	cl=CoefficientList[fac,x];
	(*Print[cl];*)
	y=Cases[vars,_?((Exponent[cl[[1]],#]==1&&FreeQ[cl[[2;;]],#])&)];
	(*If[Length[y]==0&&!FreeQ[sqr,x], Print["Convert quadratic failed. No linear variable"]; Print[term]; Print[x]; Abort[], *)
		If[Length[y]==0, Return[{term}], y=y[[1]]];
	(*];*)
	{a,b}=cl[[{3,2}]];
	{c,d}=CoefficientList[cl[[1]],y];
	newy=(b^2 - 4 a c - 4 a^2 y^2)/(4 a d);
	trans=y->newy;
	al=FactorCollect/@(D[newy,y] #/(sqr/.trans)&)/@ApartList[FactorCollect[term/.sqrt[_]:>1/.trans], x];
	If[Length[al]!=2, Print["Convert quadratic failed. Not two terms"]; Throw[Fail[term/.{sqrt->Sqrt,n[1]->1},vars],Fail]];
	al
]

FindTransformation[term_, vars_] :=
    Module[ {sqr, tra, sols, q, sol, i, v1, vothers, vothone, qs, ih, perms, pp, p, k, pmax},
    	If[pri>1,Print["Find Transformation"]];        
    	If[pri>1,Print[FindTransformationn[term, vars]]]; 
        If[ Length[vars] < 2,
            Print["No transformation. Only one variable"];
            Throw[UnsolvedTerm[term/.{sqrt->Sqrt,n[1]->1},vars],UnsolvedTerm];
        ];
        sqr = Cases[term, sqrt[_]^(-1), Infinity];
        (*Print[sqr];*)
        If[ Length[sqr] != 1,
            Print["No transformation. No square root"];
            Throw[Fail[term/.{sqrt->Sqrt,n[1]->1},vars]];
            ,
            sqr = 1/sqr[[1]]/.sqrt[u_]:>u;
        ];
        If[pri>2,Print["sqr"];
        Print[sqr]];
        pmax= 3;
        Do[
        	v1 = vars[[h]];
        	vothone= ReplacePart[vars,h->1];
        	If[pri>1,Print[vothone]];
        	vothers = Delete[vars,h];
        	If[pri>1,Print[vothers]];
        	If[pri>1,Print["p: ",p]];
        	perms=Union@@(Table[Permutations[pp],
        		{pp,
        			{ConstantArray[0,Length[vothers]], UnitVector[Length[vothers],1],If[Length[vothers]>=2,
        				 UnitVector[Length[vothers],1]+UnitVector[Length[vothers],2], UnitVector[Length[vothers],1]],
        				 2UnitVector[Length[vothers],1]}}][[1;;p+1]]);
        	If[pri>1,Print["perms"]];
        	If[pri>1,Print[perms]];
        	
        	tra = v1 -> v1+Sum[q@@pp Times@@(vothers^pp)/vothone[[k]],{pp,perms}];
        	If[pri>1,Print["tra"]];
        	If[pri>1,Print[tra]];
        	(*Print[perms];
        	Print[tra];*)
        	  (*vars[[1]] + q[1] vars[[2]] + q[2] vars[[2]]^2;*)
        	qs = Cases[tra,q[__],Infinity];
        	(*Print[qs];
        	Print[Length[CoefficientList[Numerator[Together[sqr /. tra]], v1]]];*)
        	sols = Table[Quiet[Solve[CoefficientList[Numerator[Together[sqr /. tra]], vs][[4 ;;]] == 0, qs]], {vs, Table[Prepend[Delete[vars, i], vars[[i]]], {i, Length[vars]}]}];
        	(*Print[Table[Solver[CoefficientList[Numerator[Together[sqr /. tra]], vs][[4 ;;]] == 0, qs], {vs, Table[Prepend[Delete[vars, i], vars[[i]]], {i, Length[vars]}]}]];*)
        	If[ Max[Length /@ sols] > 0, Break[] ];
        	If[ h==Length[vars] && k==Length[vars] && p==pmax, Print["No transformation found."]; 
        		Throw[UnsolvedTerm[term/.{sqrt->Sqrt,n[1]->1},vars],UnsolvedTerm]; ];
        	,
        	{p,pmax},{h,Length[vars]},{k,Length[vars]}
        	
        ];
        sol = tra /. Cases[sols, s_ /; Length[s] >= 1][[1]]/.q[__]->0;
        If[pri>1, Print["Found transformation"]];
        If[pri>3,Print[tra]];
        If[pri>3, Print[sol]];
        FactorCollect[term /. sol]
    ]

FindSimplestVariable[term_, vars_] :=
    Module[ {P, Q, S, den, exps, expS, Qlist, points, i, j, h, effexps, cl},
        P = Numerator[term];
        den = Denominator[term];
        S = Cases[ProductToList[den], sqrt[_]];
        If[ Length[S] > 1,
            Print["Too many sqrts"],
            If[ Length[S] == 1,
                S = S[[1, 1]],
                S = 1
            ]
        ];
        Q = den/sqrt[S];
        Qlist = ProductToList[Q];
        exps = Table[
          Exponent[Qlist[[i]], vars[[j]]], {j, Length[vars]}, {i, 
           Length[Qlist]}];
        effexps = Table[If[exps[[i,j]]==2&&
        	(cl=CoefficientList[Qlist[[j]],vars[[i]] ]; 
        	Or@@Table[FreeQ[cl[[2;;]],vars[[h]]]&&Exponent[cl[[1]], vars[[h]]]==1,{h,Length[vars]}])
        	,
        	1
        	,
        	exps[[i,j]]],
        		{i,Length[vars]},{j,Length[Qlist]}
        ];  
        expS = Table[Exponent[S, vars[[j]]], {j, Length[vars]}];
        points = Table[Count[exps[[i]], 1] + 10 Count[exps[[i]], 2] + 90 Count[effexps[[i]],2] + 
           100000*Count[Append[exps[[i]], expS[[i]]], _?(# > 2 &)] + 
           expS[[i]] + expS[[i]]*Count[effexps[[i]], _?(# > 1 &)]*If[Length[vars]==1,1000,100000], {i, 
           Length[vars]}];
        points
    ]

FindDoublePoles[term_, vars_, n_] :=
    Module[ {P, Pn, Q, S, den, dp, x, return, mflQ, mflS, inter, vs, cl,xx, num},
        num=ProductToList[Numerator[term]];

        (*part of the numerator that depens on n, and must not depend on square roots*)        
        P = Times@@Cases[num,a_/;!FreeQ[a,n]];
        (*general prefactor of the numerator that may contain square root factors*)
        Pn= Times@@Cases[num,a_/;FreeQ[a,n]];

        den = Denominator[term];
        S = Cases[ProductToList[den], sqrt[_]];
        If[ Length[S] > 1,
            Print["Too many sqrts"],
            If[ Length[S] == 1,
                S = S[[1, 1]],
                S = 1
            ]
        ];
        Q = den/sqrt[S];
        return = 
         Do[If[ 2 Exponent[P*Pn/.sqrt[a_]:>v^(Exponent[a,v]/2)sqrt[a], v] + 2 > 2 Exponent[Q, v] + Exponent[S, v],
                Return[DoublePole[
                  GetRule[CoefficientList[P, v][[-1]], vars, n]]]
            ], {v, vars}];
        If[ return =!= Null,
            Return[return]
        ];
        return = 
         Do[If[ dp = 
            Cases[MyFactorList[Q^2 S], 
             {a_, p_} /; (p > 2 && ! FreeQ[a, x])];
                Length[dp] > 0,
                Return[DoublePole[
                  GetRule[PolynomialRemainder[P/.(sqrt[a_]:>(sqrt[a]/.x->xx)), dp[[1, 1]], x]/.xx->x, vars, n]]]
            ], {x,
            vars}];
        If[ return =!= Null,
            Return[return]
        ];
        DoublePole[{}]
        (*mflQ=MyFactorList[Q];
        mflS=MyFactorList[S];
        inter=DeleteCases[Intersection[mflQ,mflS],_?(FreeQ[#,Alternatives@@vars]&)];
        Print[inter];
        If[Length[inter]==0, Return[DoublePole[{}]]]; 
        vs = Cases[vars, _?(Exponent[inter[[1,1]],#]==1&)];
        If[Length[vs]==0, Print["Could not remove Double Pole"]; Print[term]; Print[vars]; Abort[], vs=vs[[1]]];
        cl = CoefficientList[inter[[1,1]],vs];
        FindDoublePoles[FactorCollect[2vs cl[[2]](term/.vs->(vs^2-cl[[1]])/cl[[2]])],vars,n]
       *)
    ]
(*
FindDoublePoles[term_, vars_, nn_] :=
    Module[ {P, Q, S, den, dp, x, return, mflQ, mflS, inter, vs, cl},
    	n=nn;
        P = Numerator[term];
        den = Denominator[term];
        S = Cases[ProductToList[den], sqrt[_]];
        If[ Length[S] > 1,
            Print["Too many sqrts"],
            If[ Length[S] == 1,
                S = S[[1, 1]],
                S = 1
            ]
        ];
        Q = den/sqrt[S];
        return = 
         Do[If[ 2 Exponent[P, v] + 2 > 2 Exponent[Q, v] + Exponent[S, v],
                Return[DoublePole[
                  GetRule[CoefficientList[P, v][[-1]], vars, n]]]
            ], {v, vars}];
        If[ return =!= Null,
            Return[return]
        ];
        return = 
         Do[If[ dp = 
            Cases[ProductToList[Q], 
             Power[a_, p_] /; (p > 1 && ! FreeQ[a, x])];
                Length[dp] > 0,
                Return[DoublePole[
                  GetRule[PolynomialRemainder[P, dp[[1, 1]], x], vars, n]]]
            ], {x,
            vars}];
        If[ return =!= Null,
            Return[return]
        ];
        mflQ=MyFactorList[Q];
        mflS=MyFactorList[S];
        inter=DeleteCases[Intersection[mflQ,mflS],_?(FreeQ[#,Alternatives@@vars]&)];
        If[Length[inter]==0, Return[DoublePole[{}]]]; 
        vs = Cases[vars, _?(Exponent[inter[[1,1]],#]==1&)];
        If[Length[vs]==0, Print["Could not remove Double Pole"]; Print[term]; Print[vars]; Abort[], vs=vs[[1]]];
        cl = CoefficientList[inter[[1,1]],vs];
        FindDoublePoles[FactorCollect[2vs cl[[2]](term/.vs->(vs^2-cl[[1]])/cl[[2]])],vars,n]
       
    ]
 *)
GetRule[term_, vars_, n_] :=
    Module[ {sol},
        sol = Quiet[
          Solve[CoefficientList[Numerator[Together[term]], vars] == 0, 
           Cases[term, n[_], Infinity]]];
        If[ Length[sol] != 1,
            Print["Error finding rule"];
            Print[term],
            sol[[1]]
        ]
    ]
   
SumToList[term_] := If[Head[term] === Plus, List @@ term, {term}] 
ProductToList[term_] := If[Head[term] === Times, List @@ term, {term}]

ExSquareRoot[term_, x_] := Module[{num, den, sqr, xt, cl, rep},
  (*Print[Exsquareroot[term,x]];*)
  If[pri>2,Print["ExSquareRoot"]];
  num = Numerator[term];
  den = ProductToList[Denominator[term]];
  If[(Exponent[num, x] > 0 && Exponent[Times@@den, x]==1 ) || (Exponent[num,x]>1) || Exponent[Times@@den,x]>2, Print["Wrong powers in ",x]; Abort[];];
  sqr = Cases[den, sqrt[_]];
  If[Length[sqr] != 1, Print["no sqrt"]; Print[ExxSquareRoot[term, x]]; Abort[], sqr = sqr[[1]]];
  If[! MatchQ[Exponent[sqr[[1]], x], 1 | 2], 
   Print["Not quadratic in square root"]];
  If[Exponent[Times@@den,x]==2, 
     ret=ExSquareRootQuad2[term,x];
     If[!FreeQ[ret,x], Return[Failed[]]];
     Return[ret];
  ];
  xt = DeleteCases[Cases[den, _?(! FreeQ[#, x] &)], sqrt[_]];
  If[Length[xt] == 0 && Exponent[sqr[[1]], x] == 2, 
   Return[FactorCollect/@{(term/.sqrt[_]:>1)/sqrt[Coefficient[sqr[[1]],x^2]]}]];
  If[Length[xt] != 1, Print["no single term"], xt = xt[[1]]];
  If[Exponent[xt, x] != 1, Print["Wrong Exponent in term"]; Abort[]];
  cl = CoefficientList[xt, x];
  rep = x -> -cl[[1]]/cl[[2]];
  FactorCollect/@{num/((Times @@ DeleteCases[den, xt])*cl[[2]]) /. rep}
]

SimplifyNestedRoot[term_]:=Module[{rad,sq,a,b,c,num,den,bcon,bpol,bfac,ecands,f,res,ter,denext},
	rad=Factor[term^2/.sqrt[a_]^2:>a//.sqrt[a_]:>sqrt[MyFactor[a]]//.sqrt[a_^i_ b_]/;i<0:>sqrt[a^(i+2)*b]/a];
		(*//.sqrt[a_]^i_/;i>1\[RuleDelayed]a sqrt[a]^(i-2)//.sqrt[a_]^i_/;i<0\[RuleDelayed]1/a sqrt[a]^(i+2)//Factor);*)
		(*//.sqrt[a_]^(-1)\[RuleDelayed]sqrt[a]/a//Expand)/.sqrt[a_;*)
	(*Return[rad];
	ter=term//.sqrt[u_]:>PowerExpand[Sqrt[u]];

	rad=ter^2;*)
	{num,den}={Collect[Numerator[rad],_sqrt,Factor],Denominator[rad]};
	denext=Times@@Power@@@Replace[MyFactorList[den],{a_,b_}:>{a,Mod[b,2]},{1}];
	{num,den}={Collect[denext*num,_sqrt,Factor],den*denext};
	sq=Union@Cases[num,sqrt[_],All];
	If[Length[sq]!=1,Return[{}]];
	sq=sq[[1]];
	{a,b,c}={num/.sq->0,Factor[Coefficient[num,sq]],Replace[sq,sqrt[a_]:>a]};
	{bcon,bpol}=FactorTermsList[b];
	If[Mod[bcon,2]!=0,Return[{}],bcon=bcon/2];
	bfac=DeleteCases[Join@@Replace[Join[FactorInteger[bcon],FactorList[bpol]],{a_,i_}:>ConstantArray[a,i],{1}],1];
	ecands=Times@@@Union[Subsets[bfac]];
	res=Table[f=b/(2e);If[Expand[e^2+2 e f sqrt[c]+f^2 c-num]===0,(e+f sqrt[c])/PowerExpand[Sqrt[den]],Nothing],{e,ecands}];
	Do[If[!PossibleZeroQ[PowerExpand[term^2-res[[i]]^2/.sqrt->Sqrt]],Print["Error in simplify nested roots"];Print[term];Print[res[[i]]];Abort[]],{i,Length[res]}];
	res/.Power[a_,1/2]:>sqrt[a]
]

ExSquareRootQuad2[term_,x_]:= Module[{shift, rad, cl,dnsq,numx,tsh,res,sn},
	cl=CoefficientList[Denominator[term]/.sqrt[_]:>1,x];
	{shift,rad}={cl[[2]]/(2cl[[3]]),(cl[[2]]^2-4cl[[1]]cl[[3]])/(4cl[[3]]^2)}//Factor;
	tsh=term/.x->x-shift//FactorCollect;
	dnsq=Denominator[tsh]/.sqrt[_]:>1;
	
	res=Simplify@PowerExpand@FullSimplify[{(tsh/.sqrt[a_]:>(sn=SimplifyNestedRoot[sqrt[a/.x->sqrt[rad]]];
		If[Length[sn]>0,sn[[1]],sqrt[a/.x->sqrt[rad]]]))*dnsq/(CoefficientList[dnsq,x][[3]]sqrt[rad])/.x->sqrt[rad],
		(tsh/.sqrt[a_]:>(sn=SimplifyNestedRoot[sqrt[a/.x->-sqrt[rad]]];
		If[Length[sn]>0,sn[[1]],sqrt[a/.x->-sqrt[rad]]]))*dnsq/(-CoefficientList[dnsq,x][[3]]sqrt[rad])/.x->-sqrt[rad]}/.sqrt->Sqrt]
	
]

ExSquareRootQuad[term_,x_]:= Module[{shift, rad, cl,dnsq,numx,tsh,res},
	cl=CoefficientList[Denominator[term]/.sqrt[_]:>1,x];
	{shift,rad}={cl[[2]]/(2cl[[3]]),(cl[[2]]^2-4cl[[1]]cl[[3]])/(4cl[[3]]^2)}//Factor;
	tsh=term/.x->x-shift//FactorCollect;
	dnsq=Denominator[tsh]/.sqrt[_]:>1;

	numx=Cases[ProductToList[Numerator[tsh]],a_/;!FreeQ[a,x]];

	If[Length[numx]==0,numx=1,If[Length[numx]==1,numx=numx[[1]],Print["Error in ExSquareRootQuad"];Abort[]]];
	res={tsh*dnsq/(CoefficientList[dnsq,x][[3]]sqrt[rad])/.numx->sqrt[Expand[numx^2]]/.x^2->rad};
	Print[res];
	If[FreeQ[numx,n[_]],FactorCollect[res]/.x->Sqrt[rad],Failed[]]
]

ExSqrt[term_, x_] := Module[{num, den, prob, cl, c, d, s, n, sq, a, b},
	If[pri>4,Print["ExSqrt"]];
  	(*Print[Exsqrt[term,x]];*)
  	num = Numerator[term];
  	den = Denominator[term];
  	If[(Exponent[num, x] == 0 || Exponent[num,x] == 1/2) && Exponent[den, x] == 1, 
   		Return[{FactorCollect[(num/.x->(-(den/.x->0)/Coefficient[den,x]))/Coefficient[den, x]]}]];
  	If[Exponent[num, x] > 1 || Exponent[den, x] != 2, Print["Term not well shaped"]; Print[{term,x}];Abort[]];
  	prob = Cases[If[Head[den] =!= Times, {den}, List @@ den], _?(! FreeQ[#, x] &)];
  	If[Length[prob] == 1, prob = prob[[1]], Print["Too many den terms"]];
  	cl = CoefficientList[prob, x];
  	If[Length[cl] != 3, Print["not quadratic"]; Abort[]];
  		{d, s, n} = {-cl[[2]], sqrt[cl[[2]]^2 - 4 cl[[1]] cl[[3]]], 2 cl[[3]]};
  			{a, b, c} = {Coefficient[num, x], num /. x -> 0, den/prob};
  	sq = s /. sqrt[u_] :> u;
  	(*{-((a d+n b)s+a sq)/(2c sq),((a d+n b)s-a sq)/(2c sq)}*)
  	FactorCollect/@DeleteCases[{-((a d + n b))/(c s n), a/(c n)}, 0]
  ]


MatrixInverse[AA_] :=
    Module[ {B, A = AA, i, j, n = Length[AA], k, l, coeff, perm = {}},
        B = IdentityMatrix[n];
        For[i = 1, i <= n, i++, 
         For[j = 1, j <= n, j++, If[ A[[i, j]] =!= 0,
                                     Break[]
                                 ];];
         If[ j === n + 1,
             Print["Degenerate"];
             Return[Table[Table[0, {n}], {n}]];
         ];
         (*found non-zero*)
         AppendTo[perm, ReplacePart[Table[0, {n}], j -> 1]];
         (*Print[j];*)
         coeff = 1/A[[i, j]];
         For[l = 1, l <= n, l++, A[[i, l]] *= coeff;
                                 B[[i, l]] *= coeff;];
         For[k = 1, k <= n, k++, 
          If[ k =!= i,(*substrating next rows*)
              If[ A[[k, j]] =!= 0,(*coeff=A[[k,j]]/A[[i,j]];*)
                  coeff = A[[k, j]];
                  For[l = 1, l <= n, l++, A[[k, l]] -= A[[i, l]]*coeff;
                                          B[[k, l]] -= B[[i, l]]*coeff;
                                          A[[k, l]] = Together[A[[k, l]]];
                                          B[[k, l]] = Together[B[[k, l]]];];
              ]
          ] (*if*)](*for k*)];(*for i*)
        Return[Inverse[perm].B];
    ]




SortDlogs[dlogs_, orderedlist_] := 
 Module[{U,i}, 
  SortBy[dlogs, 
   Prepend[Union@
       Cases[# /. 
         Table[orderedlist[[i]] -> U[i], {i, Length[orderedlist]}], 
        U[_], Infinity], U[0]][[-1, 1]] &]
]

GetSimplifiedDlogList3[dloglist_]:= Module[{gs,orderedlist},
	gs=Cases[dloglist,Global`G[_,List[__]],All]//Union;
	If[Length[gs]==0,Print["No integrals found of the form G[_,List[__]]"];Abort[]];
	orderedlist=SortBy[gs,Count[#[[2]],_?Positive]*1000-Total[Cases[#[[2]],_?Negative]]&];
	GetSimplifiedDlogList3[dloglist,orderedlist]
]

GetSimplifiedDlogList3[dloglist_, orderedlist_] := 
 Module[{p, clist, c, gl, sc, g, revlist, ph, ch,H,ig,i,cll,cc,gtopos,max,sign,Q},	
	revlist = Reverse[orderedlist];
	H = Head[orderedlist[[1]]];
	clist = Collect[dloglist,_H,Factor];
	Do[
		g = revlist[[ig]];
		p = Flatten@Position[clist,	a_ /; (! FreeQ[a, g] &&  FreeQ[a, Alternatives @@ (revlist[[;; ig - 1]])]), {1}];
		If[Length[p] == 0, Continue[]];
		c = Table[Coefficient[clist[[i]], g], {i, p}];
		gl = GetLinsOrd[c];
		clist[[p]] = 
		Collect[ 
			clist[[p]] - ReplacePart[ConstantArray[1, Length[c]], ({#} & /@ gl[[1]]) -> 0]
				*(gl[[2]].clist[[p]][[gl[[1]]]]), H[__], Factor
		];
		cll = cc /@ Range[Length[dloglist]];

		p = Flatten@Position[clist, a_ /; (! FreeQ[a, g] && FreeQ[a, Alternatives @@ (revlist[[;; ig - 1]])]), {1}];
		Do[
			c = Table[Coefficient[clist[[i]], g], {i, p}];
			sc = FindSimpleCombination[Prepend[Delete[c, i], c[[i]]]];
			sc = Insert[Delete[sc, 1], sc[[1]], i];
			clist[[p[[i]]]] = Collect[clist[[p]].sc, H[__], Factor];
			c = Table[Coefficient[clist[[i]], g], {i, p}];
			,
			{i, Length[p]}
		];
		ph = Flatten@Position[clist, a_ /; (!FreeQ[a, g] && !FreeQ[a, Alternatives @@ (revlist[[;; ig - 1]])]), {1}];
		If[Length[ph] == 0, Continue[]];
		(*Print["clist"];
		Print[clist];
		Print["ch"];
		Print[ch];
		Print["g"];
		Print[g];
		Abort[];*)
		ch = Table[Coefficient[clist[[i]], g], {i, ph}];
		Do[
			gl = GetLinsTiz[Append[c, ch[[i]]]];
			If[Length[gl[[1]]] < Length[c] + 1,
				If[gl[[1]] =!= Range[Length[c]], 
					Print["Error in GetSimplifiedList3"];
					Print[Append[c,ch[[i]]]];
				];
				clist[[ph[[i]]]] = Collect[clist[[ph[[i]]]] - clist[[p]].gl[[2, -1]], H[__], Factor];
				,
				sc = FindSimpleCombination[Prepend[c, ch[[i]]]];
				clist[[ph[[i]]]] = Collect[Prepend[clist[[p]], clist[[ph[[i]]]]].sc, H[__], Factor];
			];
			,
			{i, Length[ph]}
		]
		,
		{ig, Length[orderedlist]}
   ];
   gtopos=Table[orderedlist[[i]]->Q[i],{i,Length[orderedlist]}];
   clist=DeleteCases[clist,0];
   clist=SortBy[clist,(Union@Cases[#/.gtopos,_Q,All])[[-1,1]]&];
   Table[
      max=(Union@Cases[clist[[i]]/.gtopos,_Q,All])[[-1,1]];
      sign=Sign[FactorTermsList[Coefficient[clist[[i]],orderedlist[[max]]]][[1]]];
      Collect[sign*clist[[i]]/(GCD@@(FactorTermsList[#][[1]]&/@SumToList[clist[[i]]])),Head[orderedlist[[1]]][__],Factor]
      ,{i,Length[clist]}
    ]
]

FindSimpleCombination[terms_List, ilimit_: (-1)] := 
 Module[{vecs, vterms, index, limit, zeropos},
  If[ilimit < 0, limit = Max[7 - Length[terms], 1], limit = ilimit];
  vecs = (# + 
       Prepend[ConstantArray[-limit, Length[terms] - 1], 
        1]) & /@ (IntegerDigits[#, 2*limit + 1, Length[terms]] & /@ 
      Range[0, limit*(2*limit + 1)^(Length[terms] - 1) - 1]);
  vterms = {#[[1]], Factor[#[[2]]]} & /@ 
    FactorTermsList /@ (vecs.terms);
  If[Length[(zeropos = Position[vterms[[All, 2]], 0])] > 0, 
   Return[vecs[[zeropos[[1, 1]]]]]];
  index = 
   Ordering[(100 ByteCount[vterms[[#, 2]]] + 
         Total[Abs[vecs[[#]]]]) & /@ (Range[Length[vterms]])][[1]];
  vecs[[index]]/vterms[[index, 1]]
  ]
  
  


ReplaceKinematics[]:=replacements



LinIndep[list_List]:=Module[{gl},
	gl=GetLinsOrd[list];
	list[[gl[[1]]]]
]


(*Begin of extra function 
**************************************
**************************************
**************************************
**************************************
**************************************
**************************************
**************************************
**************************************
**************************************
**************************************)


NewParametrization[newvars_,expr_]/;spinorhelicity:=Module[{repl, jacob, i, j},
	
	repl=Solve[ToSpinorHelicity[expr]==newvars,spinorhelicityvars];
	jacob = Det[Table[D[ToSpinorHelicity[expr[[i]]],spinorhelicityvars[[j]]],{i,Length[expr]},{j,Length[spinorhelicityvars]}]]/.repl[[1]]//Factor;
	Print[jacob/spinorhelicityjac];
	SetParametrization[newvars, (ToSpinorHelicity[propagators]/.repl[[1]])==propagators, spinorhelicityjac/jacob];
]

VectorSolution[expr_, v_]:=Module[{},
	ToSpinorHelicity[v]/.Solve[ToSpinorHelicity[expr]==0,Cases[Variables[ToSpinorHelicity[v]],q_/;MemberQ[spinorhelicityvars,q]]]
]

GetInfo[]:={initialized,spinorhelicity, replacements, massless};

Sps[]/;initialized:=Union@Cases[ExpandVectors[propagators,Join[internal,external]],Dot[a_,b_]/;(MemberQ[internal,a]||MemberQ[internal,b]),All]

SpsToP[]/;initialized:=Module[{},
	sps=Sps[];
	If[Length[sps]!=Length[propagators],Print["missmatch length of propagators and scalar products. sps: ",sps, " propagators: ",propagators]];
	Solve[ExpandVectors[propagators,Join[internal,external]]==Global`P/@Range[Length[propagators]],sps][[1]]
]

BaikovParametrization[Internal_List, vars_, ps_]:=Module[{vs, dets, h, i, j, pp, a, props, sols, dens, repl},
	SpinorHelicity[Internal, a, ps];
	If[Head[ps[[1]]]===List, pp=ps, pp=ps&/@Range[Length[Internal]]];
	props = Table[{(Internal[[i]])^2,(Internal[[i]]+pp[[i,1]])^2, (Internal[[i]]+pp[[i,1]]+pp[[i,2]])^2, (Internal[[i]]+pp[[i,1]]+pp[[i,2]]+pp[[i,3]])^2},
		{i,1,Length[Internal]}];
	If[Head[vars]=!=List, vs = Table[vars[i,j],{i,1,Length[Internal]},{j,1,4}],
		vs = Table[If[Head[vars[[i]]]===List, vars[[i]], vars[[i]]/@Range[4]],{i,1,Length[Internal]}];
	];
	sols = Table[Solve[ToSpinorHelicity[props[[i, 1 ;; 4]]] == 0, {a[i,1],a[i,2],a[i,3],a[i,4]}][[1]],{i,Length[Internal]}];
	dens = Table[ToSpinorHelicity[(Internal[[i]]-(ToSpinorHelicity[Internal[[i]]]/.sols[[i]]))^2],{i,Length[Internal]}];
	repl = Flatten[Table[Solve[(ToSpinorHelicity[#]/dens[[i]]) & /@ 
   		props[[i, All]] == vs[[i,1;;4]],  {a[i,1],a[i,2],a[i,3],a[i,4]}],{i,1,Length[Internal]}]];
   	dets = Table[Factor[Det[Table[D[(a[h,i] /. repl), vs[[h,j]]], {i, 1, 4}, {j, 1, 4}]]],{h,Length[Internal]}];
   	{Flatten[vs], #==Factor[(ToSpinorHelicity[#]/.repl)]&/@propagators, Factor[(Times@@dets)*(spinorhelicityjac/.replacements)]}
	
]

Dott[pr_, pw_] := pr.pw /. BitOr[1, u] :> 1 /. -u :> 0 /. u -> 1

Filter[ints_,  pwer_] := Module[{ss, i},
	(Cases[{#, 
       Length[Cases[
         Table[{Length[ss], 
           Dott[#[[
             2]], (BitOr[Sequence @@ Table[#[[i]], {i, ss}]] & /@ 
              pwer)]}, {ss, Subsets[Range[Length[internal]]][[2 ;;]]}], 
         q_ /; q[[1]]*2 >= q[[2]]]]} & /@ 
     Cases[ints, q_ /; Total[q[[2]]] >= 2 Length[internal]+1], q_ /; q[[2]] === 0])[[All, 1]]
]




GetMaximalAnsatzOld[G_[ind_, {q__}/;Length[{q}]==Length[propagators]]]/;initialized :=
    Module[ {pwer},
    pwer = GetPowers[];
    ExtendMaximal[G[ind,{q}],pwer]
];



GetPowers[]/;initialized:=Module[{i,j,cores,pw1,pw2},
	If[powers==={},
		cores=GetCores[];
		pw1=Table[If[FreeQ[propagators[[i]],internal[[j]]],0,1],{i,1,Length[propagators]},{j,1,Length[internal]}];
		pw2=Table[If[FreeQ[cores[[i]],internal[[j]]],0,1],{i,1,Length[propagators]},{j,1,Length[internal]}];
		powers=pw2+(pw1-pw2)*Global`u;
		
	];
	powers	
]



IterativeSolve[p_List, vars_] := Module[{F},
  SortBy[Flatten[
     Apply[F, IterativeSolve[p, vars, {}], {Length[p]}]] /. F -> List,
    Length]
  ]

IterativeSolve[p_List, vars_, sols_] := Module[{sol, np, i},
  If[Length[p] == 0, Return[sols]];
  sol = Quiet[Solve[p[[1]] == 0, vars]];
  np = Factor[p /. sol];
  Quiet[DeleteCases[Table[IterativeSolve[Delete[Factor[p /. sol[[i]]], 1], vars, Join[Factor[sols /. sol[[i]]], Factor[sol[[i]]]]], 
  	{i, Length[sol]}], _?(!FreeQ[#,Indeterminate|ComplexInfinity|Factor]&)]]
  
]



Leadsing[int_, dl_, vars_] := Module[{vslist, vs, ls, i},
  vslist = Union[Cases[{#}, Alternatives @@ vars, Infinity]] & /@ dl;
  vs = Table[
    Complement[vslist[[i]], Union @@ vslist[[1 ;; i - 1]]], {i, 
     Length[dl]}];
  Print[vs];
  If[Length /@ vs =!= ConstantArray[1, Length[dl]], 
   Print["Variables inconsistent"]; Abort[]];
  vs = Flatten[vs];
  ls = int;
  Do[Print[i]; 
   ls = FactorCollect[
      FactorCollect[ls dl[[i]]/Coefficient[dl[[i]], vs[[i]]]] /. 
       Solve[dl[[i]] == 0, vs[[i]]]][[1]], {i, 
    Reverse[Range[Length[vs]]]}];
  (*Do[ls=FactorCollect[Residue[ls,{vs[[i]],Solve[dl[[i]]\[Equal]0,
  vs[[i]]][[1,1,2]]}]],{i,Reverse[Range[Length[vs]]]}];*)
  ls
  ]



ComputeCut[cut_,shift_]:=Module[{propsp,sol,cutinds, props, det, vs, i,j,k, cutsol},
	If[MemberQ[cuts[[All,1]],cut], Return[cut/.cuts]];
	If[pri>-1, PrintTemporary["Compute cut ",cut]];
	If[Head[cut]=!=List, Print["cut must be a list"]; Abort[]];
	If[Length[cut]!=Length[propagators], Print["Length of cut must be the same as length of propagators"]; Abort[]];
	If[Union[cut]=!={0,1}, Print["Cut must only contain elements 0 and 1"]; Abort[]];
	propsp=Parametrize/@(propagators/.shift)//Factor;
	cutinds=PositionIndex[cut][1];
	sol=Cases[Quiet[IterativeSolve[propsp[[cutinds]],vars]],_?(Length[#]==Count[cut,1]&)];
	(*Print[IterativveSolve[propsp[[cutinds]],vars]];
	Print[sol];*)	
	If[Length[sol]==0, Print["No solution for this cut"]; Abort[]];
	If[Length[sol[[1]]]!=Count[cut,1], Print["Cut solution not well shaped"]; Abort[]];
	cutsol=Table[
		vs=sol[[i,All,1]];
		props=Factor[propsp/.sol[[i]]];
		det=Factor[Det[Table[D[propsp[[j]],vs[[k]]],{j,cutinds},{k,Length[vs]}]]/.sol[[i]]];
		{Complement[vars,vs], props, jac/det/.sol[[i]]}
		,
		{i,Length[sol]}
	];
	cuts=Append[cuts,cut->cutsol];
	cutsol
	(*DeleteCases[Table[vs = sol[[h,All,1]]; propscut=Factor/@(propsp/.sol[[h]]);
	det = Det[Table[D[propsp[[i]],vs[[j]]],{i,cutinds},{j,Length[vs]}]]/.sol[[h]]//Factor;*)	
]

ComputeCut[cut_]:=ComputeCut[cut,{}];

GtoFunctionOld[g_List, nn_, cut_List]/;initialized&&parametrized := 
Module[{maxa, i, j, h, func, glist, grels, gn, propsp, cutinds, sol, vs, propscut, det, pp, ii, den, gs},
	If[Length[Cases[cut,0|1]]!=Length[propagators], Print["cut has wrong shape."]];
	n=nn;
	If[Length[cut]!=Length[propagators], Print["cut must be a list with length of the number of propagators"]; Abort[];];
	If[Length[g]==0, Return[0]];
	glist=Union[Cases[g,Global`G[__],Infinity]];
	grels=Cases[glist, Global`G[_,ind_]/;Max[ind-cut]>=0];
	gn=g/.Global`G[_,ind_]/;Max[ind-cut]<0:>0;
	grels=DeleteCases[gn,0];
	gs = Cases[{g},Global`G[__],Infinity]//Union;
	(*Print[Length[gs]];*)
	maxa= Table[Max[Table[gs[[i,2,j]],{i,1,Length[gs]}]],{j,1,Length[propagators]}];
	(*Print[maxa];*)
	propsp=Factor/@Parametrize/@propagators;
	cutinds = Flatten[Position[cut,1]];
	maxa[[cutinds]]=ConstantArray[1,Length[cutinds]];
	maxa=If[#<0,0,#]&/@maxa;
	
	sol=Quiet[IterativeSolve[propsp[[cutinds]],vars]];
	If[Length[sol]==0, Print["No solution for this cut"]; Abort[]];
	If[Length[sol[[1]]]!=Count[cut,1], Print["Cut solution not well shaped"]; Abort[]];
	DeleteCases[
		Table[
			vs = sol[[h,All,1]];
			propscut=Factor/@(propsp/.sol[[h]]);
			det = Det[Table[D[propsp[[i]],vs[[j]]],{i,cutinds},{j,Length[vs]}]]/.sol[[h]]//Factor;
			den=Times@@Table[If[(maxa-cut)[[i]]==0,1,propscut[[i]]^(maxa-cut)[[i]]],{i,Length[propscut]}];
			If[den==0, Print["Infinity in Cut"]; Print[den]; Return[]];
			func = 
				Collect[((n/@Range[Length[g]]).(g/.Global`G[_,ind_]:>
					Times@@Table[
						pp=propscut[[i]];
						ii=(-ind+maxa)[[i]];
						If[pp=!=0,pp^ii, If[ii<0, Print["infinity in cut"]; Abort[];, If[ii==0, 1, 0]]]
						,
						{i,Length[propscut]}
					]
					(*If[Max[(ind-cut)[[zeros]]>=1, Print["infinity in cut"]; Abort[], If[ind-cut *)
					(*Times@@(propscut^(-ind+maxa))*) 
				)),n[_],Factor]/den*jac/det;
			(*func*)
			FactorCollect[func]
			,
			{h,Count[Length/@sol,Length[sol[[1]]]]}
		]
		,
		Return[]
	]
]

GetCutSolutions[] := cuts;

SetCutSolutions[newcuts_] := cuts = newcuts;


GtoFunction[g_List, nn_, cut_List]/;initialized&&parametrized := 
Module[{maxa, i, j, h, func, glist, grels, gn, propsp, cutinds, vs, propscut, cutjac, pp, ii, den, gs, cutsol},

	If[Length[Cases[cut,0|1]]!=Length[propagators], Print["cut has wrong shape."]];
	n=nn;
	If[Length[cut]!=Length[propagators], Print["cut must be a list with length of the number of propagators"]; Abort[];];
	If[Length[g]==0, Return[0]];
	glist=Union[Cases[g,Global`G[__],Infinity]];
	grels=Cases[glist, Global`G[_,ind_]/;Max[ind-cut]>=0];
	gn=g/.Global`G[_,ind_]/;Max[ind-cut]<0:>0;
	grels=DeleteCases[gn,0];
	gs = Cases[{g},Global`G[__],Infinity]//Union;
	(*Print[Length[gs]];*)
	maxa= Table[Max[Table[gs[[i,2,j]],{i,1,Length[gs]}]],{j,1,Length[propagators]}];
	(*Print[maxa];*)
	propsp=Factor/@Parametrize/@propagators;
	cutinds = Flatten[Position[cut,1]];
	maxa[[cutinds]]=ConstantArray[1,Length[cutinds]];
	maxa=If[#<0,0,#]&/@maxa;
	cutsol=ComputeCut[cut];
	DeleteCases[
		Table[
			vs = cutsol[[h,1]];
			propscut=cutsol[[h,2]];
			cutjac=cutsol[[h,3]];
			den=Times@@Table[If[(maxa-cut)[[i]]==0,1,propscut[[i]]^(maxa-cut)[[i]]],{i,Length[propscut]}];
			If[den==0, Print["Infinity in Cut"]; Print[den]; Return[]];
			func = 
				Collect[((n/@Range[Length[g]]).(g/.Global`G[_,ind_]:>
					Times@@Table[
						pp=propscut[[i]];
						ii=(-ind+maxa)[[i]];
						If[pp=!=0,pp^ii, If[ii<0, Print["infinity in cut"]; Abort[];, If[ii==0, 1, 0]]]
						,
						{i,Length[propscut]}
					]
					(*If[Max[(ind-cut)[[zeros]]>=1, Print["infinity in cut"]; Abort[], If[ind-cut *)
					(*Times@@(propscut^(-ind+maxa))*) 
				)),n[_],Factor]/den*cutjac;
			(*func*)
			FactorCollect[func]
			,
			{h,Length[cutsol]}
		]
		,
		Return[]
	]
]



GtermToFunction[term_]/;initialized:=Module[{gs, glist, n, i},
	gs = DeleteDuplicates[Cases[{term},Global`G[__],Infinity]];
	(*Print[gs];*)
	If[(term/.Dispatch[(#->0)&/@gs])=!=0, Print["Wrong terms found"]; Abort[]];
	glist = GtoFunction[gs, n];
	glist /. Dispatch[Table[n[i]->Coefficient[term,gs[[i]]],{i,Length[gs]}]] 
]

GtermToFunction[term_]/;!initialized:=(Print["Initalize first"];Failed[])


DlogBasis[g_List]/;initialized :=Module[{func, lsings, n},
	(*n=Global`n;*)
	func=GtoFunction[g,n];
	lsings=LeadingSingularities[func,IntegrandVariables[],n,Length[g]];
	GenerateDlogbasis[g, lsings, n]	
]

DlogBasisMixed[g_List]/;initialized := Module[{func, lsings, n},
	(*n=Global`n;*)
	func=GtoFunction[g,n];
	lsings=LeadingSingularities[func,IntegrandVariables[],n,Length[g]];
	GetDlogListMixed[g, lsings, n]	
]


SetPowers[pwer_]:= powers=pwer;

FindSubTops[G_[_, a_]]/;initialized := Module[{perms, u},
  perms = 
   Join @@ Table[
     Permutations[
      Join[ConstantArray[1, i], 
       ConstantArray[0, Count[a, 1] - i]]], {i, 
      2 Length[internal] + 1, Count[a, 1]}];
  (G[1, u = ConstantArray[0, Length[propagators]]; 
      u[[Flatten[Position[a, 1, {1}]]]] = #; u]) & /@ perms
  ]




SetPropagatorIndices[inds_]:=Module[{}, Print["Wrong input Pattern. Use e.g. SetPropagatorIndices[{1,0,1,1,...}]"]; Null];
SetPropagatorIndices[G[_,inds_]]/;(MatchQ[inds,{__?IntegerQ}]&&Length[inds]==Length[propagators]) :=propagatorInds=inds;
SetPropagatorIndices[inds_]/;(MatchQ[inds,{__?IntegerQ}]&&Length[inds]==Length[propagators]) :=propagatorInds=inds;

GetFunc[num_] := Module[{}, Print["Call Initalialize[] and SetPropagatorIndices[{1,0,...}] first"]; Null];
GetFunc[num_]/;(initialized&&MatchQ[propagatorInds,{__?IntegerQ}]) := Parametrize[num]*jac/Times@@(Factor/@Parametrize/@(propagators^propagatorInds));
GetGFunc[num_]/;(initialized&&MatchQ[propagatorInds,{__?IntegerQ}]) := Module[{propExp,numExp,P,pp,sol,i,res,const, ig, prop,ext, int},
	ig=Global`G@@propagatorInds;
	ext=external;
	int=internal;
	prop=propagators;
	{propExp,numExp}=ExpandVectors[{prop,num},Join[ext,int]]/.Table[ext[[i]].ext[[i]]->0,{i,1,Length[ext]}]/.replacements;
	If[Length[ext]>2,{propExp,numExp}={propExp,numExp}/.replacements];
	sol=Quiet[Solve[propExp == P /@ Range[Length[propagators]], Variables[propExp]]];
	pp=Expand[numExp/.sol[[1]]]//.{P[a_]^n_:>P@@(a&/@Range[n]),P[a__]P[b__]:>P[a,b]};
	res=pp/.P[q__]:>Head[ig][1,List@@ig-Sum[UnitVector[Length[ig],P[q][[i]]],{i,1,Length[P[q]]}]];
	const=res/.Head[ig][__]:>0;
	res-const+const*Head[ig][1,List@@ig]
]

GtermToNumerator[term_]/;(initialized&&MatchQ[propagatorInds,{__?IntegerQ}]) := Module[{},
  term /. Global`G[_, a_] :> Times @@ (propagators^(propagatorInds - a))
  ]
  
  
TransformGs[gterm_, trafo_]/;(initialized&&MatchQ[propagatorInds,{__?IntegerQ}])  := 
 GetGFunc[GtermToNumerator[gterm] /. trafo]





GetSimplifiedDlogList[sol_]:=Module[{terms, lis},
	If[sol=={},Return[{}]];
	terms = Terms[sol];
	Collect[#,Global`G[_,_], Together]&/@
		(lis=SortBy[terms.# & /@ RowReduce[InTerms[#, terms] & /@ sol], 
  			Max[Cases[Variables[#], Global`G[_, a_] :> Count[a, _?Positive]]]+ByteCount[#]*10^(-16) &];lis)	
]

GetSimplifiedDlogList2[glist_List] := 
 Module[{gs, mat, gl, rels, nvs, zers, zerocount, thebest, i,j,k,eq,gli,gsj},
  gs = SortBy[Reverse[Union[Cases[glist, Global`G[__], Infinity]]], 
    Count[#[[2]], 1] 1000000 - 1000 Total[#[[2]]] &];
  mat = Table[Coefficient[gli, gsj], {gli, glist}, {gsj, gs}];

  gl = GetLinsOrd[mat[[All, 1]]];

  mat = Table[
    If[MemberQ[gl[[1]], i] || gl[[2, i]] === 0, mat[[i]], 
     Factor[mat[[i]] - gl[[2, i]].mat[[gl[[1]]]]]], {i, 
     Length[mat]}];

  Do[
   If[mat[[i, j]] === 0, Continue[]];
   gl = GetLinsTiz[Prepend[mat[[All, j]], mat[[i, j]]]];
   If[gl[[1, 1]] != 1, Print["Errroorr"]; Abort[]];
   rels = 
    Table[(*Print[k - 1, ": ", gl[[2, k, 1]], ": ", i];*) 
     If[k == i + 1 || gl[[2, k, 1]] == 0, 
      Nothing, (gl[[2, k]].(eq /@ gl[[1]]) - eq[k]) /. 
        eq[ind_] :> eq[ind - 1] /. eq[0] :> eq[i]], {k, 2, 
      Length[gl[[2]]]}];
   nvs = Factor[(rels /. eq[in_] :> mat[[in]])];
   zers = Flatten[Position[mat[[i, Range[j - 1]]], 0, {1}]];
   nvs = Cases[nvs, q_ /; q[[zers]] === 0 Range[Length[zers]]];
   If[Length[nvs] == 0, Continue[]];
   zerocount = Count[#, 0] & /@ nvs;
   thebest = nvs[[PositionIndex[zerocount][Max[zerocount]][[1]]]];
   If[Count[mat[[i]], 0] >= Max[zerocount], Continue[]];
   mat[[i]] = thebest;
   ,
   {j, 2, Length[mat[[1]]]}, {i, Length[mat]}
   ];
  mat.gs
  ]


GramDet[a_List]:=ExpandVectors[Det[Table[Dot[a[[i]],a[[j]]],{i,Length[a]},{j,Length[a]}]],a];

GramDet[a_List,b_List]:=ExpandVectors[Det[Table[Dot[a[[i]],b[[j]]],{i,Length[a]},{j,Length[a]}]],Join[a,b]];




ExtendAnsatz[G_[in_, a_], pwers_, ind_] := Module[{sig, min, i, u},
  u=Global`u;
  sig = (a.pwers /. (Times[q_ /; q < 0, u] :> 0) /. u -> 1) - (3 + 
      0*Range[Length[pwers[[ind]]]]);
  min = Min[
    Table[If[(pwers[[ind, i]] /. u -> 0) == 0, Infinity, 
      sig[[i]]/pwers[[ind, i]]], {i, 1, Length[pwers[[ind]]]}]];
  Table[G[in, a - UnitVector[Length[a], ind]*i], {i, 0, min}]
]

ExtendMaximal[g_, pwers_] := Module[{list},
  If[Head[g] =!= List, list = {g}, list = g];
  Do[list = Union @@ (ExtendAnsatz[#, pwers, i] & /@ list), {i, 1, 
    Length[pwers]}];
  list
]

Terms[expr_List] := Union @@ (Terms /@ expr);

Terms[expr_] := Module[{ex, list},
  ex = Expand[expr];
  list = If[Head[ex] === Plus, List @@ ex, {ex}];
  Sort[FactorTermsList[#][[2]] & /@ list]
  ]

InTerms[expr_, terms_List] := Module[{ex, list, p, ft, res, i},
  ex = Expand[expr];
  list = If[Head[ex] === Plus, List @@ ex, {ex}];
  res = Sum[ft = FactorTermsList[list[[i]]]; 
    p = Position[terms, ft[[2]]][[1, 1]]; 
    UnitVector[Length[terms], p]*ft[[1]], {i, 1, Length[list]}];
  If[Expand[res.terms - expr] =!= 0, Print["Wrong result in InTerms"]];
  res
]

GetCores[] := Module[{cores, vs, count},
	count=0;
	cores = ConstantArray[{}, Length[propagators]];
  	vs = Variables /@ (ExpandVectors[propagators, Join[internal, external]] /. {Dot[a_, b_] /; 
         MemberQ[external, a] && MemberQ[external, b] :> 0});
  	While[Length[Variables[vs]] > 0,
  		count++;
  		If[count>30,Print["GetCores error"];Print[cores];Abort[]];
   		cores[[Flatten[Position[vs, {a_}, {1}]]]] = vs[[Flatten[Position[vs, {a_}, {1}]], 1]];
   		vs = Variables /@ (vs /. (#[[1]] -> 0 & /@ (Cases[vs, {_}])));
   	];
  	cores
];

GetAllCuts[maxcut_, gmax_] := Module[{cuts, allcuts, subcuts},
  cuts = {maxcut};
  allcuts = cuts;
  Do[subcuts = Union @@ (GetSubcuts[#, gmax] & /@ cuts);
   If[Length[subcuts] == 0, Break[]];
   allcuts = Join[subcuts, allcuts];
   cuts = subcuts;
   ,
   {i, 7}];
  allcuts
  ]
  
  
DlogViaCuts[seed_, gmax_, maxcut_] := 
Module[{cuts, currentG, i, subcuts, k},
	cuts = GetSubcuts[maxcut, gmax];
  	currentG = seed;
  	Print[cuts];
  	Do[
		Print[i];
   		Print["L", Length[cuts]];
   		Do[
   			Print["cut ", k];
   			Print["Helllooooo!!!!!!!"]; 
   			Print[LssingCut[currentG, gmax, cuts[[k]], IntegrandVariables[]]];
    		currentG = LsingCut[currentG, gmax, cuts[[k]], IntegrandVariables[]][[1]]
    		,
    		{k, Length[cuts]}
       	];
   		subcuts = Union @@ (GetSubcuts[#, gmax] & /@ cuts);
   		Print["Subcuts"];
   		Print[subcuts];
   		If[Length[subcuts] == 0, Break[]];
   		cuts = subcuts;
   		,
   		{i, 5}
   	];
  	currentG
]  

DlogBasisViaCuts[G_[_, inds_]] := Module[{gmax, cuts, seeds, gmaxs, i, j},
  gmax = IntegrandAnsatz[G[1, inds]];
  cuts = GetAllCuts[inds, gmax];
  seeds = GetSeeds /@ cuts;
  gmaxs = IntegrandAnsatz[G[_, #]] & /@ cuts;
  Table[If[Length[seeds] == 0, {}, 
    DlogViaCuts[seeds[[i, j]], gmaxs[[i]], cuts[[i]]]], {i, 
    Length[seeds]}, {j, Length[seeds[[i]]]}]
  ]

GetSeeds[cut_] := Module[{ansatz, lsings},
  (*gmax = IntegrandAnsatz[Global`G[1, cut]];
  LsingCut[Global`G[1, cut], gmax, cut, IntegrandVariables[]]*)
  
  ansatz = DeleteCases[GetSimplifiedDlogList[IntegrandAnsatz[Global`G[1, cut]]/.Global`G[1,a_]/;Count[a,1]<Count[cut,1]:>0],0];
  If[Length[ansatz]==0,Return[{}]];	
  lsings = LsingCut[ansatz, cut,n];
  If[pri>0,Print["lsings ", Length/@lsings]];
  If[pri>0,Print["ansatz ", Length[ansatz]]];
  If[Total[Length/@lsings]==Length[ansatz],
  	If[Length[lsings[[1]]]==0||lsings[[1]]=={},{},GetSimplifiedDlogList2[GetSimplifiedDlogList[GetDlogListInv[ansatz,lsings,n]/.n[_]:>0]]],  	
  		Print["Warning! Ansatz length and number of leading singularities do not match!"];
  		GetSimplifiedDlogList2[Collect[#,Global`G[__],Factor]&/@(GetDlogListRaw[ansatz,lsings,n]/.n[_]:>0)]
  ]

]

GetSubcuts[cut_, gmax_] := Module[{subcuts, G, i},
	G=Cases[gmax,Q_[_,{__?IntegerQ}]:>Q, Infinity][[1]];
  	subcuts = 
   	Table[If[cut[[i]] == 0, Nothing, ReplacePart[cut, i -> 0]], {i, Length[cut]}];
  	DeleteCases[subcuts, _?((gmax /. (G[_, a_] /; PositionIndex[a][1] != PositionIndex[#][1]) :> 0) == 0*gmax &)]
  ]


FactorCompletelyList[poly_,x_]:=Module[{solns,lcoeff},
	If[Exponent[poly,x]==0,Return[poly]];
	solns=Solve[poly==0,x,Cubics->False,Quartics->False];
	lcoeff=Coefficient[poly,x^Exponent[poly,x]];
	Expand[Join[{lcoeff},(x-(x/.solns))]]
]

FactorCompletelyFLST[flst_]:=Module[{fls, i},
	fls	= flst;
	Do[fls[[1,i,1,2]]=MyFactorList[Times@@(FactorCompletelyList[Times@@Power@@@fls[[1,i,1,2]],flst[[2,1]]])],{i,Length[flst[[1]]]}];
	fls
]


CombineRules[rulelists_, n_] := Module[{normrules, i, changed, pind, ns, inds, count},
	normrules=MyFactor[Quiet[
		Solve[ rulelists[[All, 1]] == rulelists[[All, 2]], 
       	Union[Cases[rulelists, n[_], Infinity]]][[-1]], Solve::svars]];
	normrules=SortBy[NormalizeRule[#,n]&/@normrules,#[[1,1]]&];
	count=1;
	While[True,
		If[count++==300, Print["Combine Rules limit reached"]; Abort[]];
		changed=False;
		pind=PositionIndex[normrules[[All,1]]];
		ns=Union[Cases[normrules[[All,1]],n[_]]];
		Do[
			inds=pind[ns[[i]]];
			If[Length[inds]==1, Continue[]];
			normrules[[inds[[2]]]]
				=
				Quiet[Solve[normrules[[inds[[1]],2]]==normrules[[inds[[2]],2]],Union[Cases[normrules, n[_], Infinity]]][[1,1]],	Solve::svars];
			normrules=SortBy[NormalizeRule[#,n]&/@normrules,#[[1,1]]&];
			changed=True;
			Break[];
			,{i,Length[ns]}
		];
		If[changed==False, Break[]];
					
	];
	Do[normrules[[i]] = normrules[[i, 1]] ->  FactorCollect[normrules[[i, 2]] /. normrules[[1 ;; i - 1]]]
		, {i, Length[normrules]}];
	normrules
 	(*Quiet[NormalizeRule[#, 
      n] & /@ (Solve[rulelists[[All, 1]] == rulelists[[All, 2]], 
       Union[Cases[rulelists, n[_], Infinity]]][[-1]]), Solve::svars]*)
  ]


(*
LsingCut[gfunc_, gmax_, cut_, vars_] := Module[
   {goncut, cutfunc, lsings, combinedlsings, combinedrules, i},
   goncut = 
    Prepend[DeleteCases[
      gmax /. Global`G[_, a_] /; (a /. q_?Negative :> 0) != cut :> 0, 0], 
     gfunc];
    Print[goncut];
   
   cutfunc = GtoFunction[goncut, n, cut];
   SetOutputLevel[-1];
   lsings = 
    Table[PrintTemporary["------------- cut ", i, "--------------"]; 
     LeadingSingularities[cutfunc[[i]], 
      Intersection[Variables[cutfunc[[i]]], IntegrandVariables[]], n, 
      Length[goncut]], {i, Length[cutfunc]}];
   combinedrules = CombineRules[Join @@ lsings[[All, 2]], n];
   combinedlsings = {(Join @@ lsings[[All, 1]])[[GetLinsOrd[Join @@ lsings[[All, 1]]][[1]]]] /. combinedrules, combinedrules};
   GetSimplifiedDlogList[ GetDlogListRaw[goncut, combinedlsings, n] /. n[_] :> 0]
   ];
*)

DlogViaCuts2[i1_, i2_] :=
    Module[ {cut, scuts, current, i,j,q,ccut,sub, cind, lsings, tab, 
      linsol, seclist, lsagain, currentlist},
        If[Length[allcuts]==0||Length[dlogs]==0||Length[gmax]==0||Length[seeds]==0,
            Print["Please initialize dlogs, seeds and gmax"];
            Abort[]
        ];
        cut = allcuts[[i1]];
        scuts = {cut};
        current = seeds[[i1, i2]];
        If[pri>0,Print[scuts]];
        Do[
         scuts = Union @@ (GetSubcuts[#, gmax] & /@ scuts);
         Print[scuts];
         If[ Length[scuts] == 0,
             Break[]
         ];
         Do[
         	 If[pri>-1,Print["Cut ", Position[scuts,ccut][[1,1]]," of ",Length[scuts]]];	
	          If[pri>1,Print[ccut]];
	          (*dp=LsingCut[{current},ccut];
	          Print[dp];
	          If[Length[dp[[1]]]\[Equal]0,Print["Found double pole"];Print[
	          ccut]; Abort[]];*)
	          cind = Position[allcuts, ccut][[1, 1]];
	          lsings = LsingCut[Prepend[dlogs[[cind]], current], ccut];
	          If[ Length[lsings[[2]]] > 0,
	              If[pri>-1,Print["Found double pole"]];
	              seclist = 
	               DeleteCases[
	                gmax /. Global`G[1, 
	                    a_] /; (Count[a[[PositionIndex[ccut][1]]], 1] != 
	                      Count[ccut, 1] || Count[a, 1] != Count[ccut, 1]) -> 0, 0];
	              Print[seclist];
	              lsagain = LsingCut[Prepend[seclist, current], ccut];
	              current = 
	               Prepend[seclist, current].n /@ Range[Length[seclist] + 1] /. 
	                  lsagain[[2]] /. n[1] -> 1 /. n[_] -> 0;
	              If[pri>1,Print["After having removed the double pole"]];
	              If[pri>0,Print[current]];
	              lsings = LsingCut[Prepend[dlogs[[cind]], current], ccut];
	              If[ Length[lsings[[2]]] > 0,
	                  Print["Now I am screwed!"];
	                  Abort[]
	              ];
	          ];
	          If[ Length[Join @@ lsings] != Length[dlogs[[cind]]] + 1,
	              Print["lsings wrong length"];
	              Print[ccut];
	              Print[lsings];
	              Abort[]
	          ];
	          tab = 
	           Table[Coefficient[lsings[[1, i]], n[j]], {i, 
	             Length[lsings[[1]]]}, {j, Length[lsings[[1]]]}];
	          linsol = Factor[LinearSolve[tab, q /@ Range[Length[lsings[[1]]]]]];
	          (*Print[linsol];*)
	          linsol = 
	           Factor[linsol /. 
	              Quiet[Solve[linsol[[1]] == 1, 
	                 q /@ Range[Length[lsings[[1]]]]][[1]], Solve::svars] /. 
	             q[_] -> 0];
	          (*Print[linsol];*)
	          current = 
	           Collect[Prepend[dlogs[[cind]], current].linsol, Global`G[__], Factor];
	          (*current=Prepend[dlogs[[cind]],current].((linsol[[#]]+q[#]&)/@
	          Range[Length[linsol]])/.q[1]\[Rule]0;
	          current=Collect[current,G[__],Simpli[#,q]&];*)
	          (*currentlist=GetSimplifiedDlogList2[GetSimplifiedDlogList[GetDlogListInv[Prepend[dlogs[[cind]], current], lsings, n]]];
	          current = Cases[currentlist, _?(!FreeQ[#,Global`G[_,a_]/;Count[a,1]==Count[cut,1]]&)];
	          If[Length[current]!=1, Print["currentlist error"]; Abort[]];
	          current=current[[1]];*)
	          Print[current];
          ,
          {ccut, scuts}
          ];
         ,
         {sub, 10}];
        current
    ]

LsingCut[gfunc_, cut_, n_]:=Module[{i, vs, exs, lsings, cutfunc, combinedrules, combinedlsings}, 
	cutfunc = GtoFunction[gfunc, n, cut];
	
	(*Print[cutfunc];*)
	lsings =  Table[
		PrintTemporary["Leading singularities on cut: Solution ",i," of ",Length[cutfunc]];
    	vs=(cut/.cuts)[[i,1]];
    	
      	exs=LeadingSingularities[cutfunc[[i]], vs, n];
      	exs
      	,
      	{i, Length[cutfunc]}      	
   	];	
   	If[pri>0,Print["Combine rules"]];
   (*	Print[CombineRuless[Join @@ lsings[[All, 2]], n]];*)
	combinedrules = CombineRules[Join @@ lsings[[All, 2]], n];
	If[pri>0,Print["Combine lsings"]];
	(*combinedls=Join@@(lsings[[All,1]]/.combinedrules);*)
   	combinedlsings = {FactorCollect/@((Join @@ (lsings[[All, 1]]/. combinedrules))[[GetLinsOrd[Join @@ (lsings[[All, 1]]/. combinedrules)][[1]]]]),
   		combinedrules}
]

JoinLsings[lsings_List]:=Module[{combinedrules, combinedlsings},
	combinedrules = CombineRules[Join@@lsings[[All,2]],n];
	combinedlsings = {FactorCollect/@((Join @@ (lsings[[All, 1]]/. combinedrules))[[GetLinsOrd[Join @@ (lsings[[All, 1]]/. combinedrules)][[1]]]]),
   		combinedrules}
]

LsingCut[gfunc_, gmax_, cut_, vars_, n_] := Module[
   {goncut, cutfunc, lsings, combinedlsings, combinedrules, gsim, i, G, vs, exs},
   G=Global`G;
   goncut = 
    Prepend[DeleteCases[
      gmax /. G[_, a_] /; (a /. q_?Negative :> 0) != cut :> 0, 0], 
     gfunc];
   cutfunc = GtoFunction[goncut, n, cut];
   (*SetOutputLevel[0];*)
   (*Print[goncut];*)
   lsings =  Table[PrintTemporary["------------- cut ",i,"--------------"];
     (*LeadingSingularities[cutfunc[[i]], 
      Intersection[Variables[cutfunc[[i]]], IntegrandVariables[]], n, 
      Length[goncut]]*)
      vs=(cut/.cuts)[[i,1]];
      (*Print["bef"];*)
      exs=ExSQRT[cutfunc[[i]], vs, n];
      (*Print["aft"];*)
      exs
      ,
      {i, Length[cutfunc]}
   ];
   combinedrules = CombineRules[Join @@ lsings[[All, 2]], n];
   combinedlsings = {FactorCollect/@((Join @@ (lsings[[All, 1]]/. combinedrules))[[
       GetLinsOrd[Join @@ (lsings[[All, 1]]/. combinedrules)][[1]]]]) , 
     combinedrules};
   Print[combinedlsings];
   If[MatchQ[combinedlsings[[1]],{0}|{}], Return[{}]];
   gsim = GetSimplifiedDlogList[
     Collect[Quiet[GetDlogListRaw[goncut, combinedlsings, n] /. n[_] :> 0, 
      Solve::svars],G[__],Factor]];
   (*Print["gsim"];
   Print[gsim];*)
   gsim= SortBy[
    gsim, -Max[
       Union[Cases[{#}, G[__], Infinity]] /. 
        G[_, a_] :> Count[a, 1]] &];
   Print[gsim[[1]]];
   gsim
];

SetCuts[cutlist_]:=allcuts=cutlist;



ChangeVars[int_, x_List, nv_List] :=
    Module[ {u, sol},
        sol = Solve[u /@ Range[Length[x]] == nv, x];
        Print[sol /. u[h_] :> x[[h]]];
        (int/Det[Table[D[nv[[i]], x[[j]]], {i, Length[nv]}, {j, Length[x]}]] /. sol[[1]] // Factor // PowerExpand // Factor) /. u[h_] :> x[[h]]
]




Options[ExINT] = {ExINTTimeConstraint -> 500};
ExINT[fs_List,vs_,n_,OptionsPattern[]]:=
Module[{sols, exints, fsnew, nums, flats},
	Print[ExIINT[fs,vs,n]];
	(*n=Global`n;*)
	sols={};
	While[
		fsnew=DeleteCases[Together[fs/.sols],0];
		If[Length[fsnew]==0,exints={};Break[]];
		exints=ExIntegrate[fsnew,vs,timeConstraint->OptionValue[ExINTTimeConstraint]];
		If[!FreeQ[exints,DoublePole[_]],
			If[pri>0,Print["Double Pole discovered"]];
			nums=(Numerator[Together[#]]&/@exints[[All,1]]);
			flats=DeleteCases[Flatten[CoefficientList[#,vs]&/@nums],0];
			If[pri>0,Print[flats]];
			sols=Join[sols,Quiet[Solve[flats==0,Cases[Variables[fs],n[_]]]][[1]]];
			If[pri>0,Print[Solved[flats==0,Cases[Variables[fs],n[_]]]]];
			If[pri>0,Print[sols]];
			sols=RearrangeRules[(#[[1]] -> (#[[2]] //.sols)) & /@ sols, n];
			If[pri>0,Print[sols]];
			True,
			False]
	];
	{exints,sols}	
]

ExInteg[func_, v_] := Module[{int, logs},
   (*Print[ExxInteg[func,v]];*)
   int = Integrate[func, v];
   If[! FreeQ[int, Root | EllipticF | EllipticPi | ArcSin | ArcSinh | Integrate | RootSum], 
    Return[Failed[int]]];
   If[Length[Cases[Variables[int],Except[_[_Integer] | (q_/;AtomQ[q]) | Log[_] | ArcTan[_] | ArcTanh[_] ]]]>0 ,
   	Print["New symbols detected"];
   	Print[int];Return[Failed[int]]];
   If[(int /. {Log[_] :> 0, ArcTan[_] :> 0, ArcTanh[_] :> 0}) =!= 0, 
    Return[DoublePole[
      int /. {Log[_] :> 0, ArcTan[_] :> 0, ArcTanh[_] :> 0}]]];
   logs = Cases[Variables[int], Log[_] | ArcTan[_] | ArcTanh[_]];
   Factor[Coefficient[int /. ArcTan[q_] :> I ArcTan[q], #]] & /@ logs
];

Options[ExIntegrate] = {timeConstraint -> 30};
ExIntegrate[fs_List, vs_, OptionsPattern[]] := 
  Module[{ff, fn, dps, dp, vv, failed, variables, dens, i},
   If[pri>-1,Print["Time constraint: " <> 
     ToString[OptionValue[timeConstraint]] <> " seconds"]];
   If[pri>3,Print[ExxIntegrate[fs, vs]]];
   dens=Flatten[(FactorList[Denominator[#]][[All,1]]&/@fs)];
   vv = SortBy[vs, Max[Table[Exponent[dens[[i]],#],{i,1,Length[dens]}]]&];
   If[pri>3,Print[vv]];
   If[pri>3,Print[Max[Table[Exponent[dens[[i]],#],{i,1,Length[dens]}]]&/@vv]]; 
   variables = Variables[fs];
   ff = fs;
   dp = Do[
     If[pri>-1,Print["Step " <> ToString[i] <> " of " <> ToString[Length[vs]]]];
     failed = Do[
       If[pri>-1,Print["---Try " <> ToString[vv[[1]]]]];
       fn = 
        TimeConstrained[Flatten[ExInteg[#, vv[[1]]] & /@ ff], 
         OptionValue[timeConstraint], Failed[Time]];
       (*Print["fn"];
       Print[fn];*)
       If[fn === Failed[Time], Print["---Integrate took too long"]];
       If[(! FreeQ[fn, vv[[1]]]) && FreeQ[fn, DoublePole], 
        Print["Variable-Still-There-Error"]; Return[fn]];
       If[
        Length[Cases[Variables[fn], 
           Except[Alternatives @@ variables | Log[_] | ArcTan[_] | 
             ArcTanh[_] | Failed[_] | DoublePole[_] ]]] > 0, 
        Print["Found unknown variables: "]; 
        Print[Cases[Variables[fn], 
           Except[Alternatives @@ variables | Log[_] | ArcTan[_] | 
             ArcTanh[_] | Failed[_] | DoublePole[_]]]];
             Return[fn]];
       If[FreeQ[fn, Failed],
        Break[]
        ,
        vv = Drop[Append[vv, vv[[1]]], 1];
        If[j == Length[vv], Print["All variables failed"]; Return[fn]];
        ]
       , {j, 1, Length[vv]}
       ];
     If[failed =!= Null, Return[failed]];
     ff = fn;
     dps = Cases[Variables[ff], DoublePole[_]];
     If[Length[dps] > 0, Return[dps]];
     ff = ff[[GetLinsOrd[ff][[1]]]];
     vv = Drop[vv, 1];
     , {i, 1, Length[vs]}];
   If[dp =!= Null, dp, ff]
];



SetN[nn_]:= Module[{},	
	If[!AtomQ[nn]||NumericQ[nn], Print["Only symbolic values"]; Abort[]];
	n=nn;
]

Test[n_]:=Module[{},
	Print[n];
	Print[dlogbasis`Private`n];
	True		
]

GetN[]:=n



SQFunc[]:=0;

GetSQFunc[func_, n_, vars_]:=Module[{fsq},
	fsq = func/.Sqrt[q_]:>sqrt[q];
		
]



ChooseLinearInd[matrix_] := Module[{vars, reps, newmat, rank, inds, i},
  vars = Variables[matrix];
  reps = Table[vars[[i]] -> Prime[13 i + 17], {i, Length[vars]}];
  newmat = {(*matrix[[1]] /. reps*)};
  rank = 0;
  inds = {};
  Do[newmat = Append[newmat, matrix[[i]] /. reps]; 
   If[MatrixRank[newmat] == rank, newmat = Delete[newmat, -1], rank++;
     inds = Append[inds, i]], {i, Length[matrix]}];
  inds
  ]



GetGram[v1_, v2_] := Module[{i,j},
  GetGFunc[Det[Table[v1[[i]].v2[[j]], {i, Length[v1]}, {j, Length[v2]}]]]
  ]

EpsilonCon[] := 0;

ExpandEpsilonCon[term_, vecs_] := Module[{qrep, k, kv, vv, q},
  kv = Total[(vv /@ Range[4]) (q /@ Range[4])];
  qrep = Solve[
     Expand[{vv[1] kv == vv[1].k, vv[2] kv == vv[2].k, vv[3] kv == vv[3].k, 
        vv[4] kv == vv[4].k}] /. {vv[i_] vv[j_] :> vv[i].vv[j], 
       vv[i_]^2 :> vv[i].vv[i]}, q /@ Range[4]][[1]];
  term //. 
      EpsilonCon[a___, kk_, b___] /; MemberQ[internal, kk] :> 
       EpsilonCon[a, Total[vecs (q[kk] /@ Range[4])], b] //. {EpsilonCon[
        u___, a_ + b_, v___] :> EpsilonCon[u, a, v] + EpsilonCon[u, b, v], 
      EpsilonCon[u___, a_ b_, v___] /; MemberQ[vecs, b] :> 
       a EpsilonCon[u, b, v], EpsilonCon[___, a_, ___, a_, ___] :> 0} /. 
    EpsilonCon[a__] :> Signature[{a}] (EpsilonCon @@ Sort[{a}]) /. 
   q[ki_][j_] :> ((q[j] /. qrep) /. {vv[i_] :> vecs[[i]], k :> ki})
  ]


BaikovCut[cut_, loops_List,qrep_]:= Module[{grams, psps, sps, i, j, k, ir, u, v, projections},
	grams=Table[{GramDet[Join@@loops[[i]]],GramDet[loops[[i,2]]]},{i,Length[loops]}];
	sps=Sort[Flatten[
		{	Table[Dot[loops[[i,1,j]],loops[[i,2,k]]],{i,Length[loops]},{j,Length[loops[[i,1]]]},{k,Length[loops[[i,2]]]}],
			Table[Dot[loops[[i,1,j]],loops[[i,1,k]]],{i,Length[loops]},{j,Length[loops[[i,1]]]},{k,j,Length[loops[[i,1]]]}]
		}
		]/.Dot[a_,b_]:>Dot@@Sort[{a,b}]
	];

	psps=Union[Cases[ExpandVectors[propagators/.qrep,Join[internal,external,Join@@loops[[All,2]]]],Dot[a_,b_]/;(MemberQ[internal,a]||MemberQ[internal,b]),Infinity]];
	Print[sps];
	Print[psps];
	Print[grams];
	projections=Flatten[Table[spprojection[loops[[u,1,i]],ir,loops[[u,2]]],
		{u,Length[loops]},{v,Length[loops],Length[loops]},{ir,Complement[loops[[v,2]],loops[[u,2]]]},{i,Length[loops[[u,1]]]}]]
	
		
]


(*
CorrectOnCut[term_,cut_,gmax_]:=Module[{gmcut,ls,dll},
	gmcut=DeleteCases[gmax/.Global`G[1,a_]/;(a/.{_?Negative:>0})!=cut:>0,0]//Union;
	gmcut=gmcut[[GetLinsOrd[gmcut][[1]]]];
	Print[gmcut];
	ls=LsingCut[Append[gmcut,term],cut];
	If[Total[Length/@ls]!=Length[gmcut]+1,Print["Too few or too many leading singularities"]];
	dll=GenerateDlogbasis[Append[gmcut,term],ls,n];
	Cases[dll,a_/;GetSector[a]=!=cut][[1]]
]
*)
CorrectOnCut[term_,cut_,gmax_,cinds_:0]:=Module[{gmcut,ls,dll,cutseeds,mat,numeric,inds,vs,ggcut,gs,cutsol,cutf},
	gmcut=DeleteCases[gmax/.Global`G[1,a_]/;(a/.{_?Negative:>0})!=cut:>0,0]//Union;
	gmcut=gmcut[[GetLinsOrd[gmcut][[1]]]];
	Print[gmcut];
	cutseeds=GetSeeds[cut];
(*Print[cutseeds];*)
	gs=Cases[{gmcut,cutseeds},_Global`G,All]//Union;
	 mat=Table[Coefficient[Join[cutseeds,gmcut][[i]],gs[[j]]],{i,Length[Join[cutseeds,gmcut]]},{j,Length[gs]}];
	vs=Variables[mat];
	numeric=Table[vs[[i]]->Prime[10+5 i],{i,Length[vs]}];
	Print[numeric];
	inds=ChooseLinearInd[mat/.numeric];
	Print[inds];
	ggcut=Join[cutseeds,gmcut][[inds]];
	cutsol=cut/.GetCutSolutions[];
	Print[Append[ggcut,term]];
	cutf=GtoFunction[Append[ggcut,term],n,cut];
	ls=JoinLsings[Table[LeadingSingularities[cutf[[i]],Reverse[cutsol[[i,1]]]	,n],{i,If[cinds===0,Range[Length[cutsol]],cinds]}]];
	If[Total[Length/@ls]!=Length[ggcut]+1,Print["Too few or too many leading singularities"]];
	dll=GenerateDlogbasis[Append[ggcut,term],ls,n];
	Cases[dll,a_/;GetSector[a]=!=cut][[1]]
]

GetSector[term_] := Module[{secs},
  secs = Cases[term, _Global`G, All]/.Global`G[_,a_]:>(a/.{_?Positive :> 1, _?Negative :> 0});
  max=Max[Count[#,1]&/@secs];
  BitOr@@(Cases[secs,a_/;Count[a,1]==max])
  ]

MaxPosition[list_List, func_] := Module[{max, fl},
  fl = func /@ list;
  max = Max[fl];
  Position[fl, max][[1, 1]]
  ]
  
  
spprojection[k_, v_, base_] := 
 Module[{}, 
  k.v -> Sum[
     GramDet[base /. b -> k, base]/GramDet[base] b.v, {b, base}] /. 
   Dot[a_, b_] :> Dot @@ Sort[{a, b}]]


  
End[] (* End Private Context *)

EndPackage[]

Print["DlogBasis: Package for automated calculation of leading singularities and dlog integrands.
Pascal Wasser, Johannes Gutenberg University Mainz (2019)."];

