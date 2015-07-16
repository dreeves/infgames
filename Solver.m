(* Best-Response finder for 2-player, one-shot, infinite games of incomplete 
   information.  Daniel Reeves.
   USAGE: br[GAME,TYPE][STRAT] --> BRSTRAT
     GAME gives the utility function parameters for one agent.
     (See equation 2.1 and table 2.1 on pages 8 and 10 of my thesis.)
       GAME = {theta, rho, theta', rho', phi, beta, alpha}
         where all but alpha are lists.
     TYPE gives the piecewise uniform type distribution of the agent.
     (See appendix A.1 on page 121 of my thesis.)
       TYPE = {d, f} where d is a list of the boundary points and f is a list
         of the pdf values between those points.  Eg, uniform = {{0,1},{1}}.
     STRAT gives the strategy of the opponent to find the best response to.
     (See equation 2.2 on page 9 of my thesis.)
       STRAT = {c, m, b}.  Eg, truthful bidding = {{},{1},{0}}.
   For asymmetric games: abr[{GAME1,GAME2},{TYPE1,TYPE2}][{STRAT1,STRAT2}]
     returns {BRSTRAT1,BRSTRAT2} where GAME1 gives agent 1's utility, TYPE1
     agent 1's type distribution, and STRAT1 agent 1's initial strategy.
     Similarly for agent 2.  BRSTRAT1 then gives agent 1's best response 
     to agent 2 playing STRAT2 and BRSTRAT2 gives agent 2's best response
     to agent 1 playing STRAT1.  abr[] can thus be nested just like br[].
*)

WriteString["stderr", "[Solver.m]"];
BeginPackage["Solver`"];

(************************************************************************)
(* EXPORTED FUNCTIONS, SAMPLE GAMES, TYPE DISTRIBUTIONS, AND STRATEGIES *)
(************************************************************************)

br; abr;
showStrats;
stratToFunc; utilToFunc;

cmpr; sga; influence; vickrey; saspa; vv; fpsb; kpsb; allPay; supchain;
jpa; swinkels; concession; bargSeller; bargBuyer; 
  
uniform; pdf1; 
  
truthful;


Begin["`Private`"];  (*******************************************************)
  
(* Compromise game *)
cmpr = {{0,1}, {0,-1}, {0,0}, {0,1}, {1/2,0}, {1}, 1};

(* Shared-Good Auction: the SCF is for the agent who cares most about 
   getting its preferred outcome to get its way and pay the other agent
   for the privelege. The original shared-good auction is the special 
   case that h=1/2,k=0. *)
sga[h_,k_] := 
  {{0,1/2,1},{k,(k-h)/2,-h},{0,0,0},{h,(h-k)/2,-k},{0,0,0},{0,0},-1}

(* I don't remember what this game was supposed to be about. *)
influence = {{0,1/2,1},{-1,-1,-1},{0,0,0},{1,1,1},{0,0,0},{0,0},-1};

vickrey = {{0,1/2,1},{0,0,0},{0,0,0},{0,-1/2,-1},{0,0,0},{0,0},-1}; 

(* Simultaneous Ascending Second-Price Auction *)
saspa = {{0,1/2,1},{0,0,0},{0,0,0},{0,-1,-2},{0,0,0},{0,0},-1}; 

vv[k_] :=  (* Vicious Vickrey Auction *)
  {{0,(1-k)/2,1-k},{k,k/2,0},{-k,-k/2,0},{0,(k-1)/2,k-1},{0,0,0},{0,0},-1}

(* First-Price Sealed-Bid Auction *)
fpsb = {{0,1/2,1},{0,-1/2,-1},{0,0,0},{0,0,0},{0,0,0},{0,0},-1}; 

(* KPSB generalizes FPSB and Vickrey.  k = 0 is FPSB; k = 1 is Vickrey. *)
kpsb[k_] := {{0,1/2,1}, {0,(k-1)/2,k-1},{0,0,0},{0,-k/2,-k},{0,0,0},{0,0},-1}

allPay = {{0,1/2,1},{-1,-1,-1},{0,0,0},{0,0,0},{0,0,0},{0,0},-1}; 

supchain[v_:((10-5^(1/2))/5)] :=  (* Supply-Chain Game *)
  {{-1,-1,0},{1,1,0},{0,0,0},{0,0,0},{0,0,0},{v,v},1}

(* Joint Purchase Auction *)
jpa[c_] := {{0,1},{0,-1/2},{0,0},{0,1/2},{0,-c/2},{c},1}

swinkels = {{0,1/2,1},{0,-1/2,-1},{0,-2,-4},{0,0,0},{0,2,4},{0,0},-1}; 

concession = {{0,0,0},{-1,-1,-1},{0,0,0},{0,0,0},{0,1/2,1},{0,0},-1}; 

(* Sealed-Bid Double Auction with k=1/2.  "Bargling". *)
bargSeller = {{-1,0},{1/2,0},{0,0},{1/2,0},{0,0},{0},-1}; 
bargBuyer = {{0,1},{0,-1/2},{0,0},{0,-1/2},{0,0},{0},-1}; 

uniform = {{0,1},{1}};  (* U[0,1] type distribution *)

pdf1 = {{0,1/2,1},{1/2,3/2}}; 

truthful = {{},{1},{0}};   (* truthful bidding *) 

debug[x___] := If[False, Print[x]]

(* Make 0*Infinity evaluate to 0.  Thanks to Daniel Lichtblau of WRI. *)
Unprotect[DirectedInfinity]; 
DirectedInfinity /: Unevaluated[0*DirectedInfinity[_]] := 0
DirectedInfinity /: Unevaluated[0*ComplexInfinity] := 0

(* The cdf given a piecewise uniform pdf. *)
F[-Infinity] = 0; 
F[+Infinity] = 1; 
F[x_] := Sum[Boole[d[[i]] <= x < d[[i+1]]] * 
               (f[[i]]*(x-d[[i]]) + Sum[f[[j]]*(d[[j+1]]-d[[j]]), {j,1,i-1}]), 
             {i, 1, Length[d]-1}]

(* argMax[f, domain] returns the element of domain for which f of that element
   is maximal -- breaks ties in favor of first occurrence. *)
SetAttributes[argMax, HoldFirst]; 
argMax[f_, dom_List] := Fold[If[f[#1]>=f[#2],#1,#2]&, First[dom], Rest[dom]]

(* argMaxSet[f,domain] returns the set of elements in domain for which f is 
   maximal *)
SetAttributes[argMaxSet, HoldFirst]; 
argMaxSet[f_, dom_List] := First[Split[Sort[dom, f[#1]>f[#2]&], f[#1]==f[#2]&]]

cons[a_, l_] := Prepend[l, a]

arbAux[{a_}] := {a}
arbAux[{{c1_, m_, b_}, {c2_, r___}, r2___}] := 
  Which[{r} == {}, cons[{c1, m, b}, arbAux[{{c2, m, b}, r2}]], 
        True, cons[{c1, m, b}, arbAux[{{c2, r}, r2}]]]

(* Add Redundant Boundaries. Returns new {c, m, b}. *)
arb[c_, m_, b_, d_] := Module[{x}, 
  x = arbAux[Sort[Join[Transpose[{cons[-Infinity, c], m, b}], 
                       Transpose[{Complement[d, c]}]], 
                  First[#1]<First[#2]&]]; 
  cons[Rest[First/@x], Transpose[Rest/@x]]]

(* Remove Redundant Boundaries. *)
rrb[{}, m_, b_] := {{}, m, b}
rrb[{c1_,c___}, {m1_,m1_,m___}, {b1_,b1_,b___}] := rrb[{c}, {m1,m}, {b1,b}]
rrb[{c1_,c___}, {m1_,m___}, {b1_,b___}] := 
  MapThread[cons, {{c1,m1,b1}, rrb[{c}, {m}, {b}]}]

mm[a_, b_, x_] := Min[b, Max[a, x]]

x0[i_, j_, a_] := (p6[[i]]   - p7*b[[j]] - a) / (p7*m[[j]])
y0[i_, j_, a_] := (p6[[i+1]] - p7*b[[j]] - a) / (p7*m[[j]])

x[i_, j_, a_] := If[p7*m[[j]] > 0, x0[i,j,a], y0[i,j,a]]
y[i_, j_, a_] := If[p7*m[[j]] > 0, y0[i,j,a], x0[i,j,a]]

p[i_,j_,a_] := F@mm[c[[j]],c[[j+1]],y[i,j,a]] - F@mm[c[[j]],c[[j+1]],x[i,j,a]]
(* SCHED FOR DEL: multiply this by (F[c[[j+1]]] - F[c[[j]]]) for some reason *)

xy[i_,j_,a_] := (1/2)*(mm[c[[j]], c[[j+1]], x[i,j,a]] 
                     + mm[c[[j]], c[[j+1]], y[i,j,a]])

eu[t_, a_] := Sum[
  If[p7*m[[j]] == 0, 
     If[If[OddQ[i], p6[[i]] - p7*b[[j]] < a < p6[[i+1]] - p7*b[[j]], 
           p6[[i]] - p7*b[[j]] <= a <= p6[[i + 1]] - p7*b[[j]]], 
        Evaluate[(p1[[i]]*t + p2[[i]]*a + (1/2)*(c[[j]] + c[[j+1]])*(p3[[i]] + 
                  p4[[i]]*m[[j]]) + p4[[i]]*b[[j]] + p5[[i]])
                 *(F[c[[j+1]]] - F[c[[j]]])], 0], 
    If[c[[j]]==-Infinity || c[[j+1]]==Infinity, 0, 
       (p1[[i]]*t + p2[[i]]*a + (p3[[i]] + p4[[i]]*m[[j]])*xy[i,j,a] + 
       p4[[i]]*b[[j]] + p5[[i]])*p[i,j,a]]], 
  {i, 1, Length[p1]}, {j, 1, Length[m]}]

abounds[] := Union@Flatten@{
  Table[p6[[i]]-p7*(m[[j]]*c[[j]]+b[[j]]), {i,2,Length@p1}, {j,2,Length@m}], 
  Table[p6[[i]]-p7*(m[[j]]*c[[j+1]]+b[[j]]), {i,2,Length@p1},{j,1,Length@m-1}]}

(* Returns a list of (1 or 0) maxima of f[x] if it's a deg <= 2 polynomial. *)
maxima[f_, x_] := Module[{sol}, 
  sol = Check[Solve[D[f, x] == 0, x], Print["ERROR in maxima: ", f]; Abort[]]; 
  If[sol === {} || sol === {{}} || D[f, {x,2}] >= 0, {}, {sol[[1,1,2]]}]]

solveFor[var_][{left_, right_}] := Module[{sol}, 
  sol = Check[Solve[left==right, var], 
              Print["ERROR in solveFor[",var,"][{",left,",",right,"}]"]; {}]; 
  If[sol === {} || sol === {{}}, Return[{}]]; 
  (#[[1,2]]&)/@sol]

(* MidPoints. Take a 1D list of boundary points and return points between 
   the boundaries, including one just before the first boundary and just 
   after the last. *)
mp[{}] = {0}; 
mp[l_] := (First@#+Last@#)/2&/@Partition[Join[{First@l-1}, l, {Last@l+1}], 2,1]

(* Converts {a,b} to a<=x<=b.  Used by stratToFunc. *)
rangeToCond[var_Symbol][{min_, max_}] := min <= var <= max
rangeToCond2[var_Symbol][{min_, max_}] := min < var < max

(* Converts {a,b} to ax+b.  Used by stratToFunc. *)
abToF[var_Symbol][{a_, b_}] := a*var + b

(* Returns a lambda function mapping type to action. *)
stratToFunc[{c_, m_, b_}] :=
  Module[{ifs, thens, t, c0 = Join[{-Infinity},c,{+Infinity}]}, 
    ifs = Partition[c0, 2, 1]; 
    thens = Transpose[{m, b}]; 
    Function[t, Evaluate[Which@@Flatten[Transpose[{rangeToCond[t]/@ifs, 
                                                  abToF[t]/@thens}]]]]]

(* Takes game params and returns a lambda function mapping own type, own 
   action, other actions to payoff. *)
(*
utilToFunc[{p1_,p2_,p3_,p4_,p5_,p6_,p7_}] :=
  Module[{ifs, thens, t, a, t2, p6a = Join[{-Infinity},p6,{+Infinity}]},
*)
     

(* Best Action for Type.  
   Takes a specific type and candidate actions and returns the set of actions 
   that tie for greatest utility for that type. *)
bat[t0_, a_] := argMaxSet[Simplify[eu[t0, # /. t->t0]]& , a]
(* Sort[a , (# /. t -> t0) == stratToFunc[{c, m, b}][t0] &] *)


(* By Carl K. Woll < carlw@u.washington.edu >. Basically, you start at the 
   beginning and find the element which gives you the longest string of common
   elements. Once the string can no longer be extended, start a new string. *)
pick[data_] := Module[{common, tmp}, 
  common = {}; 
  tmp = Reverse[
    (If[(common= Intersection[common, #])=={}, common= #, common]&) /@ data]; 
  common=.;
  Reverse[(If[MemberQ[#,common], common, common= First[#]]&) /@ tmp]]

(* Best Response given game params, type dist, and strategy {c, m, b}. *)
br[{p1a_,p2a_,p3a_,p4a_,p5a_,p6a_,p7a_}, {d0_,f0_}][{c0_,m0_,b0_}] := 
  Module[{ab, au1, u2, a2, au2, au, ca, cu, pairs, tb, actions, i}, 
    debug["DEBUG: b0: ", b0]; 
    p1 = p1a; p2 = p2a; p3 = p3a; p4 = p4a; p5 = p5a; 
    p6 = Join[{-Infinity}, p6a, {+Infinity}]; 
    p7 = p7a; 
    d = Join[{-Infinity}, d0, {+Infinity}]; 
    f = Join[{0}, f0, {0}]; 
    {c, m, b} = arb[c0, m0, b0, d0]; 
    debug["DEBUG: arb[",c0,", ",m0,", ",b0,", ",d0,"] = ",arb[c0,m0,b0,d0]]; 
    c = Join[{-Infinity}, c, {+Infinity}]; 
    ab = Sort[Union[Join[{-Infinity}, abounds[], {Infinity}]], Less]; 
    debug["DEBUG: {c,m,b,p1,p6,p7} = ", {c, m, b, p1, p6, p7}]; 
    debug["DEBUG: ab = ", ab]; 
    debug["DEBUG: ab assumptions: ", 
      (First@# < a < Last@#&) /@ Partition[ab,2,1]]; 
    (* action-utility pairs at action boundaries *)
    au1 = ({#, eu[t, #]}&) /@ Select[ab, -Infinity < # < Infinity & ]; 
    debug["DEBUG: au pairs for abounds: ", au1]; 
    (* debug["DEBUG: eu[t,2/3v-1/2] = ", eu[t, 2/3v - 1/2]]; *)
    (* best auction-utility pairs between action boundaries *)
    u2 = (Refine[FullSimplify[eu[t,a] /. DirectedInfinity[i_] -> i*10^100, 
                              First@# < a < Last@# && -10^100 < a < 10^100], 
                 First@# < a < Last@# && -10^100 < a < 10^100]&) /@ 
           Partition[ab, 2,1]; 
    a2 = maxima[#,a]& /@ u2; 
    (* TODO : a2 should have infinities when needed *)
    debug["DEBUG: au pairs between abounds: ", Transpose[{a2, u2}]]; 
    au2 = Flatten /@ Select[Transpose[{a2,u2}], Length@First@# != 0 &]; 
    (* debug["DEBUG: au1 = ", au1, " -- au2 = ", au2]; *)
    au2 = {First@#, Last@# /. a->First@#}& /@ au2; 
    au = Join[au1,au2]; 
    debug["Best Response Candidates (action-utility pairs): ", au]; 
    {ca,cu} = Transpose@au; 
    pairs = Union[Sort /@ Select[Tuples[{ca,ca}], First@# =!= Last@# &]]; 
    debug["DEBUG: type pairs: ", pairs]; 
    tb = Sort[Union[Take[c,{2,-2}],  (* don't think we need c there *)
                    Select[Flatten[solveFor@t /@ pairs], Im[#]==0&]], Less];
    debug["DEBUG: bat: ", stratToFunc[{c0, m0, b0}]]; 
    actions = bat[#,ca]& /@ mp@tb; 
    (* Print["BAT LENGTHS: ", Length /@ actions]; *)
    (* Print["BAT:\n", actions]; *)
    actions = pick[actions]; 
    (* Print["PICK DONE"]; *)
    debug["DEBUG: bat[1/6,ca,{c0,m0,b0}] = ", bat[1/6, ca, {c0,m0,b0}]]; 
    debug["DEBUG: {tb,actions,mp[tb]}: ", {tb, actions, mp[tb]}]; 
    rrb[tb, D[#, t]& /@ actions, actions /. t -> 0]]

(* Best Responses for an asymmetric game.  
   Takes a pair of game param sets (utility function for agent 1 and 2), 
   pair of type dists, and a pair of strategies.  Returns new pair of 
   strategies. *)  
abr[{u1_, u2_}, {t1_, t2_}][{s1_, s2_}] := {br[u1, t2][s2], br[u2, t1][s1]}

(* USAGE : FixedPoint[br[game, types], seedStrat, maxIterations] *)

(* Helper function for showStrats. *)
blueToPink[x_] := Hue[-0.83*x + 0.67]

(* Graphically show a set of strategies, varying in color from blue to pink.
   [a,b] is the type range and compare is a comparison strategy. *)
showStrats[strats_, a_:0, b_:1, compare_:{}] := 
  Module[{p1, p2, x, n = Length@strats}, 
    p0 = Plot[stratToFunc[Last[strats]][x], {x, a, b}, 
              PlotStyle -> {{Thickness[0.0065], GrayLevel[0.8]}}]; 
    p1 = Show[MapThread[Plot[#1[x], {x,a,b}, 
                             PlotStyle -> {blueToPink[(#2-1)/Max[1, n-1]]}]&, 
                        {stratToFunc /@ strats, Range[n]}]]; 
    p2 = If[compare=={}, {}, Show[Plot[#[x], {x,a,b}]&/@compare]]; 
    Show[p0, p1, p2, PlotRange->All, Frame->True, Axes->False] 
]
  
End[];  (* Private context *)
EndPackage[];

(************************************************************************)
(*                              SCRATCH                                 *)
(************************************************************************)
  
(* These are built in now (by version 6 at latest). *)
(*
Unprotect[Min, Max]; (* Why aren't these identities automatic? *)
Min[x_, -Infinity] := -Infinity
Min[x_, +Infinity] := x  (* The only of these identities that's built in. *)
Max[x_, -Infinity] := x
Max[x_, +Infinity] := +Infinity
Protect[Min, Max]; 
*)

(* a bunch of sucky ways to do pick[]... *)

(* Used by bestFirstSearch. *)
(*
treeSearch[states_List, goal_, successors_, combiner_] := 
  Which[states == {}, $Failed, 
   goal[First[states]], First[states], True, 
   treeSearch[combiner[successors[First[states]], 
     Rest[states]], goal, successors, combiner]]
*)

(* Takes a start state, 
  a function that tests whether a state is a goal state, 
  a function that generates a list of successors for a state, 
  and a function that gives the cost of a state.  
      Finds a goal state that minimizes cost. *)
(*
bestFirstSearch[start_, goal_, successors_, costFn_] := 
  treeSearch[{start}, goal, successors, 
             Sort[Join[#1, #2], costFn[#1]<costFn[#2]&]&]
*)

(* A goal state is one for which we've picked one element of every list in l. *)
(*
goal[l_][state_] := Length[state] == Length[l]
*)

(* If in state s we've picked one element from each list in l up to list i, 
   then the successors are all the possible ways to extend s to pick elements
   thru list i + 1. *)
(*
successors[l_][state_] := (Append[state, #1] & ) /@ l[[Length[state] + 1]]
*)

(* Cost function g : higher cost for more neighbors different, breaks ties in
   favor of longer states to keep from unnecessarily expanding the search 
   tree. *)
(*
g[l_][state_] := Length[Split[state]]*(Length[l]+1) + Length[l] - Length[state]
g[l_][state_] := -Length[state]
*)


(* Pick one element from each of the lists in l so as to minimize the
   cardinality of Split, ie, maximize the number of elements that are the same 
   as their neighbor. *)
(* pick[l_]:=bestFirstSearch[{},goal[l],successors[l],g[l]] *)

(* Dynamic programming version... *)
(* 
  pick[{}]={};
  pick[{l1_}]:={l1[[1]]};
  pick[{{x_},l2_}]:=If[MemberQ[l2,x],{x,x},{x,l2[[1]]}]
    pick[{l1_,{{x_}}}]:=If[MemberQ[l1,x],{x,x},{l1[[1]],x}]
      pick[{a___,{{x_}},b___}]:=(Print[Length[{a}]," -- ",Length[{b}]];
          Join[pick[{a}],{x},pick[{b}]])
        pick[l_]:=Module[{m=Quotient[Length[l]+1,2],a,b,candidates},
            a=Take[l,{1,m-1}];
            b=Take[l,{m+1,Length[l]}];
            
            candidates=(Join[Drop[pick[Join[a,{{#}}]],-1],{#},
                      Drop[pick[Join[{{#}},b]],1]]&/@l[[m]]);
            argMax[-Length[Split[#]]&,candidates]]
*)

(* Myopic version... *)
(*
  pick[{}]={};
  pick[{l1_}]:=First[l1]
    pick[{l1_,l2_,r___}]:=Which[Intersection[l1,l2]\[Equal]{},
*)

(* written by drbob@bigfoot.com -- this version broken *)
(* 
  pick[raw:{__List}]:=
    Module[{sets=Union/@raw,choice,costBounds,choiceConstraints,pVar,
        costConstraints,objective,p,cVar,vars,bounds,solution},
      choice[set_,{index_}]:=Plus@@(p[index,#1]&)/@set\[Equal]1;
      costBounds[{set1_,set2_},{index_}]:=
        Module[{switches},
          switches=Plus@@(p[index,#1]&)/@Complement[set1,set2];
          {(cost[index]\[GreaterEqual]switches+(p[index,#1]-p[index+1,#1])&)/@
              Intersection[set1,set2],cost[index]\[GreaterEqual]switches}];
      choiceConstraints=Flatten[MapIndexed[choice,sets]];
      pVar=Union[Cases[choiceConstraints,_p,Infinity]];
      costConstraints=Flatten[MapIndexed[costBounds,Partition[sets,2,1]]];
      cVar=Union[Cases[costConstraints,_cost,{2}]];objective=Plus@@cVar;
      vars=Flatten[{pVar,cVar}];
      bounds=Thread[0\[LessEqual]vars\[LessEqual]1];
      solution=
        Minimize[
          Flatten[{objective,choiceConstraints,costConstraints,bounds}],vars];
      Cases[Last[solution]/.Rule\[Rule]rule,rule[p[_,a_],1]\[RuleDelayed]a]]
*)

(* By Andrzej Kozlowski<akoz@mimuw.edu.pl> *)
(* <<DiscreteMath`Combinatorica` *)

(* pick[sp_]:=
    Block[{n=Length[sp],c=Length[sp],w},
      partialQ[l_List]:=
        Which[Length[l]\[Equal]n&&(w=Length[Split[l]])\[LessEqual]c,c=w;True,
          Length[l]<n&&Length[Split[l]]\[LessEqual]c,True,True,False];
      solutionQ[l_List]:=
        If[Length[l]\[Equal]n&&(w=Length[Split[l]])\[LessEqual]c,c=w;True,
          False];Last[Backtrack[sp,partialQ,solutionQ,All]]]
*)

