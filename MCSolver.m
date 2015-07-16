(* Daniel Reeves  2001.03.15
   Empirically determine best-response strategies to given strategies for 
   games where the action (eg, a bid) is a single number and the payoff 
   depends on a private piece of information, also a number (eg, your 
   valuation), known as the agent's type.

   TODO: empirically find a nash equilibrium by starting with a seed 
         strategy and proceeding to best-response fixed-point.
*)

WriteString["stderr", "[Equilibria.m]\n"];

BeginPackage["Equilibria`", {"MonteCarlo`", "Util`"}];
(* All non-private symbols must be listed below... *)

(* The following should be redefined by the program using this library... *)
payoff;
minType;
maxType;
minAction;
maxAction;
randType;
defaultConfidenceLevel;

(* The following are the functions available in this library, with their
   options listed after... *)
psHash;   (* makeData *)
psHashDomain;  (* see to-do's about this *)
allTypes;
ps;
makeTypeActionPairs;

(*
probLessThan;
maxRange;
*)

showBestAction;     {confidence, compareFuncs};
bestActionRange;    {confidence};
showBestResponse;   {confidence, compareFuncs};

(* Protect["*"];  Or do Protect on all the symbols above... *)


Begin["`Private`"];  (****************************************************)

(* payoff[myType, myAction, otherActions] gives the payoff to an agent of type
   myType doing action myAction when its opponents are doing otherActions.  
   This should be redefined by the program using this library. *)
payoff[myType_, myAction_, otherActions_] := 0

(* minType gives the minimum value for an agent's type.  This can be redefined
   by the program using this library. *)
minType = 0;

(* maxType give the maximum value for an agent's type.  This can be redefined
   by the program using this library. *)
maxType = 1;

(* minAction[myType] is a function mapping an agent's type to the minimum 
   value for an action that it can/would do.  This can be redefined by the 
   program using this library. *)
minAction[myType_:0] := 0
(* TODO: both this definition and the overriding one have to be defined in 
exactly the same way (eg, both need to have the default arg like that) 
otherwise the new one won't override this one. *)

(* maxAction[myType] is a function mapping an agent's type to the maximum 
   value for an action that it can/would do.  
   This can be redefined by the program using this library. *)
maxAction[myType_:0] := 1

(* randType[] is a function which generates an agent type according to the 
   common knowledge distribution from which agent types are drawn.  This can 
   be redefined by the program using this library. *)
randType[] := RandomReal[]

(* defaultConfidenceLevel is used for functions that compute mean confidence 
   intervals, either to show error bars (showBestAction, showBestResponse) or 
   to compute a range directly (bestActionRange).  This can be redefined by 
   the program using this library. *)
defaultConfidenceLevel = .95;

(****************************************************************************)

(* psHash maps type, action, and strategy list to statistics {n, s, ss} for 
   the expected payoff for an agent of that type using that strategy against 
   those strategies. *)
psHash[type_, action_, strategies_] = {0, 0, 0}

(* (ba = best action). caches action range we need to try. *)
baHash[type_, strategies_] = {minAction[type], maxAction[type]}

(* makeData[myType, strategies] returns a list of {action, {n,s,ss}} pairs 
   for the given type, based on psHash. *)
makeData[myType_, strategies_List] := {#[[2]], psHash@@#}& /@ 
  Union[{{myType, minAction[myType], strategies}, 
         {myType, maxAction[myType], strategies}}, 
        Select[psHashDomain, (#[[1]]==myType && #[[3]]==strategies)&]];
  (* TODO: using the global psHashDomain updated by ps[] instead of 
           making the expensive domain[psHash] call each time; below too *)

(* allTypes[strategies] returns a list of the types cached in psHash. *)
allTypes[strategies_] := Union[First /@ Select[psHashDomain, 
                                               #[[3]]===strategies&]]

(****************************************************************************)

(* TODO: we might be able to simulate more points in less time by flooring
         the time constraint to an integer so we can use TimeConstrained. *)
(* TODO: allow an arbitrary distribution for agent types *)
(* ps[myType, myAction, strategies] (ps = payoff stats) does a montecarlo 
   simulation to estimate expected payoff for an agent of a certain type 
   doing a certain action, when up against given opponent strategies 
   (functions mapping a type to an action).  
   It computes and caches (in psHash) the list {n,s,ss} for each type-action 
   simulated -- {n,s,ss} is the number of trials simulated for the type-action 
   pair, the sum of the payoffs, and the sum of the squares of the payoffs.  
   To do the simulation, this function uses the random type generator randType 
   which returns a random agent type according to the common knowledge 
   distribution.  
   It also assumes the existence of the payoff function which maps my type, 
   my action, and opponent actions to my payoff.  
   Additionally, myType and myAction can be lists of types/actions, in which 
   case the function returns a list of pairs -- {type,{n,s,ss}} if given a 
   list of types, or {action,{n,s,ss}} if given a list of actions, or 
   {{type,action},{n,s,ss}} if given both a list of types and a list of 
   actions (same thing if given a list of type-action pairs). *)
ps[myType_/;Head[myType]=!=List, 
   myAction_/;Head[myAction]=!=List, strategies_List] :=
  Module[{x, n = 0, s = 0, ss = 0},
    (* TODO: simulate till the point of diminishing returns *)
    While[n < 5000, (* don't hardcode that *)
      x = payoff[myType, myAction, #[randType[]]& /@ strategies];
      n++; s += x; ss += x^2;];
    AbortProtect[psHash[myType, myAction, strategies] += {n, s, ss};
      (* TODO: maybe also update a global list for domain[psHash]
               since it's so expensive to call domain[psHash] a lot *)
      (* TODO: did it but this might be too expensive itself... *)
      If[psHash[myType, myAction, strategies] == {n, s, ss},
        psHashDomain = Union[psHashDomain, {{myType, myAction, strategies}}];
      ]
    ]
  ]

ps[myTypeList_List, myAction_/;Head[myAction]=!=List, strategies_List] :=
  Scan[ps[#, myAction, strategies]&, myTypeList]

ps[myType_/;Head[myType]=!=List, myActionList_List, strategies_List] :=
  Scan[ps[myType, #, strategies]&, myActionList]

(* note this does the type-action pairs with the least simulations first *)
(* TODO: could bias the time spent on each type-action pair so that they
         even themselves out. *)
(* TODO: for now, I just leave off the one that has the most simulations *)
ps[typeActionPairs:{{_,_}..}, strategies_List] := 
  Scan[ps[Sequence @@ #, strategies]&, 
       Drop[Sort[typeActionPairs, 
                 typeActionPairNeedierFunc[strategies]], -1]]

ps[myTypeList_List, myActionList_List, strategies_List] :=
  ps[Distribute[{myTypeList, myActionList}, List], strategies]


(* TODO: this should look at how big the 95% confidence intervals are and
         choose the type-action pair that has the biggest interval.
         But {0,0,0} should always be considered neediest. *)
(* typeActionPairNeedierFunc[strats][ta1,ta2] returns whether tp1 should be 
   simulated before tp2, ie, tp1 has fewer simulations under its belt so far. *)
typeActionPairNeedierFunc[strategies_List] := Function[{tp1, tp2},
  psHash[Sequence@@tp1, strategies][[1]] < 
  psHash[Sequence@@tp2, strategies][[1]]
]

(* tryActions[type, strategies, actionDelta] returns a list of actions to try 
   (returns {type,action} pairs where all the types are the same) for the 
   current type.  It decides on an action range that we're almost certain 
   contains the best action. *)
tryActions[type_, strategies_List, actionDelta_] := Module[{b, min, max, l},
  {b, {min, max}} = bestActionRange[type, strategies, confidence->1.-1/10^6];
 
(*
  l = Range[min, max, actionDelta];  (* shouldn't make it the whole range *)
  If[Last[l]=!=max, AppendTo[l, max]];
  If[Length[l]>=5, l = Drop[l, {3, -3}]];
  l = Union[l, {b}];
  {type, #}& /@ l
*)

  {type, #}& /@ Union[Range[min, max, actionDelta], {max}]
]

(* makeTypeActionPairs[typeDelta, actionDelta] constructs a list of type-action 
   pairs.  Options for minimum and maximum type can be specified, but only 
   matter if they are within the ranges set by minType and maxType. *)
makeTypeActionPairs[typeDelta_, actionDelta_, strategies_List, 
                    tMin_:-Infinity, tMax_:Infinity] := 
  Module[{start, t1, t2, ans},
    start = TimeUsed[];
    t1 = Max[minType, Min[maxType, tMin]];
    t2 = Max[minType, Min[maxType, tMax]]; 

    ans = tryActions[#, strategies, actionDelta]& /@ Range[t1, t2, typeDelta];

    Print["[makeTypeActionPairs: ", Plus@@(Length/@ans), " -> ", Length /@ ans,
(*
          Quotient[t2-t1+typeDelta, typeDelta], " types, ", 
          Length[ans], " pairs, ", 
          N[Length[ans]/Quotient[t2-t1+typeDelta, typeDelta]],
*)
          " pairs per type", 
          " in ", seconds2str[TimeUsed[] - start], "]"];   (* TODO *)

    Join @@ ans
  ]

(****************************************************************************)

(* showBestAction[myType, strategies] plots expected payoff vs myAction based 
   on psHash.  Options allow setting the confidence level to use in showing the
   range for the true expected payoff for given actions. *)
Options[showBestAction] = { confidence -> defaultConfidenceLevel, 
                            compareFuncs -> {}};
showBestAction[myType_, strategies_List, opts___] := 
Module[{opt, x, p1, p2, p3, t, best, min, max, reallyMin, reallyMax},
  opt[x_] := x /. {opts} /. Options[showBestAction];
  p1 = plotWithErrorBars[opt[confidence], minAction, maxAction,
                         makeData[myType, strategies], 
                         DisplayFunction->Identity];
  (* TODO: color code the dots based on confidence... *)
  {best, {min, max}} = bestActionRange[myType, strategies, 
                                       confidence->.95];  (* TODO hardcode? *)
  {best, {reallyMin, reallyMax}} = bestActionRange[myType, strategies,
                                                   confidence->1.-1/10^6];
                                       
  p2 = Graphics[{AbsolutePointSize[6],
         RGBColor[0,0,1],
         Point[{min, maxLikelihoodValue[psHash[myType, min, strategies]]}],
         Point[{max, maxLikelihoodValue[psHash[myType, max, strategies]]}],
         Point[{reallyMin, maxLikelihoodValue[psHash[myType, reallyMin, 
                                                     strategies]]}],
         Point[{reallyMax, maxLikelihoodValue[psHash[myType, reallyMax,
                                                     strategies]]}],
         RGBColor[0,1,0],
         Point[{best, maxLikelihoodValue[psHash[myType, best, strategies]]}]}];
  p3 = Plot[Evaluate[#[t]& /@ opt[compareFuncs]], {t, minAction[myType], 
                                                      maxAction[myType]}, 
                                                  PlotStyle->RGBColor[0,0,1],
                                                  DisplayFunction->Identity];
  Show[p1, p2, p3, PlotRange -> All, DisplayFunction -> $DisplayFunction]
     (* TODO: pass on any of opts except the ones 
              in Options[showBestResponse] to Show *)
]


maxLikelihoodValue[{n_, s_, ss_}] := If[n==0, 0, s/n]
maxLikelihoodValue[{x_, {n_, s_, ss_}}] := If[n==0, 0, s/n]


(* TODO: This is currently a very conservative estimate of the probability.
         call the maxLikelihood values a and b
         and let c be the midpoint between a and b, ie, (a+b)/2 
         This gives the probability that the true mean for a is less than 
           c times the probability that the true mean for b is greater than c.
         (so the true probability of a < b will be greater)
         If we could OR the above for all values of c from -inf to +inf, we'd 
           have the true answer... TODO!
         TODO: actually, let's just use the meanDifferenceTest adapted for
               when we only know {n,s,ss}...
*)
(* probLessThan[stats1, stats2] gives the probability that the true mean of 
   the distribution from which the sample statistics stats1 were taken is less 
   than the true mean of the distribution from which the sample statistics 
   stats2 were taken. *)
probLessThan[{n1_, s1_, ss1_}, {n2_, s2_, ss2_}] := Module[{c},
  c = (maxLikelihoodValue[{n1,s1,ss1}] + maxLikelihoodValue[{n2,s2,ss2}]) / 2;
  Which[n1 == 0 || n2 == 0,
    1/2,  (* TODO: does this make sense? *)
  probRange[n1,s1,ss1,c,c] == 1 && probRange[n2,s2,ss2,c,c] == 1,
    0,
  True,  
    probRange[n1, s1, ss1, -Infinity, c] * probRange[n2, s2, ss2, c, Infinity]
  ]
]

(* offset[n, me, list] finds me's position, adds n to that, and returns the 
   element at that position in the list, or the first (last) if that would 
   take us out of the list.  This will crash if me is not in list. *)
offset[n_, me_, list_List] := Module[{pos},
  pos = Position[list, me][[1,1]];
  list[[Max[1, Min[Length[list], pos + n]]]]
]

(* maxRange[conf, points] takes a set of x values with their goodnesses 
   expressed as {n, s, ss} and return a range of x values that has probability 
   conf of containing the best x -- actual return value is 
   {maximumLikelihoodMax, {lowerBoundOnMax, upperBoundOnMax}}. *)
maxRange[conf_, points:{{_, {_, _, _}}..}] := 
  Module[{sorted, likelyBest, candidates},
    sorted = Sort[points, #1[[1]] < #2[[1]]&];
      (* Print["sorted is ", First/@sorted]; *)
    likelyBest = argMax[maxLikelihoodValue, sorted];
      (* Print["likely best is ", likelyBest]; *)
    candidates = (* points we're not so sure are worse than the likelyBest *)
      Select[sorted, 
        (probLessThan[#[[2]], likelyBest[[2]]] <= conf 
         || #[[2,1]] < 4)&];   (* almost no trials for this point *)
    likelyBest = First[likelyBest];
    candidates = Append[First /@ candidates, likelyBest];
    sorted = First /@ sorted;
      (* Print["candidates are ", candidates]; *)
    {likelyBest, 
      {offset[-1, Min[candidates], sorted], 
       offset[+1, Max[candidates], sorted]}}
  ]


(* bestActionRange[myType, strategies] is similar to showBestAction but it 
   automatically looks at the graph and returns a range of actions that is 
   likely to contain the best action. (return value is of the same form as 
   maxRange) *)
Options[bestActionRange] = { confidence -> defaultConfidenceLevel};
bestActionRange[myType_, strategies_List, opts___Rule] := 
Module[{opt, x, b, min, max},
  opt[x_] := x /. {opts} /. Options[bestActionRange];
  {b, {min, max}} = maxRange[opt[confidence], makeData[myType, strategies]];
  (* TODO: baHash[myType, strategies] = {min, max} -- no, need higher conf *)
  {b, {min, max}}
]

(* showBestResponse[strategies] plots a best response strategy (a strategy is 
   a mapping from type to action) to the given opponent strategies. *)
Options[showBestResponse] = {confidence -> defaultConfidenceLevel,
                             compareFuncs -> {}};
showBestResponse[strategies_List, opts___Rule] := 
Module[{opt, x, p1, p2, p3, t, a, b},
  opt[x_] := x /. {opts} /. Options[showBestResponse];

  p1 = Plot[Evaluate[#[t]& /@ strategies], {t, minType, maxType}, 
            Frame -> True, Axes -> False, DisplayFunction -> Identity];

  p3 = Plot[#[t]& /@ opt[compareFuncs], {t, minType, maxType}, 
         Frame -> True, Axes -> False, PlotStyle->RGBColor[0,0,1],
         DisplayFunction->Identity];

  p2 = plotWithErrorBars[
         {#, bestActionRange[#, strategies, confidence -> opt[confidence]]}& /@
            allTypes[strategies], DisplayFunction->Identity];
   
  Show[p1, p2, p3, PlotRange -> All, DisplayFunction -> $DisplayFunction]
]

End[];   (* Private context *)
EndPackage[];
