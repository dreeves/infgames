(* Daniel Reeves
   Functions for doing Monte Carlo simulations.
*)

WriteString["stderr", "[MonteCarlo.m]"];

BeginPackage["MonteCarlo`", {"Util`",
                             "HypothesisTesting`"}];
                             (*
                             "Statistics`Common`DistributionsCommon`", 
                             "Statistics`ConfidenceIntervals`",
                             "Statistics`NormalDistribution`"
                             *)
(* All non-private symbols must be listed below... *)

(* TODO: how to decide what this should be?  200 was too low 
         for Equilibria.m *)
$MaxExtraPrecision = 256;

meanTable;  meanDiffTable;
plotWithErrorBars; plotStatList; plotStatList2;
distill;
mean; variance; varianceOfSampleMean; standardErrorOfSampleMean;
  stderr = standardErrorOfSampleMean;
sample;
meanCI; probRange; meanDiffTest;
mostSigFig;
round;
statusReport; mailStatus; mailStatus2; runSimulation; runSimulation2;


Begin["`Private`"];  (***************************************************)

cat = StringJoin@@(ToString/@{##})&;

meanTable::usage = 
"Show means, CIs, sample sizes, etc based on list of data triples (n,s,ss)'s.";
meanTable[stats_, str_:""] := Module[{dp, pos, spos},
  dp = 3; (* decimal places *)
  pos = First /@ Position[stats, {n_,_,_}/;n>0];  (* positions of nonzeros *)
  spos = Sort[pos, mean[stats[[#1]]] > mean[stats[[#2]]]&];
  (* mc = meanCI[.95, #]& /@ stats; *)
  cat["MEANS, 95% CIs, SAMP SIZES -- ", str, "\n",  (* Pr(X<=0) *)
   "-----------------------------------------------------------------------\n",
   table[
    Map[{#,
         ni[mean[stats[[#]]], dp], "  +/- ", 
         ni[-Subtract@@meanCI[.95,stats[[#]]]/2, dp],
         cat["  (", NumberForm[First[stats[[#]]], DigitBlock->3], ")"]
         (* ni[Last[Select[empiricalCDF[d], First[#] == 0 &]][[2]], 2] *)}&,
     spos]]]
]

meanDiffTable::usage = 
"Show mean difference tests for every pair given a 
 list of data triples (n,s,ss)'s.";
meanDiffTable[stats_, str_:""] := Module[{pos, spos},
  pos = First /@ Position[stats, {n_,_,_}/;n>0];  (* positions of nonzeros *)
  spos = Sort[pos, mean[stats[[#1]]] > mean[stats[[#2]]]&];
  cat["MEAN DIFF TESTS (p-values * 100) -- ", str, "\n",
    table@labeledMatrix[Table[If[i < j,
    ni[Round[100*meanDiffTest[stats[[spos[[i]]]], stats[[spos[[j]]]]]]], "-"],
    {i, 1, Length[pos] - 1}, {j, 2, Length[pos]}],
    Drop[spos, -1], Drop[spos, 1]]]
]

(* TODO make DisplayFunction an option like with the builtin plot functions *)
(* TODO colorize the error bars based on certainty *)
plotWithErrorBars::usage = 
"plotWithErrorBars[data] takes a list of data points in the form 
 {x, {y, {ymin, ymax}}} and plots them similarly to ListPlot.  
 plotWithErrorBars[conf, data] takes a confidence level and a list of data 
 points of the form {x, {n, s, ss}} where ymin and ymax for the error bars are 
 determined by finding the mean confidence interval based on n, s, and ss 
 (count, sum, and sum-of-squares).";
plotWithErrorBars[data:{{_?NumericQ, {_, {_, _}}}..}, opts___] := 
  Show[Graphics[convert /@ data], Frame -> True, opts]

convert[{x_, {y_, {a_, b_}}}] := Module[{line},
  line = Line[{{x, a}, {x, b}}];
  Which[NumericQ[y],
    {AbsolutePointSize[2], Point[{x,y}], RGBColor[1,0,0], line},
      (* TODO: was absolutepointsize[2] *)
  True,
    {RGBColor[1,0,1], AbsolutePointSize[0], Point[{x,a}], Point[{x,b}], line}]
]  (* TODO: was absolutepointsize[4] not 0 *)

errorBarify[conf_, minFunc_, maxFunc_][{x_, {n_, s_, ss_}}] := Module[{u, a,b},
  u = If[n<=0, Indeterminate, s/n];
  {a, b} = meanCI[conf, n, s, ss];
  {x, {u, {If[NumericQ[a], a, minFunc[x]], If[NumericQ[b], b, maxFunc[x]]}}}
]

plotWithErrorBars[conf_, minFunc_, maxFunc_,
                  data:{{_?NumericQ, {_?NumericQ, _?NumericQ, _?NumericQ}}..},
                  opts___] := 
  plotWithErrorBars[errorBarify[conf, minFunc, maxFunc] /@ data, opts]

plotStatList::usage = "plotStatList[conf, statList] plots a list of {n,s,ss} 
                      triples.";
plotStatList[conf_, statList_, opts___] := Module[{min, max},
  {min, max} = {Min[#1], Max[#2]}& @@ (Select[#, NumericQ]& /@ Transpose[
                                                meanCI[conf,#]& /@ statList]);
  plotWithErrorBars[conf, min&, max&, 
    Transpose[{Range[Length[statList]], statList}], opts]
]

plotStatList2::usage = "like plotStatList but with fancy labels and stuff...";
plotStatList2[statList_, title_:"", show_:True] := Module[{p,p2,p3},
  Off[Graphics::gptn];
  p = plotStatList[.95, statList, 
        DisplayFunction -> Identity];
  p2 = If[Length[statList] > 2, 
        ListPlot[mean /@ statList, PlotJoined -> True, 
          PlotStyle -> RGBColor[0.678396, 0.847102, 0.902005], 
          DisplayFunction -> Identity], 
        {}];
  p3 = Show[p2, p, Frame->True, Axes->False, GridLines->{None,Automatic},
         FrameLabel -> {"Agents", "Average Score"},
         PlotLabel -> title <> " -- " <> 
          If[Length[Union[First /@ statList]] == 1, 
            cat[NumberForm[statList[[1, 1]], DigitBlock -> 3], " trials"], 
            cat[NumberForm[Min[Select[First /@ statList, #>0&]], DigitBlock -> 3], "--", 
              NumberForm[Max[First /@ statList], DigitBlock -> 3], " trials"]], 
        DisplayFunction -> Identity];
  If[show, Show[p3, DisplayFunction->$DisplayFunction]];
  p3
]

distill::usage = "Takes a list of datapoints and converts to {n,s,ss}.";
distill[data_] := { Length[data], Total[data], Total[data^2] }

mean::usage = "The sum divided by the count.";
mean[{n_,s_,ss_}] := If[n<=0, Indeterminate, s/n]

variance::usage = 
  "Give the sample variance of a list of data but instead of needing the 
  whole list, just need the count, sum, and sum of squares.";
variance[n_,s_,ss_] := If[n<=1, Indeterminate, Max[0,(ss - n*(s/n)^2) / (n-1)]]
  (* due to rounding errors, the above could be negative which goofs up
     other stuff... TODO (see below too) a better way to handle this? *)

varianceOfSampleMean::usage = 
  "Give the variance of sample mean for a list of data but instead of 
  needing the whole list, just need the count, sum, and sum of squares.";
varianceOfSampleMean[n_,s_,ss_] := If[n<=0, Indeterminate, 
                                            Max[0, variance[n,s,ss] / n]]


standardErrorOfSampleMean::usage = 
  "Give the standard error of sample mean for a list of data but instead 
  of needing the whole list, just need the count, sum, and sum of squares.";
standardErrorOfSampleMean[n_,s_,ss_] := 
  Max[0, Sqrt[varianceOfSampleMean[n,s,ss]]]

sample::usage = "A corollary of Fisher's Theorem is that sample mean minus
  mean, divided by square root of, sample variance over n, has t-distribution
  with n-1 degrees of freedom.  
  In other words, we can estimate a distribution for the mean.";
sample[{n_, s_, ss_}, scale_:1] := Which[
  n <= 0, Indeterminate,
  n <= 1000, 
    mean[{n,s,ss}] - Random[StudentTDistribution[n-1]] *
      Sqrt[variance[n,s,ss]/(n*scale)],
  True,  (* same as NormalDist[mean,varianceOfSampleMean] *)
    mean[{n,s,ss}] - Random[NormalDistribution[0,1]] *
      Sqrt[variance[n,s,ss]/(n*scale)]]

Off[StudentTCI::"badse"];  (* warning when standard error is 0 *)

meanCI::usage = 
  "Give a confidence interval for the mean of a list of data but instead 
  of needing the whole list, just need the count, sum, and sum of squares.";
meanCI[c_, n_, s_, ss_, cutoff_:1000] := Which[
  n <= 0,
    {Indeterminate, Indeterminate},
  n <= cutoff, 
    StudentTCI[s/n, standardErrorOfSampleMean[n,s,ss], n-1, 
                                              ConfidenceLevel -> c],
  True,
    NormalCI[s/n, standardErrorOfSampleMean[n,s,ss], ConfidenceLevel -> c]]
meanCI[c_, {n_, s_, ss_}, cutoff_:1000] := meanCI[c, n, s, ss, cutoff]

(* TODO: the case of 0 standard error; is this the right thing to do? *)
probRange::usage = 
  "Given the sample size (n), the sum of the xi's, and the sum of the 
  squares of the xi's, and a range (a-b), return the probability the true 
  mean is in the range.  If above cutoff then use a normal distribution 
  instead of a t distribution.";
probRange[n_, s_, ss_, a_, b_, cutoff_:1000] := 
  If[n<=0, Indeterminate,
    Module[
      {u = s/n, se = standardErrorOfSampleMean[n, s, ss]},
      Which[
        se===Indeterminate || se==0, 
          If[a<=u<=b, 1, 0], 
        n <= cutoff,
          CDF[StudentTDistribution[n-1], 
            If[se===Indeterminate || se==0, Sign[b-u]*Infinity, (b-u)/se]] - 
            CDF[StudentTDistribution[n-1], 
                If[se==0 || se===Indeterminate, Sign[a-u]*Infinity, (a-u)/se]],
        True,
          CDF[NormalDistribution[u,se], b] - CDF[NormalDistribution[u,se], a]]
]]


meanDiffTest::usage = 
  "Give the OneSidedPValue for the mean difference test for 2 lists of
   numbers but instead of needing the actual lists, just needs the 
   length, sum, and sum of squares of the lists.";
meanDiffTest[{n1_, s1_, ss1_}, {n2_, s2_, ss2_}, cutoff_:10^6] := 
  If[n1<=1 || n2<=1, Indeterminate,
    Module[
      {delta, v1, v2, pooledvar, dof, test},
      delta = s1/n1 - s2/n2;
      v1 = variance[n1, s1, ss1];
      v2 = variance[n2, s2, ss2];
      pooledvar = v1/n1 + v2/n2;
      dof = pooledvar^2 / ((v1/n1)^2/(n1 - 1) + (v2/n2)^2/(n2 - 1));
      test = delta / Sqrt[pooledvar];
      If[dof <= cutoff,
        OneSidedPValue /. StudentTPValue[test, dof],
        OneSidedPValue /. NormalPValue[test]]
]]


mostSigFig::usage = 
  "Takes a real number and retuns the place of the most significant 
  digit -- eg, .0123 -> 1/100 or 12.34 -> 10";
mostSigFig[num_] := Module[{n = Abs[num], place},
  Which[n >= 1,
    For[place = 1, place <= n, place *= 10];
    Return[place/10],
  True,
    For[place = 1/10, place > n, place /= 10];
    Return[place] 
  ]
] 


(* could modify the builtin Round to take an optional 2nd argument. *)
round::usage = 
  "Rounds n to the nearest place -- eg, round[123,10] -> 120 or 
  round[1.0987,1/100] -> 1.10";
round[n_?NumericQ, place_] := With[{result = Round[n/place] * place},
  (* TODO: figure out how to keep it from rounding eg 2 to 2.000000001 *)
  If[Chop[result-n] == 0, n, result];   
  result
]
round[l_List, place_] := round[#,place]& /@ l
round[Indeterminate, _] := Indeterminate

statusReport::usage = 
  "Given n, sum, and sum-of-squares (and optionally a predicted mean), 
  returns a big string reporting things like how many digits in 
  the mean value can be considered significant.";
statusReport[n_, s_, ss_, predicted_:0] := Module[
  {str, u = If[n<=0, Indeterminate, s/n], i, place, p, x, a, b},

  If[u === Indeterminate, Return[cat["Invalid n: ", n, "\n"]]];

  str = cat[
    "n: ", NumberForm[n, DigitBlock->3], "\n",
    "{n, sum, sumOfSqs}: {", ni[n], ", ", ni[s], ", ", ni[ss], "}\n"];

  If[s === 0 && ss === 0, Return[str]];

  str = str <> cat[
    "mean: ", ni[u], "\n",
    "std err of samp mean: ", ni[standardErrorOfSampleMean[n,s,ss]], "\n",
    "95% mean CI: ", ni[meanCI[.95,{n,s,ss}]], "\n",
    "\n",
    "LOG OF PLACE, RANGE, WHAT RANGE ROUNDS TO, PROBABILITY OF IN RANGE\n",
    "\n",
    StringPadRight["predicted: ", 48], ni[predicted], "\n",
    StringPadRight["sample mean = max likelihd estimate: ", 48], ni[u], "\n",
    "\n"
  ];

  place = 1000 * mostSigFig[u];
  For[i = 1, i <= 10 || place > 1*^-20, place /= 10; i++,
    x = round[u, place];
    a = round[x - place/2, place/10];
    b = round[x + place/2, place/10];
    p = probRange[n,s,ss, a, b];
    str = str <> cat[
      StringPadLeft[ni[Log[10,place]], 3], " ", 
      StringPadRight[{ni[a],ni[b]}, 43], " ", 
      (* TODO: make x have the appropriate number of trailing 0s *)
      StringPadRight[ni[x], 20], 
      " ", ni[round[p,1*^-8]], "\n"];
  ];

(*
  str = str <> cat[
    "\n\n",
    "50%CI:     ", ni[meanCI[.50, n,s,ss]], "\n",
    "55%CI:     ", ni[meanCI[.55,n,s,ss]], "\n",
    "60%CI:     ", ni[meanCI[.60,n,s,ss]], "\n",
    "65%CI:     ", ni[meanCI[.65,n,s,ss]], "\n",
    "70%CI:     ", ni[meanCI[.70,n,s,ss]], "\n",
    "75%CI:     ", ni[meanCI[.75,n,s,ss]], "\n",
    "80%CI:     ", ni[meanCI[.80,n,s,ss]], "\n",
    "85%CI:     ", ni[meanCI[.85,n,s,ss]], "\n",
    "90%CI:     ", ni[meanCI[.90,n,s,ss]], "\n",
    "95%CI:     ", ni[meanCI[.95,n,s,ss]], "\n",
    "99%CI:     ", ni[meanCI[.99,n,s,ss]], "\n",
    "99.5%CI:   ", ni[meanCI[.995,n,s,ss]], "\n",
    "99.9%CI:   ", ni[meanCI[.999,n,s,ss]], "\n",
    "99.99%CI:  ", ni[meanCI[.9999,n,s,ss]], "\n",
    "99.999%CI: ", ni[meanCI[.99999,n,s,ss]], "\n"
  ];
*)

  Return[str];
]


mailStatus::usage = 
  "mailStatus[tag,n,s,ss, n0, start, predicted] sends myself email 
  about the status of the monte carlo simulation.";
mailStatus[tag_, n_, s_, ss_, n0_, start_, predicted_:0] := 
Module[{u = s/n, subj, bod},
  subj = cat[
    tag, 
    " trial ", NumberForm[n0, DigitBlock->3], ": ", ni[u],
    " (", seconds2str[AbsoluteTime[]-start], ")"
  ];
  bod = cat[
    "time: ", seconds2str[AbsoluteTime[]-start], "\n", 
    statusReport[n, s, ss, predicted]
  ];

  pout["SUBJECT:\n", subj, ">\n\nBODY:\n", bod, ">\n"]; 
  mail[subject -> subj, body -> bod<>"\n\n"<>SYSTEMINFO]; 
]

(* TODO: a quick attempt at generalizing this (see runSimulation2) *)
mailStatus2::usage = "TODO see above";
mailStatus2[tag_, datList_, n0_, start_] :=
Module[{uList, subj, bod},
  uList = (#[[2]]/#[[1]]&) /@ datList;
  subj = cat[
    tag,
    " trial ", NumberForm[n0, DigitBlock->3], ": ", ni[uList[[1]]],
    "... (", seconds2str[AbsoluteTime[]-start], ")"
  ];
  bod = cat[
    "time: ", seconds2str[AbsoluteTime[]-start], "\n",
    (cat @@
      (statusReport@@#& /@ datList))
  ];

  (* pout["SUBJECT:\n", subj, ">\n\nBODY:\n", bod, ">\n"]; *)
  mail[subject -> subj, body -> bod<>"\n\n"<>SYSTEMINFO];
]


(* TODO: if the sum and sum-of-squares are zero, does this now work? *)
(* TODO: I see a lot of divide-by-zero warnings even though it doesn't 
         seem to matter. *)
runSimulation::usage = 
  "runSimulation[trialFunc, tag, stateFile, processIdFile, predicted] 
  runs a monteCarlo simulation, logging the processID in 
  processIdFile -- sending an abort will trigger an update via email.  
  stateFile is where it stores its state
  so that multiple processes can work in parallel, or so it can resume 
  if the process is killed.  tag is just a string identifying the 
  experiment.";
SetAttributes[runSimulation, HoldFirst];
runSimulation[trialFunc_, tag_, stateFile_, processIdFile_, predicted_:0] := 
Module[{register, n, s, ss, start, n0, state, x},
  registerProcess[processIdFile, cat["(", tag, ")"]];

  {n, s, ss} = {0, 0, 0};
  If[FileInformation[stateFile] === {}, lockPut[{n, s, ss}, stateFile]];
  start = AbsoluteTime[];

  (* TODO: maybe it should always interrupt on abort, and just say Infinity
     seconds if you want it to *only* interrupt on abort... *)
  interruptedWhile[
    abort, 
      Run["lockfile " <> stateFile <> ".lock"];  (* TODO: use lockFile *)
      n0 = n;
      state = Get[stateFile];
      assert[MatchQ[state, {_?NumberQ, _?NumberQ, _?NumberQ}], 
             cat["stateFile: ", InputForm[state]]];
      {n, s, ss} += state;
      Put[{n, s, ss}, stateFile];
      Run["rm -f " <> stateFile <> ".lock"];
      mailStatus[tag, n, s, ss, n0, start, predicted];
      {n, s, ss} = {0, 0, 0},
    True,
      x = trialFunc;
      n++; s += x; ss += x^2;
  ];
]

update[{n_,s_,ss_}, x_] := {n+1, s+x, ss+x^2}

(* TODO: a quick attempt at generalizing runSimulation for a trialFunc
         that returns a list of values instead of just one.  *)
runSimulation2::usage = "TODO see above";
SetAttributes[runSimulation2, HoldFirst];
runSimulation2[trialFunc_, n_, tag_, stateFile_, processIdFile_] :=
Module[{register, datList, start, n0, state, xList},
  registerProcess[processIdFile, cat["(", tag, ")"]];

  datList = Table[{0, 0, 0}, {n}];
  If[FileInformation[stateFile] === {}, 
    lockPut[datList, stateFile],
    perr["WARNING: STATEFILE ", stateFile, " EXISTS (", 
      removeDups[Get[stateFile][[All,1]]], " trials/sample, ", 
      Length[Get[stateFile]], " samples)\n"]];
  start = AbsoluteTime[];

  interruptedWhile[
    abort,
      Run["lockfile " <> stateFile <> ".lock"];  (* TODO: use lockFile *)
      n0 = datList[[1,1]];
      state = Get[stateFile];
      assert[MatchQ[state, {{_?NumberQ, _?NumberQ, _?NumberQ}..}], 
             cat["stateFile: ", InputForm[state]]];
      datList += state;
      Put[datList, stateFile];
      Run["rm -f " <> stateFile <> ".lock"];
      mailStatus[tag, Sequence@@datList[[Random[Integer,{1,Length[datList]}]]],
        n0, start]; 
      plotStatList2[datList];
      datList = Table[{0, 0, 0}, {n}],
    True,
      xList = trialFunc;
      datList = MapThread[update[#1, #2]&, {datList, xList}];
  ];
]


(* nah, don't want this; maybe some kind of addPoint thing *)
(*
avgValue::usage = "TODO";
SetAttributes[avgValue, HoldRest];
avgValue[interruptFreq_, interruptBody_, expr_] := Module[{i,s,ss,x},
  i = 0;
  s = 0; 
  ss = 0;  
  interruptedWhile[interruptFreq, interruptBody, True,
    i++;
    x = expr;
    s += x;
    ss += x^2;
  ]
]
*)

End[];   (* Private context *)
EndPackage[];
   
