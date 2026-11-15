# SimulatorMachine overlap, reuse and host record

The lead approved phasePrefix as a public mathematical semantic recursion, realized using the
published ColMachines.polyTimeComputable_loopState' host. No new control host, transition
machine, or private machine is built. PhaseView was copied as an authorized stable source;
its hash and independent compile log are retained. It was not edited; no agent-a olean copied.

Raw searches are in simulator-searches.log. Earlier Efficiency/WrappedVerifier searches cover
coin slicing, uniform output/layout combinators, and canonical prefix reencoding. No exact
normalized-prefix simulator was found in TCSlib or pinned Mathlib.

New declaration nearest relatives and reuse:
- phasePrefix / zero / succ / succ_simulate: public mathematical sequence of canonical
  normalized simulator calls, following the issued source sketch. Nearest repeated-simulator
  code is PerfectZKAbort.retry (ZeroKnowledge/Defs.lean:337) and attempt (:319): their input is
  fixed and output stops at the first success, rather than changing auxiliary prefix and
  accumulating normalized messages. S.simulate_eq, S.runAt_eq and S.runAtL readers are reused
  to match the published simulator convention exactly.
- length_phasePrefix: new exact i*k count obtained from public
  length_normalizePhaseMsgs (PhaseView.lean:~97) and List append/replicate length readers.
- length_le_of_mem_phasePrefix: new prefix bound obtained by induction from public
  length_le_of_mem_normalizePhaseMsgs (PhaseView.lean:~105) and empty fillers.
- length_encodeMsgs_phasePrefix_le: direct use of public
  CommitmentLemmas.length_encodeMsgs_le (CommitmentLemmas.lean:241), together with the two
  preceding prefix readers. No generic encoding-size proof is copied.
- encode_emptyMsgs_poly: counted emission of the fixed chunk pairEncode [] [] through public
  ColMachines.polyTimeComputable_flatMap_range (ThreeColoring/Machines.lean:~158).
  Core List.map_const' and flatMap_map identify the result with existing encodeMsgs_eq_flatMap.
  This generic encoding composition has no exact prior counterpart found by the searches.
- phasePrefix_poly: existing ColMachines.polyTimeComputable_loopState' (:101), unary arithmetic,
  GI.coinSlice_poly (GraphIsomorphism/EfficiencyRep.lean:376), agent-a's public normalized-view
  machine, phaseAux_poly, and NUPPT output/layout readers are reused. The only new invariant is
  the exact identity of the existing host's state with the encoded semantic prefix. Nearest
  concrete consumers are ThreeColoring proverRepStr_poly and PerfectZKAbort.retry_poly
  (Defs.lean:412); their fixed protocol/first-success outputs prevent direct reuse.
- exists_phaseSimulator: uses public NUPPT.ofPolyTimeUniform and its uniform/coins/activation
  readers. Nearest relative exists_retrySimulator (Defs.lean:433) uses n retries on the same
  input, whereas this simulator threads phaseAux data and emits the entire canonical view.

Promotion requests: phasePrefix and the simulator construction are source-specific and stay
in this helper. The small encode_emptyMsgs_poly composition could later move beside the shared
encoded-history machines. No frozen-file changes or scope requests are needed.
