# SuffixMachine overlap and existing-host record

The lead explicitly approved a new generic per-step PT leaf and arbitrary-start/prefix suffix,
while preserving every prior stable helper byte. Raw searches are in suffix-machine-searches.log.
The semantic recursion uses the published ColMachines.polyTimeComputable_loopState' host;
no host implementation, transition table, private host or control machine is copied or added.

Every new declaration and nearest relative:
- phaseStep / phaseStep_eq: the append formula is the one displayed inside public
  phasePrefix_succ (SimulatorMachine.lean:71), generalized from its fixed earlier prefix to
  arbitrary pre and phase index j. It also matches the normalized typed-coin update simStep
  (lead's PrefixFolds.lean:64; public simStep_eq:71) when the selected full coin block equals
  List.ofFn of the typed coin. Here arbitrary raw tapes, including short/beyond-tape blocks,
  require S.runAtL rather than the typed S.simulate interface. The existing typed update
  cannot directly express this required total raw-tape function. No existing definition is
  unfolded: the new definition has its own complete equation reader.
- length_encodeMsgs_phaseStep_le: nearest bound is
  length_encodeMsgs_phasePrefix_le (SimulatorMachine.lean:~139) for an initially empty chain.
  That bound cannot retain an arbitrary initial prefix with unbounded individual messages.
  The new additive bound directly reuses public normalized-message encoding bounds,
  CommitmentLemmas.length_encodeMsgs_le (:241), and encodeMsgs_append (:233).
- phaseStep_poly: explicitly overlaps the unexported local upd/haux/hcoins/hsim/hnorm/hfill
  assembly inside phasePrefix_poly (SimulatorMachine.lean:~155--232). That assembly is not
  a reusable published declaration. The new public general leaf is re-derived from the same
  published NUPPT output/layout, GI.coinSlice_poly, phaseAux_poly, phase-view normalization,
  unary arithmetic and existing encode_emptyMsgs_poly readers. No private lemma is referenced
  or copied. This overlap is intentional and disclosed; a future extraction can make the old
  whole-prefix proof consume the new general leaf without changing stable bytes now.
- phaseSuffix / phaseSuffix_zero / phaseSuffix_succ: nearest recursion is phasePrefix
  (SimulatorMachine.lean:54), which fixes start=0 and pre0=[]. The new arbitrary start and
  initial prefix cannot be recovered from that specialized semantic definition. The recursion
  is a public mathematical specification and instantiates an existing host below.
- length_encodeMsgs_phaseSuffix_le: generalizes the empty-initial prefix encoding bound by
  retaining |encodeMsgs pre0| additively. It uses the new step bound; no bound on initial
  individual messages or on start/count is assumed.
- phaseSuffix_poly: nearest proof is phasePrefix_poly and its canonical encoded-prefix loop
  invariant. Both directly instantiate the published orbit-bounded counted-loop host
  (ThreeColoring/Machines.lean:101), without copying that host. The old theorem's fixed
  empty prefix, start0 and polynomial Q evaluated at |X| cannot supply arbitrary encoded H,
  unary Start and Count. The new envelope also includes H's polynomial output size and the
  unary Count's polynomial output bound. Shared canonical decoding and loop equations are
  reused as published readers.
- phaseSuffix_raw_poly: direct specialization of the new generic suffix theorem through
  the existing public canonical reencoding machine; no decoder or normalization proof is
  duplicated, and malformed prefix words are interpreted by total BinArith.decWords.
- phaseSuffix_zero_nil: new compatibility equation, directly reusing the public zero/succ
  readers for both semantic recursions and the new phaseStep equation. It records exactly
  the specialization relationship to the stable whole-prefix API.

Future promotion/refactor request: promote phaseStep_poly as the common general normalized
phase leaf, and refactor the existing phasePrefix_poly local assembly to consume it. The old
semantics can later use phaseSuffix_zero_nil. Current stable files remain unchanged as ordered.
No frozen-file edit, scope request, new Mathlib root, or host addition is needed.
