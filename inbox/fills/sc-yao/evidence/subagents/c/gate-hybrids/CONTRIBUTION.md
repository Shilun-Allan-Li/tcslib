# Subagent c: two-stage gate hybrids

Source `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybrids.lean`. Namespace `...YaoHybridProof.GateHybrids`.
346 lines,35 source declarations,49 stored constants,width<=100,no sorry.

## Contract

rowWith/tableWith are new hybrid objects parameterized by assignment output
labels, with full equation readers. They specialize to the existing real and
FakeObjects rows/tables using those objects' public readers. tableWith_relabel
and tableWith_start reuse RelabelGarbling.garbledTable_relabel directly.

trueBit is gateOut(a XOR argument values) XOR output value. trueBit_zero uses
a supplied circuit-consistency equation; values_consistent derives that
equation from actual C.values via gateOut_eq and values_getD_gate.

outputBit cutoff phase is false at completed gates, additionally false on
current first-bit-true rows in phase1, and trueBit elsewhere. stageBit t uses
cutoff t/2 and phase t%2, with exact even/odd/start readers. tableWith_end is
exactly FakeObjects.table at stage2*gatecount, including empty circuits.

outputBit_first_unchanged proves only current first-bit-true rows can change
in substep1. outputBit_second_unchanged, for fanin<=2 and consistent values,
proves only current firstfalse/secondtrue rows can change in substep2. The
all-zero row is false at every phase; assignment_zero_of_two reuses fold
injectivity to avoid re-deriving Boolean assignment uniqueness. Current row,
completed gate, and future gate readers give the exact challenge labels.

## Reuse and overlap disclosure

Closest published relatives: Garbling.garbledRow_eq/garbledTable_eq; new
FakeObjects.row_eq/table_eq; RelabelGarbling.garbledTable_relabel;
DAGCircuit.values_getD_gate; gateOut_eq; CoinSeedRelabel.assignmentFold_injective;
RowFromCoins.assignmentFold_eq_two. These are reused through equations.
rowWith/tableWith parameterize the real/fake formulas by a label map, rather
than re-proving their semantic machinery. a/root explicitly approved this
independent generic object to keep FakeObjects stable. tableWith_congr is a
direct specialization of List.map_congr_left, not another list theorem.

SY5: unmerged sc-garble a73072f1 was searched for hybridRow/hybridTable/
gateHybrid/outputBit/rowWith/tableWith; no matching helper was found within
the searched source/delivery paths. Its assignmentFold_small overlap belongs
to the earlier CoinSeedRelabel report; this module consumes the proved public
injectivity result. No unmerged code/import or probability proof is copied.

## Verification

Normal07 PASS. Four whole-file Rule10 seals (A/B,strict/coe) PASS with
-DmaxErrors=0. Axioms-01 enumerates all49 stored constants: standard axioms
only,every closure sorried=[]. Both error forms counted. Style lint for
CoinSeedRelabel+GateHybrids reports0findings. Failed/source/raw logs retained.
Seal generator/runner are the previously provenance-recorded c/coin-seed tools
with only evidence path changes, originally adapted from sc-garble tools.

Lead must run final merged checks. No commits by this agent.
