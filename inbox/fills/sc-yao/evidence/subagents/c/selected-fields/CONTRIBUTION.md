# Subagent c: selected-fill field and stage support

Source `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SelectedFields.lean`. Namespace `...YaoHybridProof.SelectedFields`.
320 lines,width<=95,20 source/30 stored theorems incl generated auxiliaries.
No definitions,admissions,simp attributes or frozen-file changes.

## Contract

keyAt_of_label_ne specializes SelectedSeed.fill_keyAt at labels other than
(u,true), including default vertices. keyAt_false and keyAt_of_ne give the
false-key and unrelated-vertex cases. decodePair_fill keeps arbitrary-result
decoding pairs at unrelated output vertices. activeAnswers_fill preserves
every false-key answer vector, with arbitrary start/count and no width>0.

message_tail_stage_eq removes the stage-dependent table head via public
message and pair readers. message_tail_fill preserves the entire encoded
key/pair tail under fill when every output vertex differs from u. It needs
no encryption assumption or key-value inequality.

outputBit_plaintext_ne_of_lt composes GateOccurrences.hybrid_plaintext_ne
with the completed-gate reader. outputBit_plaintext_ne obtains its bound
from selected_wire_lt. Even,odd,next-stage corollaries expose the exact
symbolic output-label inequality used by selected-key reconstruction.

stage_first_of_arity_zero proves full stage-label equality2i→2i+1 without
any selected wire. stage_second_of_arity_le_one proves2i+1→2i+2 equality
from fanin<=2 and wire-value consistency, again without an arbitrary u.
message_eq_of_stageBit_eq and sample_eq_of_stageBit_eq transport these
label-family equalities to exact message/view sample equality.

selectedPosition_none_bit/getD specialize the published selected-position
characterization. stage_first_unselected and stage_second_unselected use
these readers at an actual argument p with p.val=0/1. Other gates are
unchanged; the current argument bit must be false. The second-step theorem
uses the existing consistent-zero-row argument. Missing-argument branches
remain separate and never fabricate a selected key.

## Reuse and overlap disclosure

No general probability result, protocol, real/fake message or seed is
redefined. Existing SelectedSeed.fill_keyAt/fill_perm/key_other were searched
first; this module reads fill_keyAt directly rather than repeating its
inside/default-region proof. Active-answer and decoding-pair equations are
read through FakeObjects readers. Message/view equations use the published
GateHybridMessage and pair readers.

The symbolic acyclicity inequality is reused directly from GateOccurrences,
not re-derived. Unselected-row equalities reuse GateHybrids.first/second
unchanged support. The small-arity cases use List.getD_eq_default; encoded
bit lookup uses getD_eq_getElem/getElem_ofFn. No general list lemma is copied.
The new None-bit consequence is a direct specialization of the existing
selectedPosition_eq_some_iff. These are within-unit consumer specializations;
no additional sc-garble/sc-compose/#318 general result is re-derived.

## Verification

Normal01 through15 all PASS. style-lint-15 reports0findings. All four whole
file seals A/B by strict/coe PASS with -DmaxErrors=0. Axioms-01 enumerates
all30 stored constants,standard axioms only,every closure sorried=[].
Both error forms counted and all raw logs/source versions/manifests retained.
Seed-history-resume3 was supplied by root and left intact as provenance.

The normal15 API snapshot source+matching olean is byte-identical to final
source: /private/tmp/sc-yao-c-selectedfields-api-normal15-resume3/.
Seal tools are the provenance-recorded c/tape-values tools with path changes.
Root reruns final merged checks. No child commits.
