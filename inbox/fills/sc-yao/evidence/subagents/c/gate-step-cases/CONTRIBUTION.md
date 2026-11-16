# Subagent c: present or unchanged gate-clock cases

Source `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateStepCases.lean`. Namespace `...YaoHybridProof.GateStepCases`.
91 lines,width<=100,2 public/14 stored theorems including arithmetic
auxiliaries. No definitions,admissions or new attributes.

## Contract

step_cases_exact says each t<2*gatecount either has identical full stageBit
families at t and t+1, or has an actual gate i and argument p with
i.val=t/2,p.val=t%2,t=2*i.val+p.val,p.val<2.
step_cases drops the quotient/remainder equalities for the requested simpler
equality-or-actual-argument interface.

When the argument is missing,remainder0 forces arity0 and invokes
SelectedFields.stage_first_of_arity_zero. Remainder1 forces arity<=1 and
invokes stage_second_of_arity_le_one with the supplied consistency/fanin
hypotheses. No dummy or arbitrary selected wire is introduced. Empty gate
lists are covered by the empty clock bound.

The existing SelectedFields.sample_eq_of_stageBit_eq already has the exact
requested complete-sample transport. Root explicitly requested direct reuse,
so no redundant wrapper or semantic definition was added here.

## Reuse and overlap

The only case-specific content is quotient/remainder arithmetic and the two
existing missing-argument equations. No probability machinery or another
real/fake message/seed is defined or re-derived. This is a consumer-specific
composition of the public stage readers, not a general probability/list lemma.
SelectedStep can consume t=2*i+p.val directly for its two-neighbor frame.

## Verification

Normal03 PASS,style-lint-03 reports0findings. Four whole-file strict/coe by
evalA/B seals PASS with -DmaxErrors=0. Axioms-01 enumerates all14 stored
constants,standard axioms only,every transitive closure sorried=[]. Both
error forms counted; the original failed arithmetic/binder probe is retained.
No source changes after normal03.

Interim normal03 source+matching olean is byte-identical to final source:
/private/tmp/sc-yao-c-gatestepcases-api-normal03-resume3/.
Seal runners are the provenance-recorded c/selected-fields tools with path
changes only. Root reruns final merged checks. No child commits/frozen edits.
