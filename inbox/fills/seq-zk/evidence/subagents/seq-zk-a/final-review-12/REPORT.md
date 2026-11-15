# Final explicit-reader scan: unresolved-name review

Reviewer: seq-zk-a. Final proof revision d842dc8f681f6b89499129f5b64a50d0e4587935.
Read-only review of scan1.py, scan2.py, review_explicit.py, and the final-repair/explicit
inputs/results. All41scanned source files independently match the committed revision byte
for byte (source-revision-verification.json). No Lean/lake command or source edit was made
by this reviewer. Python scripts write only this final-review-12 evidence directory.

## Completed outcome

The raw scan contains1245items:868native-resolved theorem uses,6same-module definition
uses,and371LOCAL_OR_UNRESOLVED items. Its zero-foreign count alone was incomplete evidence
until those371items were reviewed. Every one is now classified source-locally and the
nonlocal aliases are checked by the lead's completed secondary native probe:

| Supplement category | Items |
|---|---:|
|Named local hypothesis, case, lambda, obtained value, or let|322|
|Anonymous local have proof named this|2|
|Inline typed show equality proof term|15|
|Local equality combined by Eq.trans|1|
|Public theorem/equality/iff/contract readers through aliases|29|
|Additional same-module inherited AbortRetry definitions|2|
|Still unexplained|0|

Thus the merged interpretation is897public theorem/reader items,8same-module definition
items,and340local/inline proof items. No foreign definition-body unfolding was found. All
eight same-module definition occurrences are in declarations marked UNCHANGED by the
base/final touched map. No newly added/changed declaration unfolds a foreign definition
explicitly in this scan. The raw scan2 output is retained unchanged; this is a separately
reported supplement, not a silent rewrite of its results.

## Native alias confirmation

The lead ran `.lake/seq-zk-rule10/final-repair/explicit/ExplicitAliases`; the retained log
`evidence/logs/final-explicit/final-explicit-aliases.log` contains all24requested canonical
names,EXPLICIT_ALIAS_DONE24,and EXIT0,with zero error: or error( diagnostics.22names have
native kind theorem and type_is_Prop=true; the only two definitions are AbortRetry.attempt
and AbortRetry.retry,with the same Defs module home as their explicit uses.

The initial conservative warning that proof-valued class/spec fields might have definition
kind was a probe-design precaution, not an observed issue. The pinned native result
actually classifies every queried proof field as theorem-kind. native-supplement-validation
records these exact results and probe/log hashes.

## Why the scanner left valid names unresolved

1. Export aliases are absent from the probe's raw env.constants string map. `mul_zero` and
   `zero_mul` are exported from MulZeroClass at Mathlib/Algebra/GroupWithZero/Defs.lean:77
   (field declarations35,37). Their canonical names MulZeroClass.mul_zero and zero_mul are
   theorem-kind public equality readers in the native result. `not_not` is exported from
   Classical at Mathlib/Logic/Basic.lean:188; Init/Classical.lean:141 declares the theorem.
2. Receiver notation needs the local receiver type. hA.advice_eq/hS.advice_eq resolve to
   Complexity.NUPPT.Uniform.advice_eq (Randomized/PPT.lean:300). The specification methods
   h.realCoinsEquiv_fst_ofFn,d.phase_take,and d.outV_eq resolve to their published
   PaddedProverSpec/PaddedVerifierSpec theorems. The13spec-field uses are public equality
   proof projections (first,rounds_eval,next,boundary; rounds_eq,first_eq,next_eq,terminal_eq,
   period,local_length), not attempts to unfold those projections' definitions. All are
   native theorem-kind/type-is-Prop=true.
3. List.mem_singleton.mp and List.prefix_iff_eq_append.mp apply the mp direction of public
   iff theorems to local membership/prefix proofs. Canonical List lemmas and Iff.mp were
   verified natively. hpV.trans hp combines two local equality proofs using Eq.trans;
   hpV is explicitly bound by congrArg at SequentialZK.lean:669.
4. `open AbortRetry in` appears at Defs.lean:588 before the following theorem's docstring.
   scan1.py only searches tactic-local opens inside the owning declaration span, so it
   misses this legal preceding local open. At636,648,the inherited simp arguments attempt
   and retry are owned AbortRetry.attempt/retry (defined at328,346 in that same file). At642,
   firstHit_map_getD_eq is the public AbortRetry theorem declared at460. These are not
   private copies and are not foreign-definition uses.
5. The inline keyword show is not a declaration name. The15full items are13arithmetic
   equality terms proved by ring/omega and two local funext h equalities. No foreign body
   is hidden in those terms. The two local this entries come from anonymous have:= at
   Defs.lean:472 and494 before their rw uses at474 and496.

## Source-local handling of ordinary local names

For322entries the review retains the enclosing compiled declaration and direct binding
evidence (have,let,set,by_cases,intro,obtained pattern,case/lambda binder,or typed premise)
strictly before the scanned use. No blanket “starts with h” rule was used. All322had a
direct binder match under a second stricter pass. The two anonymous-have cases were
reviewed manually and explicitly overridden. The exact occurrence, full rewrite item,
source context,and local binding lines are in native-validated-review.json. The original
proposed/unlocated intermediate files remain for provenance; resolved-review and native-
validated-review explicitly resolve both initial missing binder locations.

## Tool review and requirements

scan2.py correctly keeps LOCAL_OR_UNRESOLVED separate at32–33 and reports raw foreign
items only among resolved names at37–46. It cannot itself certify zero foreign unfolding
while unknown names remain. Its equation-target handling covers generated eq_N,eq_def,
eq_unfold heads; the original explicit-items inventory remains authoritative for those
lexer records. Any native-kind continuation must preserve both diagnostic forms error:
and error( and must require successful completion/exit, as done in the root logs here.

review_explicit.py is not generic for this fill: it hard-codes hash-sign SignatureScheme
aliases,an unrelated local-head whitelist,and writes .lake/hash-sign-rule10 paths. It should
not be executed unchanged or treated as resolving the371seq-zk unknowns. The present
supplement performs the corresponding source-specific review and canonical native check,
while leaving that archived tool untouched.

This explicit scan is one part of Rule10 evidence; it does not replace strict/coe A/B
irreducibility seals or their attribution. The lead's separate native sweeps/axioms/seals
remain the authority for implicit elaboration. No source correction is requested by this
review. All files produced here are indexed by receipt.tsv and lie outside the historical
frozen CP3 and post-CP3 audit receipts.
