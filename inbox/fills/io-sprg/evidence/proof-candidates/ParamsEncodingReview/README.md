# Params14 / Encoding17 / fixed-width review — READ ONLY, NOT RUN

No source edits, Lean/lake/build/cache, git mutation or agent spawn. Reviewed all
14 Params bodies,17 Encoding bodies, both fixed-width helper bodies, current
source signatures and pinned Core/Mathlib APIs. No false mathematical obligation
or definite API-name error was found. This is text review, not elaboration.

## Priority correction: foundational placement

policy.md section1 explicitly says foundational area helpers belong in Basic.
This supersedes the earlier first-use Encoding placement suggestion. Stage
  TCSlib/Cryptography/Obfuscation/StructuredSeed/Basic.lean
with exactly the existing Uniform import. Basic.lean here is a TACTIC-FREE
skeleton: two intentional term-level sorry placeholders; do not land them.
Use the existing FixedWidthList proof bodies one invocation at a time and check.

The proposed helper interfaces exactly preserve the dependent Encoding and
Reduction calls. In particular injection keeps f IMPLICIT and arguments
  hf, width, hwidth;
length keeps f EXPLICIT and arguments
  f, width, hwidth, xs.
Keep alpha : Type, as in the owner BoolCircuit.encodeList. Do not generalize
to Type* without changing the imported code's universe-zero domain.

Owned graph: Basic -> Uniform, Encoding -> Basic and Params -> LPN -> Uniform.
This is acyclic; Reduction.LPN sees Basic through Hybrids/Samplers/Encoding.
Do not add Basic to LPN merely to cover Raw.encDraw: that different Nat.bits
selector code is variable width and remains a separate closed-pair proof.

Root-owned follow-up for a real helper addition: import Basic in Encoding;
import/list Basic in the StructuredSeed facade (policy says every child);
record new helper/module and rerun collector/canonical seals for its coverage.
Basic has only theorems, so it introduces no definition-reader obligation.
The static Uniform closure is a subset of the current Encoding closure: ZERO
new external modules/Mathlib roots. No forbidden/heavy emitter or BinaryArith
import is needed. The new owned module itself is naturally new seal inventory.

## Concise API/syntax review

| Location | Assessment / practical correction if needed |
|---|---|
|Params D_pos|Nat.div_pos_iff expects 0<denominator AND denominator<=numerator; the candidate gives exactly 0<2 and2<=d+1.|
|Params four inverse bodies|PadQuad.nu_eq/nu_pow_le/nu_le/le_nu match the current numeric search exactly. Nat.pow_le_pow_iff_left needs exponent!=0; one_le_iff_ne_zero supplies it. Nat.pow_mul DOES exist as a protected Core theorem. Keep normalization simp restricted to the published owner readers.|
|Params le_n / le_log_n|Nat.le_pow takes positive exponent; both supplied exponents are positive. le_log_n uses threshold2^c and Nat.le_log_of_pow_le; no real-log proof is needed. Current source declaration order puts le_n before le_log_n.|
|Params Gamma_le_B|Highest-risk syntax: IsLittleO composition/cast lambdas and logb_pow normalization. All names exist. Real.natLog_le_logb is UNCONDITIONAL in a,b, so no missing n>0 or base hypothesis. Real.logb_pow is also unconditional; its D*(E*log) expression matches the target after mul_assoc. If cast rw becomes brittle, name separate hncast : (n k:Real)=((k:Real)^E)^D via readers, then rewrite logb through hncast. The existing final quotient argument and W>0 are sound.|
|Encoding W_le_ell_add_one|Only analytic body. Both ell=0 and positive ell branches are valid. If Rat.cast_le inference at the exponent bound fails, name hdelta1 : (P.δ:Real)<=1 and prove it with exact_mod_cast P.δ_lt_one.le, or use public Rat.cast_le_natCast (K:=Real)(n:=1). Then feed hdelta1 directly to rpow_le_rpow_of_exponent_le. Do not alter the statement or omit the zero branch.|
|Encoding B_le_bucketBound|The quotient<=m*k assertion is valid even m*k=0. div_lt_iff_lt_mul matches the supplied strict numerator bound. Nat.le_mul_of_pos_right and Nat.le_add_right_of_le names/types match.|
|Encoding count bounds|The seed/private double-copy counts and idxBound constant6 match current definitions. No missing separator/tag correction.|
|Encoding injections|pairEncode_injective implicit arguments really are a1/a2; the existing owner uses this style too. Modular vector/matrix injection take explicit width then modulus<=2^width, as supplied. ZMod.val_injective takes modulus explicitly.|
|Encoding helper width inference|Implicit f for injection is inferred from helem; explicit f for length matches the local encoder by let reduction. If inference fails, pass (f:=f) explicitly rather than changing the helper order. Noise pair width is2*(ell+1)+2+(kappa+1); OneDraw includes BOTH final false markers correctly.|
|Encoding idx length omega|hG, hBM and hNL contain the exact nonlinear products treated as atoms by omega; encodeMatrix_length is rows*columns*width, matching hNL. If normalization leaves association mismatches, normalize those specific products with Nat.mul_assoc before omega; no larger generic length lemma is needed.|
|FixedWidthList injection|Its induction is correctly generalized: ys is introduced inside each induction case. Core List.append_inj takes code equality FIRST and equal left lengths SECOND, exactly as used. List.cons.inj h returns head/tail equalities. Zero width is valid.|
|FixedWidthList exact length|Nil contributes1; cons contributes width+1. Nat.succ_mul plus omega matches the current List.length_cons convention. No positivity/nonempty assumption is needed.|

These are conditional mechanical suggestions, not claims that a known compiler
error occurred. Root currently owns the actual Params checks and may prefer
its already-passing spellings. No replacement proof was run here.

## Reuse / overlap

The imported public helpers are adopted directly: BoolCircuit.encodeList_nil/cons,
Core List.append_inj/List.cons.inj, length lemmas and Nat.succ_mul.
Uniform.lean's private PrefixFree(:87), encodeList_prefixFree(:158) and generic
length_encodeList_le(:234) are conceptual overlaps, NOT callable public APIs.
Do not access generated private names or recreate a general prefix predicate.
The proposed statements are constant-width specializations: list injectivity and
an exact length equality. The current helper bodies use only the public readers.

Public encodeList_eq_flatMap in UniformTableauEmitter exists but is outside the
current needed closure and introduces heavier machinery; it is not needed or
reproved. The public AdjWalk generic length bound likewise is not imported or
restated. Lamport's list injection uses a different nested-pair code, and matrix
injection uses untagged flattened rows, so neither proves these tagged-list facts.
See ../FixedWidthList/README.md for original full searches and ../RawLPNVariableWidth
for the separate variable-width selector case. Required exact?/apply? searches
remain root's pending work before landing new helper declarations.
