# Existing Classes.phfeClass_eval_eq_quad proof draft

Status: exact-header/prose replacement, inspected but not natively elaborated. No live
source edits, Lean, lake, build, or Git commands. No helper or new import is proposed.

## Deliverable

`ClassesPhfeClassEvalEqQuad.lean.inc` preserves the complete current frozen docstring,
source tag, proof sketch, and existing theorem header. Only its admitted body changes.
A Python assertion matched the live block before replacement. One tactic block, no
admitted terms, maximum line width 81 columns.

## Reused APIs and proof route

- `phfeClass_eval` (Classes:402) and `quadClass_eval` (:508) read the two wire-class
  evaluations through their public readers, with the same coefficient/public words.
- `phfeEval_eq` identifies the typed diagonal evaluation with quadEval at two copies
  of the same private scalar vector.
- Core `congrArg₂` reduces the remaining typed evaluation equality to equality of its
  two private vectors. No public or private decoder-duplication helper is introduced.
- The now-proved `decodeResidues_block` (:160) reads each compared coordinate as a
  `listToNat` of its exact finite-product bit block, cast modulo p.
- `duplicatePrivateBits_eq` (:565) reads the duplicate's bit selection. The canonical
  `Equiv.symm_apply_apply` reader cancels its finite-product coordinate conversion.
- Mathlib `finSumFinEquiv_symm_apply_castAdd` and `_natAdd` select the first and
  second copies respectively; `Sum.elim_inl`, `Sum.elim_inr`, and `id_eq` leave the
  same original input bit at every within-block coordinate.

Both residue lists, natural values, and casts are therefore identical pointwise.
This is an equality for **arbitrary** words: no residue width, range, canonicality,
encoder-image, or prime assumption is added. Original words with aliases modulo p
remain valid, including values >=p. Dimensions/width zero work by the empty finite
index types. There are no admitted dependencies in these readers as inspected/reported.

Only published TCSlib and Mathlib/core equations are explicitly used; no class,
decoder, duplicate, finite equivalence, or generated defining equation is unfolded.
The candidate uses the original Fin.castAdd/Fin.natAdd split already in quadClass_eval,
so it adds no transport or concatenation representation.

## Actual searches/reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
rg -n -A 32 -B 8 'theorem phfeClass_eval_eq_quad|theorem duplicatePrivateBits_eq|theorem quadClass_eval |theorem phfeClass_eval |theorem decodeResidues_block' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
sed -n '216,250p' .lake/packages/mathlib/Mathlib/Logic/Equiv/Fin/Basic.lean
rg -n 'Equiv.symm_apply_apply|finSumFinEquiv_symm_apply_castAdd|finSumFinEquiv_symm_apply_natAdd' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticCorrect.lean TCSlib/Cryptography/Games/BitCodec.lean | head -20
rg -n 'congr 1 <;> funext|congr 1.*funext' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean | head -15
rg -n 'theorem id_eq|lemma id_eq|theorem congrArg₂' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init | head -15
```

The exact sum-equivalence inverse readers are at Mathlib Logic/Equiv/Fin/Basic:236
and :246. Core Init/Prelude:295 supplies `id_eq`. No missing coordinate reader or new
helper target was found necessary. The separate polynomial-completeness planning and
its further source searches are recorded in `ClassesPadOne-PLAN.md`.

## Validation limits

Static frozen prose/header equality, line width, one-block count, and no-admission
checks passed. Native elaboration (including the two binary congruence goals), standard
axiom checking, and inventory refresh remain with the root. No false statement,
semantic weakening, or mathematical obstruction was identified.
