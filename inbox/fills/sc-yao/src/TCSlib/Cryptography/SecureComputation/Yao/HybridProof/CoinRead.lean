/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time windows of a coin string

The window operations below take their offsets and widths in unary. They work on arbitrary
words, including words shorter than the requested window, by padding the missing bits with
`false`. The contracts therefore apply to the malformed inputs included in strategy efficiency.

## Main definitions

No new data representation is introduced.

## Main results

* `polyTimeComputable_window`: a padded window whose word, offset and width are polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (fixed blocks of the parties' random tapes).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing

/-- A padded window is polynomial-time when its word and its unary offset and width are:
`z ↦ List.ofFn (fun t : Fin (len z) => (w z).getD (off z + t) false)`.
The contract includes zero widths and windows extending beyond the word. -/
theorem polyTimeComputable_window {w : List Bool → List Bool} {off len : List Bool → ℕ}
    (hw : PolyTimeComputable w)
    (hoff : PolyTimeComputable fun z => List.replicate (off z) true)
    (hlen : PolyTimeComputable fun z => List.replicate (len z) true) :
    PolyTimeComputable fun z =>
      List.ofFn (fun t : Fin (len z) => (w z).getD (off z + t) false) := by
  have hdrop : PolyTimeComputable fun z => (w z).drop (off z) :=
    ((polyTimeComputable_pairDropPoly .var).comp (hoff.pairEncode hw)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
        PolyExpr.eval_var, List.length_replicate]
  have hp := EnsembleLemmas.polyTimeComputable_padL .var hlen hdrop
  refine hp.congr fun z => ?_
  simp only [PolyExpr.eval_var, List.length_replicate, ← EnsembleLemmas.ofFn_padFin_eq_padL]
  apply congrArg List.ofFn
  funext t
  rw [padFin_apply, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getD_eq_getElem?_getD]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
