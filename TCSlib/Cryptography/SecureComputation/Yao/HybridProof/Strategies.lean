/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficient first-message and reply strategies

The existing interactive-layout machine constructor applies to arbitrary histories.
These contracts package its two uses in an Alice-first, two-message protocol.

## Main definitions

There are no new definitions.

## Main results

* `firstThenEcho_efficient`: compute the empty-history message and echo a later message.
* `reply_efficient`: compute a reply from the first received message.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Definition 155.1 and Protocol 162.6.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing TCSlib.Cryptography

/-- A strategy that computes `first x z r` on the empty history and echoes the first
received message on every nonempty history is efficient if its first-message map is
polynomial-time on the interactive machine layout. [PS10, Definition 155.1]
`S.Efficient`.

**Proof sketch.** Test whether the encoded history is empty. The two branches are the
given polynomial-time map and the first projection of the encoded history. Apply the
existing generic strategy constructor and its canonical-layout readers. -/
theorem firstThenEcho_efficient (S : Strategy)
    (first : List Bool → List Bool → List Bool → List Bool)
    (hNil : ∀ x z r, S.next x z r [] = first x z r)
    (hCons : ∀ x z r a hist, S.next x z r (a :: hist) = a)
    (hFirst : PolyTimeComputable fun w => first (GI.argX w) (GI.argZ w) (NUPPT.inCoins w)) :
    S.Efficient := by
  have hnil : PolyTimeComputable fun w => [decide (GI.argM w = [])] :=
    polyTimeComputable_isNil.comp GI.argM_poly
  have hhead := polyTimeComputable_pairFstD.comp GI.argM_poly
  refine GI.efficient_of_polyTime S (polyTimeComputable_ite hnil hFirst hhead) ?_
  intro x z r hist
  cases hist with
  | nil =>
    rw [hNil]
    simp only [GI.argM_ilayout, Strategy.encodeMsgs_nil, decide_true, if_true,
      GI.argX_ilayout, GI.argZ_ilayout, GI.inCoins_ilayout]
  | cons a hist =>
    rw [hCons]
    simp only [Function.comp_apply, GI.argM_ilayout, Strategy.encodeMsgs_cons, pairEncode_ne_nil,
      decide_false, Bool.false_eq_true, if_false, pairFstD_pairEncode]

/-- A strategy whose next message is `reply x z (hist.headD [])` is efficient if
the corresponding interactive-layout map is polynomial-time. The contract includes
empty and malformed histories and arbitrary private words. [PS10, Definition 155.1]
`S.Efficient`. -/
theorem reply_efficient (S : Strategy)
    (reply : List Bool → List Bool → List Bool → List Bool)
    (hNext : ∀ x z r hist, S.next x z r hist = reply x z (hist.headD []))
    (hReply : PolyTimeComputable fun w =>
      reply (GI.argX w) (GI.argZ w) (pairFstD (GI.argM w))) : S.Efficient := by
  refine GI.efficient_of_polyTime S hReply ?_
  intro x z r hist
  rw [hNext, GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout,
    Strategy.pairFstD_encodeMsgs]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
