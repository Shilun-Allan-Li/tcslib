/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The fixed-tape phase verifier for sequential zero knowledge

The phase wrapper of [PS10, Theorem 175.1] carries the original auxiliary input, one global
verifier tape, the phase index and the earlier received-prover prefix in its auxiliary input.
It invokes the original verifier on that fixed tape and the prefix followed by the current
phase's received messages. The wrapper itself has zero random bits.

## Main definitions

* `phaseAux z r j pre`: the nested-pair auxiliary input for a phase.
* `phaseVerifier V`: the deterministic phase wrapper of `V`.

## Main results

* `phaseAux_fields`, `phaseAux_prefix`: the auxiliary-input field readers.
* `phaseAux_length`, `phaseAux_length_le`: exact and bounded auxiliary-input lengths.
* `phaseAux_poly`: polynomial-time assembly of the auxiliary data.
* `phaseVerifier_next_phaseAux`: the exact next-message equation on encoded phase data.
* `phaseVerifier_efficient`: an efficient verifier has an efficient phase wrapper.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- For original auxiliary input `z`, verifier tape `r`, phase `j` and received prefix
`pre`, the phase auxiliary word is `⟨z, ⟨r, ⟨1^j, encodeMsgs pre⟩⟩⟩`.
[PS10, Theorem 175.1, phase-verifier auxiliary data].
`phaseAux z r j pre = pairEncode z (pairEncode r (pairEncode (List.replicate j true)
(Strategy.encodeMsgs pre)))`. -/
def phaseAux (z r : List Bool) (j : ℕ) (pre : List (List Bool)) : List Bool :=
  pairEncode z (pairEncode r (pairEncode (List.replicate j true) (Strategy.encodeMsgs pre)))

/-- The equation for `phaseAux z r j pre` is the nested pair
`pairEncode z (pairEncode r (pairEncode (List.replicate j true) (encodeMsgs pre)))`.
`phaseAux z r j pre = pairEncode z (pairEncode r (pairEncode (List.replicate j true)
(Strategy.encodeMsgs pre)))`. -/
theorem phaseAux_eq (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
    phaseAux z r j pre =
      pairEncode z (pairEncode r (pairEncode (List.replicate j true)
        (Strategy.encodeMsgs pre))) := rfl

/-- The four projection fields of `phaseAux z r j pre` are, in order,
`z`, `r`, `List.replicate j true`, and `Strategy.encodeMsgs pre`.
`pairFstD (phaseAux z r j pre) = z ∧ pairFstD (pairSndD (phaseAux z r j pre)) = r ∧ pairFstD
(pairSndD (pairSndD (phaseAux z r j pre))) = List.replicate j true ∧ pairSndD (pairSndD (pairSndD
(phaseAux z r j pre))) = Strategy.encodeMsgs pre`. -/
theorem phaseAux_fields (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
    pairFstD (phaseAux z r j pre) = z ∧
    pairFstD (pairSndD (phaseAux z r j pre)) = r ∧
    pairFstD (pairSndD (pairSndD (phaseAux z r j pre))) = List.replicate j true ∧
    pairSndD (pairSndD (pairSndD (phaseAux z r j pre))) = Strategy.encodeMsgs pre := by
  simp only [phaseAux_eq, pairFstD_pairEncode, pairSndD_pairEncode, and_self]

/-- The original auxiliary-input field is `pairFstD (phaseAux z r j pre) = z`. -/
theorem phaseAux_z (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
    pairFstD (phaseAux z r j pre) = z := (phaseAux_fields z r j pre).1

/-- The fixed verifier tape is `pairFstD (pairSndD (phaseAux z r j pre)) = r`. -/
theorem phaseAux_tape (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
    pairFstD (pairSndD (phaseAux z r j pre)) = r := (phaseAux_fields z r j pre).2.1

/-- The unary phase field has length `j`:
`(pairFstD (pairSndD (pairSndD (phaseAux z r j pre)))).length = j`. -/
theorem phaseAux_phase (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
    (pairFstD (pairSndD (pairSndD (phaseAux z r j pre)))).length = j :=
  (congrArg List.length (phaseAux_fields z r j pre).2.2.1).trans (List.length_replicate ..)

/-- Decoding the prefix field recovers `pre`:
`decWords (pairSndD (pairSndD (pairSndD (phaseAux z r j pre)))) = pre`. -/
theorem phaseAux_prefix (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
    BinArith.decWords (pairSndD (pairSndD (pairSndD (phaseAux z r j pre)))) = pre :=
  (congrArg BinArith.decWords (phaseAux_fields z r j pre).2.2.2).trans
    ((congrArg BinArith.decWords (encodeMsgs_eq_encWords pre)).trans
      (BinArith.decWords_encWords pre))

/-- The phase wrapper of `V` runs on original input `x`, the first auxiliary field as `z`,
the second as fixed tape, and the decoded prefix followed by its current received history.
Its own random-tape polynomial is `PolyExpr.const 0`.
[PS10, Theorem 175.1; Gol01, §4.3.4, the fixed-prefix phase verifier].
`phaseVerifier V = { next := fun x aux _ hist => V.next x (pairFstD aux) (pairFstD (pairSndD aux))
(BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist), coins := .const 0 }`. -/
def phaseVerifier (V : Strategy) : Strategy where
  next x aux _ hist :=
    V.next x (pairFstD aux) (pairFstD (pairSndD aux))
      (BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist)
  coins := .const 0

/-- The complete strategy equation is `phaseVerifier V = ⟨next, PolyExpr.const 0⟩`, where
`next x aux r hist = V.next x (pairFstD aux) (pairFstD (pairSndD aux))
(decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist)`. -/
theorem phaseVerifier_eq (V : Strategy) :
    phaseVerifier V =
      { next := fun x aux _ hist =>
          V.next x (pairFstD aux) (pairFstD (pairSndD aux))
            (BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist)
        coins := .const 0 } := rfl

/-- The coin polynomial of `phaseVerifier V` is `PolyExpr.const 0`.
`(phaseVerifier V).coins = .const 0`. -/
theorem phaseVerifier_coins (V : Strategy) : (phaseVerifier V).coins = .const 0 := rfl

/-- For `V, x, aux, r, hist`, the next message of the phase wrapper is
`V.next x (pairFstD aux) (pairFstD (pairSndD aux)) (decWords (snd (snd (snd aux))) ++ hist)`.
`(phaseVerifier V).next x aux r hist = V.next x (pairFstD aux) (pairFstD (pairSndD aux))
(BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist)`. -/
theorem phaseVerifier_next (V : Strategy) (x aux r : List Bool) (hist : List (List Bool)) :
    (phaseVerifier V).next x aux r hist =
      V.next x (pairFstD aux) (pairFstD (pairSndD aux))
        (BinArith.decWords (pairSndD (pairSndD (pairSndD aux))) ++ hist) := rfl

/-- At every input length `n`, `(phaseVerifier V).coinLen n = 0`. -/
theorem phaseVerifier_coinLen (V : Strategy) (n : ℕ) : (phaseVerifier V).coinLen n = 0 :=
  (Strategy.coinLen_eq (phaseVerifier V) n).trans
    ((congrArg (fun q : PolyExpr => q.eval n) (phaseVerifier_coins V)).trans
      (PolyExpr.eval_const 0 n))

/-- For `z, r, j, pre`, the exact auxiliary-word length is
`(phaseAux z r j pre).length = 2|z| + 2|r| + 2j + |encodeMsgs pre| + 6`. -/
theorem phaseAux_length (z r : List Bool) (j : ℕ) (pre : List (List Bool)) :
    (phaseAux z r j pre).length =
      2 * z.length + 2 * r.length + 2 * j + (Strategy.encodeMsgs pre).length + 6 := by
  rw [phaseAux_eq, length_pairEncode, length_pairEncode, length_pairEncode,
    List.length_replicate]
  omega

/-- For verifier `V`, input `x`, original auxiliary input `z`, fixed tape `r`, phase `j`,
earlier prefix `pre`, wrapper tape `s` and current history `hist`,
`(phaseVerifier V).next x (phaseAux z r j pre) s hist = V.next x z r (pre ++ hist)`.
[PS10, Theorem 175.1; Gol01, §4.3.4, the fixed-prefix phase verifier]. -/
theorem phaseVerifier_next_phaseAux (V : Strategy) (x z r : List Bool) (j : ℕ)
    (pre : List (List Bool)) (s : List Bool) (hist : List (List Bool)) :
    (phaseVerifier V).next x (phaseAux z r j pre) s hist = V.next x z r (pre ++ hist) := by
  rw [phaseVerifier_next, phaseAux_z, phaseAux_tape, phaseAux_prefix]

/-- If `V` is efficient, its fixed-tape phase wrapper is efficient:
`V.Efficient → (phaseVerifier V).Efficient`.
[PS10, Theorem 175.1; Gol01, §4.3.4, efficiency of the phase verifier].

**Proof sketch.** Take the uniform machine computing `V`. The new machine reads the original
auxiliary input and fixed random tape from projection fields. It canonically reencodes the
total decoded prefix with the published word-list map, appends the encoding of the current
history, assembles the original machine's layout, and runs its polynomial-time output.
The encoding of a concatenated history is the concatenation of its encodings, so the exact
next-message equation holds on every auxiliary word, including malformed encodings.
The machine uses the wrapper's zero coin polynomial. -/
theorem phaseVerifier_efficient {V : Strategy} (hV : V.Efficient) :
    (phaseVerifier V).Efficient := by
  obtain ⟨A, hA, _, hnext⟩ := (Strategy.efficient_iff V).1 hV
  -- Read the fixed data and canonically reencode the total prefix decoder.
  have hz := polyTimeComputable_pairFstD.comp GI.argZ_poly
  have hr := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp GI.argZ_poly)
  have hraw := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp GI.argZ_poly))
  have hprefix := polyTimeComputable_encWords_decWords hraw
  have hmsgs := hprefix.append GI.argM_poly
  have hlay := NUPPT.polyTimeComputable_layout
    (EncodingMachines.unaryLength_poly GI.argX_poly)
    ((GI.argX_poly.pairEncode hz).pairEncode hmsgs) (polyTimeComputable_const []) hr
  let F : List Bool → List Bool := fun w =>
    A.output (NUPPT.layout (List.replicate (GI.argX w).length true)
      (pairEncode (pairEncode (GI.argX w) (pairFstD (GI.argZ w)))
        (BinArith.encWords (BinArith.decWords
          (pairSndD (pairSndD (pairSndD (GI.argZ w))))) ++ GI.argM w)) []
      (pairFstD (pairSndD (GI.argZ w))))
  have hF : PolyTimeComputable F := A.polyTimeComputable_output.comp hlay
  -- The public strategy and encoding readers identify every actual activation.
  apply GI.efficient_of_polyTime (phaseVerifier V) hF
  intro x aux r hist
  dsimp only [F]
  rw [GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout]
  rw [phaseVerifier_next, hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout,
    hA.advice_eq, CommitmentLemmas.encodeMsgs_append,
    encodeMsgs_eq_encWords (BinArith.decWords (pairSndD (pairSndD (pairSndD aux))))]

/-- For polynomial-time words `Z, R`, a unary polynomial-time phase `J`, and a history
family `H` whose encoding is polynomial-time, `w ↦ phaseAux (Z w) (R w) (J w) (H w)` is
polynomial-time.
`PolyTimeComputable fun w => phaseAux (Z w) (R w) (J w) (H w)`. -/
theorem phaseAux_poly {Z R : List Bool → List Bool} {J : List Bool → ℕ}
    {H : List Bool → List (List Bool)}
    (hZ : PolyTimeComputable Z) (hR : PolyTimeComputable R)
    (hJ : PolyTimeComputable fun w => List.replicate (J w) true)
    (hH : PolyTimeComputable fun w => Strategy.encodeMsgs (H w)) :
    PolyTimeComputable fun w => phaseAux (Z w) (R w) (J w) (H w) := by
  refine (hZ.pairEncode (hR.pairEncode (hJ.pairEncode hH))).congr fun w => ?_
  rw [phaseAux_eq]

/-- For `z, r, j, pre, slots, B`, if `pre` has at most `slots` messages of at most `B` bits,
then `(phaseAux z r j pre).length ≤ 2|z| + 2|r| + 2j + slots*(2B+2) + 6`. -/
theorem phaseAux_length_le (z r : List Bool) (j : ℕ) (pre : List (List Bool))
    (slots B : ℕ) (hcount : pre.length ≤ slots) (hB : ∀ m ∈ pre, m.length ≤ B) :
    (phaseAux z r j pre).length ≤
      2 * z.length + 2 * r.length + 2 * j + slots * (2 * B + 2) + 6 := by
  rw [phaseAux_length]
  have henc := CommitmentLemmas.length_encodeMsgs_le pre B hB
  have hslots := Nat.mul_le_mul_right (2 * B + 2) hcount
  omega

end TCSlib.Cryptography.SequentialZK
