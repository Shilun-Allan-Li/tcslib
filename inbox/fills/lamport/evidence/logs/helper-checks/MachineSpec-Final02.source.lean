/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Functional contracts of the planted Lamport machine

## Main definitions

None.

## Main results

* `advIn_context` identifies the machine's public key with the typed planted public table.
* `run_input` identifies its query answer and abort flag.
* `out_nonabort` identifies its final signature-block extraction.

The exact finite-tuple `coinBlock` reader is passed as a parameter, so this helper neither
imports the owned consumer nor copies that consumer's public lemma.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity Turing TCSlib.Cryptography.Games
open TCSlib.Cryptography

/-- The serialized public table is the concatenation of its self-delimiting image-pair
blocks. This reads the public tuple encoding through `encodeList_eq_flatMap`. -/
theorem publicWord_flatten {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) :
    publicWord Y = (List.ofFn fun i : Fin n =>
      pairEncode (pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) []).flatten := by
  rw [publicWord_eq, encodeList_eq_flatMap, List.flatMap_def, List.map_ofFn]
  simp only [Function.comp_apply]

section KeyWindows

variable (hcoin : ∀ {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
  (i : Fin q), coinBlock B i (List.ofFn g).flatten = g i)

include hcoin in
/-- Reading the first `n`-bit half of the selected sampled row returns `T(i,false)`. -/
theorem first_context {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool) :
    LamportMachine.first (seedIn n (pairEncode challenge (List.replicate i.val true))
      (c :: secretWord T)) = List.ofFn (T (i, false)) := by
  rw [LamportMachine.first_eq, LamportMachine.tape_seedIn, LamportMachine.offset_eq,
    LamportMachine.pos_seedIn, LamportMachine.u_seedIn]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hrow := hcoin (B := 2 * n) (fun j : Fin n => List.ofFn (T (j, false)) ++ List.ofFn (T (j, true)))
    (fun j => by simp only [List.length_append, List.length_ofFn]; omega) i
  rw [coinBlock_eq, ← secretWord_eq] at hrow
  have h := congrArg (fun w : List Bool => w.take n) hrow
  rw [List.take_take, Nat.min_eq_left (by omega), List.take_left' List.length_ofFn] at h
  exact h

include hcoin in
/-- Reading the second `n`-bit half of the selected sampled row returns `T(i,true)`. -/
theorem second_context {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool) :
    LamportMachine.second (seedIn n (pairEncode challenge (List.replicate i.val true))
      (c :: secretWord T)) = List.ofFn (T (i, true)) := by
  rw [LamportMachine.second_eq, LamportMachine.tape_seedIn, LamportMachine.offset_eq,
    LamportMachine.pos_seedIn, LamportMachine.u_seedIn]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hrow := hcoin (B := 2 * n) (fun j : Fin n => List.ofFn (T (j, false)) ++ List.ofFn (T (j, true)))
    (fun j => by simp only [List.length_append, List.length_ofFn]; omega) i
  rw [coinBlock_eq, ← secretWord_eq] at hrow
  have h := congrArg (fun w : List Bool => w.drop n) hrow
  rw [List.drop_take, show 2 * n - n = n by omega, List.drop_drop,
    List.drop_left' List.length_ofFn] at h
  exact h

include hcoin in
/-- The machine's replacement block serializes the planted row, using the evaluator's
published agreement on `n`-bit inputs. -/
theorem replacement_context {n ℓ : ℕ} (g : (Fin n → Bool) → Fin ℓ → Bool)
    (E : List Bool → List Bool)
    (hE : ∀ x : Fin n → Bool,
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (g x))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : Fin ℓ → Bool) :
    LamportMachine.replacement E
        (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
          (c :: secretWord T)) =
      pairEncode (pairEncode
        (List.ofFn (plantedPublic g T i c challenge (i, false)))
        (List.ofFn (plantedPublic g T i c challenge (i, true)))) [] := by
  rw [LamportMachine.replacement_eq, LamportMachine.bit_seedIn, LamportMachine.u_seedIn,
    LamportMachine.y_seedIn, first_context hcoin, second_context hcoin, hE, hE]
  cases c <;> simp [plantedPublic_eq]

include hcoin in
/-- On a canonical seed context, the machine's public-key input is exactly the serialized
typed planted table. The only generator/evaluator facts required are their stated functional
contracts; the owned Lamport module supplies them.

**Proof sketch.** The ordinary generated key is a concatenation of width `6ℓ+6` blocks.
The machine takes the blocks before `i`, inserts the planted block, and drops through block
`i`. The general fixed-width replacement lemma identifies this with updating row `i` before
serialization. Every other row retains both images. -/
theorem advIn_context {n ℓ : ℕ} (W : PolyExpr)
    (hW : W.eval n = 6 * ℓ + 6) (g : (Fin n → Bool) → Fin ℓ → Bool)
    (E G : List Bool → List Bool)
    (hE : ∀ x : Fin n → Bool,
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (g x))
    (hG : ∀ T : Table n,
      G (NUPPT.layout (List.replicate n true) [] [] (secretWord T)) =
        pairEncode (publicWord (tablePublic g T)) (secretWord T))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : Fin ℓ → Bool) :
    LamportMachine.advIn W E G
        (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
          (c :: secretWord T)) =
      publicWord (plantedPublic g T i c challenge) := by
  have hpk : LamportMachine.honestPk G
      (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
        (c :: secretWord T)) = publicWord (tablePublic g T) := by
    rw [LamportMachine.honestPk_eq, LamportMachine.u_seedIn, LamportMachine.tape_seedIn,
      hG, pairFstD_pairEncode]
  let rows : Fin n → List Bool := fun j => pairEncode (pairEncode
    (List.ofFn (g (T (j, false)))) (List.ofFn (g (T (j, true))))) []
  let plantedRows : Fin n → List Bool := fun j => pairEncode (pairEncode
    (List.ofFn (plantedPublic g T i c challenge (j, false)))
    (List.ofFn (plantedPublic g T i c challenge (j, true)))) []
  have hrows (j : Fin n) : (rows j).length = W.eval n := by
    simp only [rows, length_pairEncode, List.length_ofFn, List.length_nil, hW]
    ring
  have hnew : (plantedRows i).length = W.eval n := by
    simp only [plantedRows, length_pairEncode, List.length_ofFn, List.length_nil, hW]
    ring
  have hupdate : Function.update rows i (plantedRows i) = plantedRows := by
    funext j
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
    · have hp0 : (j, false) ≠ (i, c) := fun hp => hj (congrArg Prod.fst hp)
      have hp1 : (j, true) ≠ (i, c) := fun hp => hj (congrArg Prod.fst hp)
      rw [Function.update_of_ne hj]
      simp only [rows, plantedRows, plantedPublic_eq, if_neg hp0, if_neg hp1]
  have hnormal : publicWord (tablePublic g T) = (List.ofFn rows).flatten := by
    rw [publicWord_flatten]
    simp only [tablePublic_eq, rows]
  have hplant : publicWord (plantedPublic g T i c challenge) =
      (List.ofFn plantedRows).flatten := by
    rw [publicWord_flatten]
  simp only [LamportMachine.advIn_eq, hpk, replacement_context hcoin g E hE,
    LamportMachine.offset_eq, LamportMachine.width_eq, LamportMachine.pos_seedIn,
    LamportMachine.u_seedIn, List.length_replicate]
  simp only [hnormal, hplant]
  change (List.ofFn rows).flatten.take (i.val * W.eval n) ++ plantedRows i ++
    (List.ofFn rows).flatten.drop (i.val * W.eval n + W.eval n) =
      (List.ofFn plantedRows).flatten
  rw [show i.val * W.eval n + W.eval n = (i.val + 1) * W.eval n by ring,
    flatten_ofFn_update rows hrows i (plantedRows i) hnew, hupdate]

end KeyWindows

/-- The selected bit of a serialized message is its typed bit at that position. -/
theorem headD_drop_ofFn {n : ℕ} (m : Fin n → Bool) (i : Fin n) :
    ((List.ofFn m).drop i.val).headD false = m i := by
  simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some]

/-- On canonical input, the machine returns the typed signature and records the old abort
bit or equality `m_i=c`. This statement covers both safe and aborting calls. -/
theorem run_input {n : ℕ} (S : List Bool → List Bool)
    (hS : ∀ (T : Table n) (m : Fin n → Bool),
      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (tableSignature T m))
    (T : Table n) (i : Fin n) (c bad : Bool) (challenge : List Bool)
    (j : Fin 1) (m : Fin n → Bool) :
    LamportMachine.run S (PolyHandler.input n
        (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
        [bad] j (List.ofFn m)) =
      pairEncode (List.ofFn (tableSignature T m)) [bad || decide (m i = c)] := by
  have hb : LamportMachine.blocked (PolyHandler.input n
      (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
      [bad] j (List.ofFn m)) = decide (m i = c) := by
    rw [LamportMachine.blocked_eq, LamportMachine.context_input, LamportMachine.message_input,
      LamportMachine.pos_seedIn, LamportMachine.bit_seedIn, List.length_replicate,
      headD_drop_ofFn]
  simp only [LamportMachine.run_eq, LamportMachine.context_input, LamportMachine.state_input,
    LamportMachine.message_input, LamportMachine.u_seedIn, LamportMachine.tape_seedIn, hS,
    List.headD_cons, hb]

/-- A safe query from non-abort state returns the typed signature and a false abort bit. -/
theorem run_safe {n : ℕ} (S : List Bool → List Bool)
    (hS : ∀ (T : Table n) (m : Fin n → Bool),
      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (tableSignature T m))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool)
    (j : Fin 1) (m : Fin n → Bool) (hm : m i ≠ c) :
    LamportMachine.run S (PolyHandler.input n
        (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
        [false] j (List.ofFn m)) =
      pairEncode (List.ofFn (tableSignature T m)) [false] := by
  rw [run_input S hS]
  simp only [hm, decide_false, Bool.false_or]

/-- Finalization in non-abort state returns exactly the selected block of the typed forged
signature, after its first `n` message bits. -/
theorem out_nonabort {n : ℕ} (i : Fin n) (z ρ : List Bool)
    (a : Fin (n + n * n) → Bool)
    (hz : LamportMachine.pos (seedIn n z ρ) = List.replicate i.val true) :
    LamportMachine.out (pairEncode (seedIn n z ρ) (pairEncode [false] (List.ofFn a))) =
      List.ofFn (signatureBlock (splitBits a).2 i) := by
  rw [LamportMachine.out_eq, LamportMachine.state_eq, LamportMachine.context_eq]
  simp only [LamportMachine.context_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, Bool.false_eq_true,
    if_false, LamportMachine.u_seedIn, LamportMachine.offset_eq, hz,
    List.length_replicate, PolyExpr.eval_var]
  have hs : List.ofFn (splitBits a).2 = (List.ofFn a).drop n := by
    have hsplit : (splitBits a).2 = fun j => a (Fin.natAdd n j) := by
      funext j
      exact splitBits_snd a j
    rw [hsplit, ofFn_natAdd_eq_drop]
  rw [← hs, ← FunFamily.ofFn_blocks n n (splitBits a).2 i]
  apply congrArg List.ofFn
  funext k
  rw [FunFamily.blocks_apply, signatureBlock_eq]

end TCSlib.Cryptography.Authentication.LamportFill
