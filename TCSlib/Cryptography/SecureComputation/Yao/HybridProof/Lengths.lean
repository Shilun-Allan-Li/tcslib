/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Complexity.ClassP.BinaryArith.Words

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Length bounds for garbled messages

The bounds here do not assume that encryption evaluators return correctly sized pads.
Truncation and `zipWith` cap every ciphertext. This gives message bounds independent of
ideal-call answers, as required by [PS10, Definition 155.1].

## Main definitions

This module introduces no definitions.

## Main results

* `length_spEncStr_le`: special encryption has at most `3 |r| + |m| + 2` bits.
* `length_nestedSpecial_enc_le`: a nested ciphertext has at most `7 n + 4` bits.
* `length_encoded_garbledTables_le`: the encoded tables have at most
  `|gates| (112 n + 82)` bits for a fan-in-two circuit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Definition 155.1 and Protocol 162.6.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing TCSlib.Cryptography BoolCircuit

/-- Special encryption with evaluator `E`, key `k`, message `m` and nonce `r` satisfies
`|spEncStr E k m r| ≤ 3 |r| + |m| + 2`, regardless of the evaluator's output length.
[PS10, Algorithm 157.2] -/
theorem length_spEncStr_le (E : List Bool → List Bool) (k m r : List Bool) :
    (spEncStr E k m r).length ≤ 3 * r.length + m.length + 2 := by
  rw [spEncStr_eq, length_pairEncode, List.length_append, List.length_take,
    List.length_zipWith]
  omega

/-- For evaluators `E₁`, `E₂`, key length `n`, keys `ks`, plaintext `o` and coins `r`,
`|(nestedSpecial E₁ E₂ n).enc ks o r| ≤ 7 n + 4`. The bound holds for arbitrary
evaluator output lengths and arbitrary key-list lengths. [PS10, Protocol 162.6]

**Proof sketch.** With no key the ciphertext is the `n`-bit plaintext. With one key,
the special-encryption bound gives `4 n + 2`. With two keys, apply it first to the
inner layer and then to the outer layer to obtain `7 n + 4`. Longer key lists
produce the empty string. -/
theorem length_nestedSpecial_enc_le (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    (ks : List (Fin n → Bool)) (o : Fin n → Bool)
    (r : (Fin n → Bool) × (Fin n → Bool)) :
    ((nestedSpecial E₁ E₂ n).enc ks o r).length ≤ 7 * n + 4 := by
  rw [nestedSpecial_enc]
  match ks with
  | [] => simp only [List.length_ofFn]; omega
  | [k] =>
    change (spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1)).length ≤ 7 * n + 4
    have h := length_spEncStr_le E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1)
    simp only [List.length_ofFn] at h
    omega
  | [k₁, k₂] =>
    change (spEncStr E₂ (List.ofFn k₁)
      (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2))
      (List.ofFn r.1)).length ≤ 7 * n + 4
    have h₁ := length_spEncStr_le E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)
    have h₂ := length_spEncStr_le E₂ (List.ofFn k₁)
      (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)) (List.ofFn r.1)
    simp only [List.length_ofFn] at h₁ h₂
    omega
  | _ :: _ :: _ :: _ => simp only [List.length_nil]; omega

/-- For every list of words `L`, the history encoding and the word-list encoding agree:
`Strategy.encodeMsgs L = BinArith.encWords L`. -/
theorem encodeMsgs_eq_encWords (L : List (List Bool)) :
    Strategy.encodeMsgs L = BinArith.encWords L := by
  induction L with
  | nil => rw [Strategy.encodeMsgs_nil, BinArith.encWords_nil]
  | cons w L ih => rw [Strategy.encodeMsgs_cons, BinArith.encWords_cons, ih]

/-- For every input count `m`, circuit `C`, seed `s`, gate `i` and assignment `a`,
the nested-special garbled row has length at most `7 n + 4`.
[PS10, Protocol 162.6]
`(garbledRow (nestedSpecial E₁ E₂ n) C s i a).length ≤ 7 * n + 4`. -/
theorem length_garbledRow_le (E₁ E₂ : List Bool → List Bool) (n : ℕ) {m : ℕ}
    (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    (garbledRow (nestedSpecial E₁ E₂ n) C s i a).length ≤ 7 * n + 4 := by
  rw [garbledRow_eq]
  exact length_nestedSpecial_enc_le E₁ E₂ n _ _ _

/-- Gate `i` of a circuit `C` has at most four garbled rows whenever its argument
list has length at most two: `|garbledTable M C s i| ≤ 4`.
[PS10, Construction 158.a] -/
theorem length_garbledTable_le {K W ρ : Type} [Inhabited K] {m : ℕ}
    (M : MultiEnc K W ρ) (C : DAGCircuit m) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) (hi : (C.gates[i]).args.length ≤ 2) :
    (garbledTable M C s i).length ≤ 4 := by
  rw [garbledTable_eq, List.length_map, Finset.length_toList, Finset.card_univ]
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using
    (Nat.pow_le_pow_right Nat.zero_lt_two hi : 2 ^ (C.gates[i]).args.length ≤ 2 ^ 2)

/-- For evaluators `E₁`, `E₂`, key length `n`, circuit `C`, seed `s` and a gate `i`
with at most two arguments, `|encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) C s i)|
≤ 56 n + 40`. [PS10, Protocol 162.6]

**Proof sketch.** Each row has at most `7 n + 4` bits and the table has at most four
rows. Reuse the encoded-word-list bound through the history/word-list encoding
identity; four words of this length use at most `4 (2 (7 n + 4) + 2)` bits. -/
theorem length_encoded_garbledTable_le (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    {m : ℕ} (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (i : Fin C.gates.length) (hi : (C.gates[i]).args.length ≤ 2) :
    (Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) C s i)).length ≤
      56 * n + 40 := by
  rw [encodeMsgs_eq_encWords]
  calc
    _ ≤ (garbledTable (nestedSpecial E₁ E₂ n) C s i).length * (2 * (7 * n + 4) + 2) :=
      BinArith.length_encWords_le _ _ fun w hw => by
        rw [garbledTable_eq] at hw
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hw
        exact length_garbledRow_le E₁ E₂ n C s i _
    _ ≤ 4 * (2 * (7 * n + 4) + 2) :=
      Nat.mul_le_mul_right _ (length_garbledTable_le _ C s i hi)
    _ = 56 * n + 40 := by omega

/-- For evaluators `E₁`, `E₂`, key length `n`, circuit `C` and seed `s`, if each
gate has at most two arguments, the encoded list of encoded garbled tables has length
at most `C.gates.length * (112 n + 82)`. [PS10, Protocol 162.6]
`(Strategy.encodeMsgs (List.ofFn fun i : Fin C.gates.length => Strategy.encodeMsgs (garbledTable
(nestedSpecial E₁ E₂ n) C s i))).length ≤ C.gates.length * (112 * n + 82)`. -/
theorem length_encoded_garbledTables_le (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    {m : ℕ} (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (hC : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) :
    (Strategy.encodeMsgs (List.ofFn fun i : Fin C.gates.length =>
      Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) C s i))).length ≤
      C.gates.length * (112 * n + 82) := by
  rw [encodeMsgs_eq_encWords]
  have h := BinArith.length_encWords_le
    (List.ofFn fun i : Fin C.gates.length =>
      Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) C s i))
    (56 * n + 40) fun w hw => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact length_encoded_garbledTable_le E₁ E₂ n C s i (hC i)
  simpa only [List.length_ofFn, show 2 * (56 * n + 40) + 2 = 112 * n + 82 by omega]
    using h

/-- Encoding a list of `a` keys of `n` bits has length at most `a (2 n + 2)`:
`|encodeMsgs (ofFn (fun i => ofFn (keys i)))| ≤ a * (2 n + 2)`.
[PS10, Protocol 162.6] -/
theorem length_encoded_keys_le {a n : ℕ} (keys : Fin a → Fin n → Bool) :
    (Strategy.encodeMsgs (List.ofFn fun i => List.ofFn (keys i))).length ≤
      a * (2 * n + 2) := by
  rw [encodeMsgs_eq_encWords]
  have h := BinArith.length_encWords_le
    (List.ofFn fun i => List.ofFn (keys i)) n fun w hw => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact (List.length_ofFn (f := keys i)).le
  simpa only [List.length_ofFn] using h

/-- Encoding `o` decoding pairs of two `n`-bit keys has length at most `o (6 n + 6)`:
`|encodeMsgs (ofFn (fun j => ⟨ofFn (keys j false), ofFn (keys j true)⟩))|
≤ o * (6 n + 6)`. [PS10, Protocol 162.6, output-decoding implementation] -/
theorem length_encoded_pairs_le {o n : ℕ} (keys : Fin o → Bool → Fin n → Bool) :
    (Strategy.encodeMsgs (List.ofFn fun j =>
      pairEncode (List.ofFn (keys j false)) (List.ofFn (keys j true)))).length ≤
      o * (6 * n + 6) := by
  rw [encodeMsgs_eq_encWords]
  have h := BinArith.length_encWords_le
    (List.ofFn fun j => pairEncode (List.ofFn (keys j false)) (List.ofFn (keys j true)))
    (3 * n + 2) fun w hw => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      rw [length_pairEncode, List.length_ofFn, List.length_ofFn]
      omega
  simpa only [List.length_ofFn, show 2 * (3 * n + 2) + 2 = 6 * n + 6 by omega] using h

/-- If the table word, input-key word and decoding-pair word satisfy the bounds
`g (112 n + 82)`, `a (2 n + 2)` and `o (6 n + 6)`, their nested pair has length at most
`2 g (112 n + 82) + 2 a (2 n + 2) + o (6 n + 6) + 4`.
[PS10, Protocol 162.6]
`(pairEncode tables (pairEncode keys pairs)).length ≤ 2 * (g * (112 * n + 82)) + 2 * (a * (2 * n +
2)) + o * (6 * n + 6) + 4`. -/
theorem length_message_of_parts_le (tables keys pairs : List Bool) (g a o n : ℕ)
    (ht : tables.length ≤ g * (112 * n + 82))
    (hk : keys.length ≤ a * (2 * n + 2))
    (hp : pairs.length ≤ o * (6 * n + 6)) :
    (pairEncode tables (pairEncode keys pairs)).length ≤
      2 * (g * (112 * n + 82)) + 2 * (a * (2 * n + 2)) + o * (6 * n + 6) + 4 := by
  rw [length_pairEncode, length_pairEncode]
  omega

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
