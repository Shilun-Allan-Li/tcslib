/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Encryption

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The iterated block encryptor and tuple decryptor

The honest iterated machines behind the public-key constructions of [PS10, §3.10]: the
**block encryptor** `blockEncFun E L B` which, on the state word `⟨u, ⟨pk, ⟨m, r⟩⟩⟩`, encrypts the
consecutive `L(|u|)`-bit blocks of the message string `m` under the public key `pk` with a fresh
`B(|u|)`-coin segment of `r` each, returning the nested-pair tuple of the ciphertexts; and the
**tuple decryptor** `decListFun Dc` which, on `⟨sk, ⟨c₀, ⟨c₁, …⟩⟩⟩`, concatenates `Dc ⟨sk, cᵢ⟩`.
With one-bit blocks they are the encryptor and decryptor of the bitwise scheme built from a
single-bit secure scheme [PS10, p. 103]; with `n`-bit blocks the encryptor is the
"efficiently generate encryptions of any message, without knowing the secret key" step of the
hybrid reductions of the single ⇒ multi-message theorem for public-key encryption
[PS10, p. 103] and of the multi-value hiding of commitments [PS10, Theorem 126.4]. Both are
instances of `Complexity.polyTimeComputable_iterateEmit` (D11), with the unfolding lemmas
`blockEncFun_spec`, `blockList_ofFn`, `decListFun_spec` proved.

## Main definitions

* `TCSlib.Cryptography.blockState`, `blockStep`, `blockEmit`, `blockEncFun`, `blockList` — the
  block encryptor, its step, emission and ideal output.
* `TCSlib.Cryptography.coinBlock` — the `i`-th coin segment.
* `TCSlib.Cryptography.decListStep`, `decListEmit`, `decListFun` — the tuple decryptor.

## Main results

* `TCSlib.Cryptography.blockEncFun_spec`, `blockList_ofFn` — unfolding of the block encryptor.
* `TCSlib.Cryptography.blockEncFun_poly`, `decListFun_poly` — both machines are polynomial-time.
* `TCSlib.Cryptography.decListFun_spec` — unfolding of the tuple decryptor.
* `TCSlib.Cryptography.encodeList_eq_flatMap`, `pairEncode_nil_append`,
  `length_le_length_encodeList` — the tuple encoding as a concatenation of blocks.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.10, p. 103; §4.6, Theorem 126.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026.
-/

namespace TCSlib.Cryptography

open Complexity Turing
open PrivateKeyScheme (encodeList)

/-! ## The tuple encoding as a concatenation of blocks -/

/-- The nested-pair encoding is the concatenation of the self-delimiting blocks `⟨c, []⟩`. -/
theorem encodeList_eq_flatMap (l : List (List Bool)) :
    encodeList l = l.flatMap fun c => pairEncode c [] := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [encodeList, ih, pairEncode]

/-- A tuple encoding is at least as long as the tuple. -/
theorem length_le_length_encodeList (l : List (List Bool)) :
    l.length ≤ (encodeList l).length := by
  induction l with
  | nil => simp
  | cons c cs ih => simp only [encodeList, length_pairEncode, List.length_cons]; omega

/-! ## The iterated block encryptor and decryptor -/

/-- The state word `⟨u, ⟨pk, ⟨m, r⟩⟩⟩` of the block encryptor: unary parameter `u`, public key
`pk`, remaining message `m`, remaining coins `r`. -/
def blockState (u pk m r : List Bool) : List Bool := pairEncode u (pairEncode pk (pairEncode m r))

/-- One step of the block encryptor: drop `L(|u|)` message bits and `B(|u|)` coins. -/
def blockStep (L B : PolyExpr) (w : List Bool) : List Bool :=
  blockState (pairFstD w) (pairFstD (pairSndD w))
    ((pairFstD (pairSndD (pairSndD w))).drop (L.eval (pairFstD w).length))
    ((pairSndD (pairSndD (pairSndD w))).drop (B.eval (pairFstD w).length))

/-- The emission of the block encryptor: nothing once the message is exhausted, otherwise the
block `⟨E ⟨⟨⟨u, ⟨pk, m.take L⟩⟩, []⟩, r.take B⟩, []⟩` (the evaluator `E` is an `NUPPT.output` run
on the uniform layout with the next coin segment). The emptiness test is written in the shape
of `Complexity.polyTimeComputable_lenLe`. -/
def blockEmit (E : List Bool → List Bool) (L B : PolyExpr) (w : List Bool) : List Bool :=
  if decide ((pairSndD (pairEncode [] (pairFstD (pairSndD (pairSndD w))))).length ≤
      (pairFstD (pairEncode [] (pairFstD (pairSndD (pairSndD w))))).length) then []
  else pairEncode (E (NUPPT.layout (pairFstD w)
    (pairEncode (pairFstD (pairSndD w))
      ((pairFstD (pairSndD (pairSndD w))).take (L.eval (pairFstD w).length)))
    [] ((pairSndD (pairSndD (pairSndD w))).take (B.eval (pairFstD w).length)))) []

/-- The **block encryptor**: on a state word `x = ⟨u, ⟨pk, ⟨m, r⟩⟩⟩`, the concatenation of the
emissions along `|x| + 1` steps — the nested-pair tuple of the encryptions of the consecutive
`L(|u|)`-bit blocks of `m` under `pk`, each with a fresh `B(|u|)`-coin segment of `r`. -/
def blockEncFun (E : List Bool → List Bool) (L B : PolyExpr) (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => blockEmit E L B ((blockStep L B)^[i] x)

/-- The ideal list of block encryptions with fuel `k`: `[]` once the message is empty. -/
def blockList (E : List Bool → List Bool) (L B : ℕ) (u pk : List Bool) :
    ℕ → List Bool → List Bool → List (List Bool)
  | 0, _, _ => []
  | k + 1, m, r => if m = [] then [] else
      E (NUPPT.layout u (pairEncode pk (m.take L)) [] (r.take B)) ::
        blockList E L B u pk k (m.drop L) (r.drop B)

/-- Unfolding: the step on a state word. -/
theorem blockStep_blockState (L B : PolyExpr) (u pk m r : List Bool) :
    blockStep L B (blockState u pk m r) =
      blockState u pk (m.drop (L.eval u.length)) (r.drop (B.eval u.length)) := by
  simp [blockStep, blockState]

/-- Unfolding: the emission on a state word. -/
theorem blockEmit_blockState (E : List Bool → List Bool) (L B : PolyExpr) (u pk m r : List Bool) :
    blockEmit E L B (blockState u pk m r) = if m = [] then [] else
      pairEncode (E (NUPPT.layout u (pairEncode pk (m.take (L.eval u.length))) []
        (r.take (B.eval u.length)))) [] := by
  simp [blockEmit, blockState, List.length_eq_zero_iff]

/-- The projections of the empty word are empty. -/
private theorem pairFstD_nil : pairFstD [] = [] := rfl

/-- The projections of the empty word are empty. -/
private theorem pairSndD_nil : pairSndD [] = [] := rfl

/-- The block `⟨c, []⟩` followed by a tuple is the tuple extended by `c`. -/
theorem pairEncode_nil_append (c w : List Bool) :
    pairEncode c [] ++ w = pairEncode c w := by
  simp [pairEncode]

/-- **Unfolding of the block encryptor** on a state word: with `k` rounds and a message of at
most `k · L(|u|)` bits (`L(|u|) > 0`), the concatenated emissions are the nested-pair tuple of
`blockList` with fuel `k + 1`.

**Proof sketch.** Induction on `k` generalizing `m, r`: `List.range_succ_eq_map` splits off the
first emission (`blockEmit_blockState`); the remaining emissions are those of the state after
one step (`Function.iterate_succ_apply`, `blockStep_blockState`), covered by the induction
hypothesis at `m.drop L` (`List.length_drop`), and `pairEncode_nil_append` reassembles the
tuple; an empty message emits nothing forever. -/
theorem blockEncFun_spec (E : List Bool → List Bool) (L B : PolyExpr) (u pk : List Bool) :
    ∀ (k : ℕ) (m r : List Bool), m.length ≤ k * L.eval u.length →
      ((List.range (k + 1)).flatMap fun i =>
        blockEmit E L B ((blockStep L B)^[i] (blockState u pk m r))) =
      encodeList (blockList E (L.eval u.length) (B.eval u.length) u pk (k + 1) m r) := by
  intro k
  induction k with
  | zero =>
    intro m r hm
    have hm0 : m = [] := List.length_eq_zero_iff.mp (by simpa using hm)
    subst hm0
    simp [blockEmit_blockState, blockList, encodeList]
  | succ k ih =>
    intro m r hm
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero, id, Function.iterate_succ_apply, blockStep_blockState]
    by_cases hm0 : m = []
    · subst hm0
      simp only [List.drop_nil]
      rw [ih [] (r.drop (B.eval u.length)) (by simp)]
      simp [blockEmit_blockState, blockList, encodeList]
    · rw [ih (m.drop (L.eval u.length)) (r.drop (B.eval u.length)) (by
        rw [List.length_drop, Nat.add_mul, one_mul] at *
        omega)]
      simp only [blockEmit_blockState, hm0, if_false, blockList, encodeList]
      exact pairEncode_nil_append _ _

/-- A step grows a word by at most six symbols (an invalid word collapses to the empty state).

**Proof sketch.** Case analysis on the validity of the three nested pairs (`pairDecode`
`none` versus `eq_pairEncode_of_pairDecode`); `length_pairEncode`, `List.length_drop`. -/
private theorem length_blockStep_le (L B : PolyExpr) (w : List Bool) :
    (blockStep L B w).length ≤ w.length + 6 := by
  have key : ∀ z : List Bool, (pairFstD z = [] ∧ pairSndD z = []) ∨
      2 * (pairFstD z).length + 2 + (pairSndD z).length = z.length := by
    intro z
    cases hz : pairDecode z with
    | none => exact Or.inl ⟨by simp [pairFstD, hz], by simp [pairSndD, hz]⟩
    | some p =>
      obtain ⟨a, b⟩ := p
      rw [eq_pairEncode_of_pairDecode z a b hz]
      exact Or.inr (by simp [length_pairEncode])
  simp only [blockStep, blockState, length_pairEncode, List.length_drop]
  rcases key w with ⟨hw1, hw2⟩ | hw
  · simp only [hw1, hw2, pairFstD_nil, pairSndD_nil, List.length_nil]
    omega
  rcases key (pairSndD w) with ⟨ht1, ht2⟩ | ht
  · simp only [ht1, ht2, pairFstD_nil, pairSndD_nil, List.length_nil]
    omega
  rcases key (pairSndD (pairSndD w)) with ⟨hs1, hs2⟩ | hs
  · simp only [hs1, hs2, List.length_nil]
    omega
  omega

/-- Orbit bound for a step that grows words by at most `c` symbols. -/
private theorem length_iterate_le {g : List Bool → List Bool} {c : ℕ}
    (hg : ∀ w, (g w).length ≤ w.length + c) (x : List Bool) :
    ∀ i, (g^[i] x).length ≤ x.length + c * i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := hg (g^[i] x)
    rw [Nat.mul_succ]
    omega

/-- The block step is polynomial-time (pair projections, `polyTimeComputable_pairDropPoly`). -/
theorem blockStep_poly (L B : PolyExpr) : PolyTimeComputable (blockStep L B) := by
  have hu := polyTimeComputable_pairFstD
  have hpk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hr := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have h := hu.pairEncode (hpk.pairEncode
    (((polyTimeComputable_pairDropPoly L).comp (hu.pairEncode hm)).pairEncode
      ((polyTimeComputable_pairDropPoly B).comp (hu.pairEncode hr))))
  convert h using 1
  funext w
  simp [blockStep, blockState, Function.comp]

/-- The block emission is polynomial-time for a polynomial-time `E`
(`polyTimeComputable_ite`, `polyTimeComputable_lenLe`, `polyTimeComputable_pairTakePoly`,
`NUPPT.polyTimeComputable_layout`). -/
theorem blockEmit_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) (L B : PolyExpr) :
    PolyTimeComputable (blockEmit E L B) := by
  have hu := polyTimeComputable_pairFstD
  have hpk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hr := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hp := polyTimeComputable_lenLe.comp ((polyTimeComputable_const []).pairEncode hm)
  have hbody := (hE.comp (NUPPT.polyTimeComputable_layout hu
    (hpk.pairEncode ((polyTimeComputable_pairTakePoly L).comp (hu.pairEncode hm)))
    (polyTimeComputable_const []) ((polyTimeComputable_pairTakePoly B).comp (hu.pairEncode hr)))).pairEncode
    (polyTimeComputable_const [])
  have h := polyTimeComputable_ite hp (polyTimeComputable_const []) hbody
  convert h using 1
  funext w
  simp only [blockEmit, Function.comp, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **The block encryptor is polynomial-time**: an instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := var` rounds and the orbit bound
`7 · |x|` (`length_blockStep_le`, `length_iterate_le`). -/
theorem blockEncFun_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) (L B : PolyExpr) :
    PolyTimeComputable (blockEncFun E L B) := by
  have h := polyTimeComputable_iterateEmit (blockStep_poly L B) (blockEmit_poly hE L B)
    .var (.mul (.const 7) .var) (fun x i hi => by
      have := length_iterate_le (length_blockStep_le L B) x i
      simp only [PolyExpr.eval_var] at hi
      simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      nlinarith)
  exact h

/-- One step of the tuple decryptor on `⟨sk, cs⟩`: drop the first ciphertext. -/
def decListStep (w : List Bool) : List Bool := pairEncode (pairFstD w) (pairSndD (pairSndD w))

/-- The emission of the tuple decryptor on `⟨sk, cs⟩`: nothing once the tuple is exhausted,
otherwise `Dc ⟨sk, c₀⟩` (test in the shape of `polyTimeComputable_lenLe`). -/
def decListEmit (Dc : List Bool → List Bool) (w : List Bool) : List Bool :=
  if decide ((pairSndD (pairEncode [] (pairSndD w))).length ≤
      (pairFstD (pairEncode [] (pairSndD w))).length) then []
  else Dc (pairEncode (pairFstD w) (pairFstD (pairSndD w)))

/-- The **tuple decryptor**: on `x = ⟨sk, ⟨c₀, ⟨c₁, …⟩⟩⟩` the concatenation
`Dc ⟨sk, c₀⟩ ++ Dc ⟨sk, c₁⟩ ++ ⋯` along `|x| + 1` steps. -/
def decListFun (Dc : List Bool → List Bool) (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => decListEmit Dc (decListStep^[i] x)

/-- **Unfolding of the tuple decryptor**: with `k ≥ |l|` rounds on `⟨sk, encodeList l⟩` the
emissions concatenate to `l.flatMap (fun c => Dc ⟨sk, c⟩)`.

**Proof sketch.** Induction on `k` generalizing `l`, cases on `l`; `List.range_succ_eq_map`,
`Function.iterate_succ_apply`; the step on `⟨sk, ⟨c, rest⟩⟩` is `⟨sk, rest⟩` and the step on
`⟨sk, []⟩` is `⟨sk, []⟩`. -/
theorem decListFun_spec (Dc : List Bool → List Bool) (sk : List Bool) :
    ∀ (k : ℕ) (l : List (List Bool)), l.length ≤ k →
      ((List.range (k + 1)).flatMap fun i => decListEmit Dc (decListStep^[i] (pairEncode sk (encodeList l)))) =
        l.flatMap fun c => Dc (pairEncode sk c) := by
  intro k
  induction k with
  | zero =>
    intro l hl
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hl0
    simp [decListEmit, encodeList]
  | succ k ih =>
    intro l hl
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero, id, Function.iterate_succ_apply]
    cases l with
    | nil =>
      have hstep : decListStep (pairEncode sk (encodeList [])) = pairEncode sk (encodeList []) := by
        simp [decListStep, encodeList, pairSndD_nil]
      rw [hstep, ih [] (by simp)]
      simp [decListEmit, encodeList]
    | cons c cs =>
      have hstep : decListStep (pairEncode sk (encodeList (c :: cs))) = pairEncode sk (encodeList cs) := by
        simp [decListStep, encodeList]
      rw [hstep, ih cs (by simpa using hl)]
      simp [decListEmit, encodeList, length_pairEncode]

/-- The tuple decryptor's step grows a word by at most two symbols. -/
private theorem length_decListStep_le (w : List Bool) : (decListStep w).length ≤ w.length + 2 := by
  simp only [decListStep, length_pairEncode]
  cases hz : pairDecode w with
  | none =>
    simp [pairFstD, pairSndD, hz, pairDecode]
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [eq_pairEncode_of_pairDecode w a b hz]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode]
    have : (pairSndD b).length ≤ b.length := by
      cases hb : pairDecode b with
      | none => simp [pairSndD, hb]
      | some p' =>
        obtain ⟨a', b'⟩ := p'
        rw [eq_pairEncode_of_pairDecode b a' b' hb]
        simp [length_pairEncode]
    omega

/-- **The tuple decryptor is polynomial-time** for a polynomial-time `Dc`
(`polyTimeComputable_iterateEmit`, `R := var`, orbit bound `7 · |x|`). -/
theorem decListFun_poly {Dc : List Bool → List Bool} (hD : PolyTimeComputable Dc) :
    PolyTimeComputable (decListFun Dc) := by
  have hstep : PolyTimeComputable decListStep :=
    polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hemit : PolyTimeComputable (decListEmit Dc) := by
    have hp := polyTimeComputable_lenLe.comp
      ((polyTimeComputable_const []).pairEncode polyTimeComputable_pairSndD)
    have h := polyTimeComputable_ite hp (polyTimeComputable_const [])
      (hD.comp (polyTimeComputable_pairFstD.pairEncode
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
    convert h using 1
  have h := polyTimeComputable_iterateEmit hstep hemit .var (.mul (.const 7) .var)
    (fun x i hi => by
      have := length_iterate_le length_decListStep_le x i
      simp only [PolyExpr.eval_var] at hi
      simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      nlinarith)
  exact h

/-- The `i`-th segment of `B` coins of a coin string. -/
def coinBlock (B i : ℕ) (r : List Bool) : List Bool := (r.drop (i * B)).take B

/-- `blockList` with one-bit blocks and enough fuel on an `n`-bit message is the list of the `n`
bit encryptions with the consecutive coin segments.

**Proof sketch.** Induction on `n`; `List.ofFn_succ` splits off the first bit, the fuel is a
successor, and the segments of `r.drop B` are the shifted segments of `r` (`List.drop_drop`). -/
theorem blockList_ofFn (E : List Bool → List Bool) (B : ℕ) (u pk : List Bool) :
    ∀ (n : ℕ) (m : Fin n → Bool) (r : List Bool) (k : ℕ), n ≤ k →
      blockList E 1 B u pk k (List.ofFn m) r =
        List.ofFn fun i : Fin n => E (NUPPT.layout u (pairEncode pk [m i]) [] (coinBlock B i r)) := by
  intro n
  induction n with
  | zero =>
    intro m r k _
    cases k <;> simp [blockList]
  | succ n ih =>
    intro m r k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [blockList, List.cons_ne_nil, if_false, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero, coinBlock, Fin.val_zero, zero_mul, List.cons.injEq,
      true_and]
    rw [ih (fun i => m i.succ) (r.drop B) k (by omega)]
    congr 1
    funext i
    simp only [coinBlock, Fin.val_succ, List.drop_drop]
    rw [show (B + ↑i * B) = (↑i + 1) * B by ring]

end TCSlib.Cryptography
