/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The learner's input, computed from the distinguisher's encoded tuple

The distinguisher of [PS10, Theorem 179.1, proof] queries its oracle at `m(n) + 1` points
`ρ_0, …, ρ_m` and receives the encoded tuple of the pairs `(ρ_j, g(ρ_j))`: the concatenation
`tupleWord ρ g` of the blocks `⟨⟨ρ_j, g(ρ_j)⟩, []⟩`, each of `6n + 6` bits (the query chain of
`MultiMsg.exists_queryChain_nuppt`). It runs the learner on the labelled sample of the first
`m(n)` points, labelled by the first bits of the answers, and the last point, and compares the
prediction with the first bit of the last answer.

This file computes, by polynomial-time string functions of `⟨1^n, tupleWord ρ g⟩`:
- `learnIn m`: the learner's input `⟨S, ρ_m⟩`, where `S` is the nested pairs of the labelled
  examples `⟨ρ_j, [g(ρ_j)₁]⟩` (the sample encoding of the learning game);
- `lastLabel m`: the first bit of the last answer.

The labelled sample is a fold of pairs, which is a flat concatenation (`foldr_pairEncode_nil`),
so it is a block map of the first `m(n)` blocks of the tuple (`MultiMsg.flatMap_range_blocks`).

## Main definitions

* `LearnPRF.firstBit`, `LearnPRF.tupleWord`, `LearnPRF.relabel`, `LearnPRF.sampleLen`,
  `LearnPRF.learnIn`, `LearnPRF.lastLabel`.

## Main results

* `LearnPRF.foldr_pairEncode_nil`: a fold of pairs ending in `[]` is a concatenation.
* `LearnPRF.polyTimeComputable_learnIn`, `LearnPRF.polyTimeComputable_lastLabel`.
* `LearnPRF.learnIn_tupleWord`, `LearnPRF.lastLabel_tupleWord`: their values on an encoded tuple.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity Turing TCSlib.Cryptography

/-! ### Folds of pairs -/

/-- **A fold of pairs ending in `[]` is a concatenation:**
`L.foldr pairEncode [] = L.flatMap (fun a => pairEncode a [])`.

**Proof sketch.** Induction on `L`; `pairEncode a w = pairEncode a [] ++ w`
(`GGMRed.pairEncode_append_right`). -/
theorem foldr_pairEncode_nil (L : List (List Bool)) :
    L.foldr pairEncode [] = L.flatMap fun a => pairEncode a [] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, ih, List.flatMap_cons, ← GGMRed.pairEncode_append_right,
      List.nil_append]

/-! ### Words -/

/-- The first bit of an `n`-bit string, `false` for `n = 0`: `firstBit y = ⟦y⟧.headD false`. -/
def firstBit {n : ℕ} (y : Fin n → Bool) : Bool := (List.ofFn y).headD false

/-- `firstBit y = (List.ofFn y).headD false`. -/
theorem firstBit_eq {n : ℕ} (y : Fin n → Bool) : firstBit y = (List.ofFn y).headD false := rfl

/-- **The encoded tuple** of the pairs `(ρ_j, g(ρ_j))`: the concatenation of the blocks
`⟨⟨ρ_j, g(ρ_j)⟩, []⟩` (as in `MultiMsg.exists_queryChain_nuppt`). -/
def tupleWord {n k : ℕ} (ρ : Fin k → Fin n → Bool) (g : (Fin n → Bool) → (Fin n → Bool)) :
    List Bool :=
  (List.ofFn fun j => pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (g (ρ j)))) []).flatten

/-- `tupleWord ρ g = (List.ofFn fun j => ⟨⟨⟦ρ j⟧, ⟦g (ρ j)⟧⟩, []⟩).flatten`. -/
theorem tupleWord_eq {n k : ℕ} (ρ : Fin k → Fin n → Bool) (g : (Fin n → Bool) → (Fin n → Bool)) :
    tupleWord ρ g = (List.ofFn fun j =>
      pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (g (ρ j)))) []).flatten :=
  rfl

/-- The block of a pair `(x, y)`: `⟨⟨⟦x⟧, ⟦y⟧⟩, []⟩`. -/
private def blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- A block has `6n + 6 = histBlockLen(n)` bits. -/
private theorem length_blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    (blk p).length = MultiMsg.histBlockLen.eval n := by
  rw [blk, length_pairEncode, length_pairEncode, List.length_ofFn, List.length_ofFn,
    List.length_nil, MultiMsg.eval_histBlockLen]
  omega

/-- **Relabelling a block:** `⟨⟨x, y⟩, []⟩ ↦ ⟨⟨x, [y.headD false]⟩, []⟩`, the encoded labelled
example of the pair. -/
def relabel (w : List Bool) : List Bool :=
  pairEncode (pairEncode (pairFstD (pairFstD w)) [(pairSndD (pairFstD w)).headD false]) []

/-- `relabel w = ⟨⟨pairFstD (pairFstD w), [(pairSndD (pairFstD w)).headD false]⟩, []⟩`. -/
theorem relabel_eq (w : List Bool) :
    relabel w =
      pairEncode (pairEncode (pairFstD (pairFstD w)) [(pairSndD (pairFstD w)).headD false]) [] :=
  rfl

/-- Relabelling is polynomial-time. -/
theorem polyTimeComputable_relabel : PolyTimeComputable relabel := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  exact (((hF.comp hF).pairEncode (polyTimeComputable_headD.comp (hD.comp hF))).pairEncode
    (polyTimeComputable_const [])).congr fun w => rfl

/-- The relabelled block of `(x, y)` is `⟨⟨⟦x⟧, [firstBit y]⟩, []⟩`. -/
private theorem relabel_blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    relabel (blk p) = pairEncode (pairEncode (List.ofFn p.1) [firstBit p.2]) [] := by
  rw [relabel_eq, blk, pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode, firstBit_eq]

/-! ### The learner's input and the last label -/

/-- The length `m(n) · (6n + 6)` of the first `m(n)` blocks. -/
def sampleLen (m : PolyExpr) : PolyExpr := .mul m MultiMsg.histBlockLen

/-- `(sampleLen m).eval n = m(n) · (6n + 6)`. -/
theorem sampleLen_eval (m : PolyExpr) (n : ℕ) : (sampleLen m).eval n = m.eval n * (6 * n + 6) := by
  rw [sampleLen, PolyExpr.eval_mul, MultiMsg.eval_histBlockLen]

/-- The relabelled first `m(|u|)` blocks of `s`, on `⟨u, s⟩`: the block map of `relabel` over
`s.take (sampleLen m (|u|))` (the function of `Complexity.polyTimeComputable_blockMap`). -/
def sampleOf (m : PolyExpr) (z : List Bool) : List Bool :=
  (List.range (((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).length /
      MultiMsg.histBlockLen.eval (pairFstD z).length)).flatMap fun i =>
    relabel ((((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).drop
      (i * MultiMsg.histBlockLen.eval (pairFstD z).length)).take
        (MultiMsg.histBlockLen.eval (pairFstD z).length))

/-- `sampleOf m z` is the block map of `relabel` over the first `sampleLen m` bits. -/
theorem sampleOf_eq (m : PolyExpr) (z : List Bool) :
    sampleOf m z =
      (List.range (((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).length /
          MultiMsg.histBlockLen.eval (pairFstD z).length)).flatMap fun i =>
        relabel ((((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).drop
          (i * MultiMsg.histBlockLen.eval (pairFstD z).length)).take
            (MultiMsg.histBlockLen.eval (pairFstD z).length)) := rfl

/-- The last block's pair `⟨x, y⟩` on `⟨u, s⟩`: `pairFstD (s.drop (sampleLen m (|u|)))`. -/
def lastPair (m : PolyExpr) (z : List Bool) : List Bool :=
  pairFstD ((pairSndD z).drop ((sampleLen m).eval (pairFstD z).length))

/-- `lastPair m z = pairFstD ((pairSndD z).drop ((sampleLen m).eval |pairFstD z|))`. -/
theorem lastPair_eq (m : PolyExpr) (z : List Bool) :
    lastPair m z = pairFstD ((pairSndD z).drop ((sampleLen m).eval (pairFstD z).length)) := rfl

/-- **The learner's input** on `⟨1^n, s⟩`: `⟨sampleOf m z, x⟩`, the relabelled first `m(n)`
blocks and the point `x` of the last block. -/
def learnIn (m : PolyExpr) (z : List Bool) : List Bool :=
  pairEncode (sampleOf m z) (pairFstD (lastPair m z))

/-- `learnIn m z = ⟨sampleOf m z, pairFstD (lastPair m z)⟩`. -/
theorem learnIn_eq (m : PolyExpr) (z : List Bool) :
    learnIn m z = pairEncode (sampleOf m z) (pairFstD (lastPair m z)) := rfl

/-- **The last label** on `⟨1^n, s⟩`: the first bit of the answer of the last block. -/
def lastLabel (m : PolyExpr) (z : List Bool) : Bool := (pairSndD (lastPair m z)).headD false

/-- `lastLabel m z = (pairSndD (lastPair m z)).headD false`. -/
theorem lastLabel_eq (m : PolyExpr) (z : List Bool) :
    lastLabel m z = (pairSndD (lastPair m z)).headD false := rfl

/-- The last block's pair is polynomial-time (`polyTimeComputable_pairDropPoly`). -/
theorem polyTimeComputable_lastPair (m : PolyExpr) : PolyTimeComputable (lastPair m) :=
  (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairDropPoly (sampleLen m))).congr
    fun _ => rfl

/-- The learner's input is polynomial-time: the block map of `relabel`
(`Complexity.polyTimeComputable_blockMap`) after the head cut
(`polyTimeComputable_pairTakePoly`), paired with the last point. -/
theorem polyTimeComputable_learnIn (m : PolyExpr) : PolyTimeComputable (learnIn m) := by
  have hcut : PolyTimeComputable fun z => pairEncode (pairFstD z)
      ((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)) :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairTakePoly (sampleLen m))
  have hS : PolyTimeComputable (sampleOf m) :=
    ((polyTimeComputable_blockMap MultiMsg.histBlockLen polyTimeComputable_relabel).comp
      hcut).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, sampleOf_eq]
  exact (hS.pairEncode (polyTimeComputable_pairFstD.comp (polyTimeComputable_lastPair m))).congr
    fun _ => rfl

/-- The last label, as a one-bit output, is polynomial-time. -/
theorem polyTimeComputable_lastLabel (m : PolyExpr) :
    PolyTimeComputable fun z => [lastLabel m z] :=
  (polyTimeComputable_headD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_lastPair m))).congr fun _ => rfl

/-! ### Values on an encoded tuple -/

section Values

variable {n : ℕ} (m : PolyExpr) (ρ : Fin (m.eval n + 1) → Fin n → Bool)
  (g : (Fin n → Bool) → (Fin n → Bool))

/-- The encoded tuple is the first `m(n)` blocks followed by the last block, and the first part
has `sampleLen m` bits. -/
private theorem tupleWord_split :
    tupleWord ρ g =
      (List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten ++
        blk (ρ (Fin.last _), g (ρ (Fin.last _))) ∧
    ((List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten).length =
      (sampleLen m).eval n := by
  refine ⟨?_, ?_⟩
  · rw [tupleWord_eq, List.ofFn_succ', List.concat_eq_append, List.flatten_append,
      List.flatten_singleton]
    rfl
  · rw [MultiMsg.length_flatten_of_length (MultiMsg.histBlockLen.eval n) _ (fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        exact length_blk _), List.length_ofFn, sampleLen_eval, MultiMsg.eval_histBlockLen]

/-- **The learner's input on an encoded tuple:** on `⟨1^n, tupleWord ρ g⟩`, `learnIn m` is the
pair of the nested labelled examples `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points and
the last point `⟦ρ_m⟧`.

**Proof sketch.** Split the tuple into its first `m(n)` blocks and the last
(`tupleWord_split`); the head cut keeps the first part and the tail cut the last block
(`List.take_left'`, `List.drop_left'`). The block map over the first part relabels each block
(`MultiMsg.flatMap_range_blocks`, `MultiMsg.flatMap_ofFn`, `relabel_blk`), and the fold of the
examples is the same concatenation (`foldr_pairEncode_nil`). -/
theorem learnIn_tupleWord :
    learnIn m (pairEncode (List.replicate n true) (tupleWord ρ g)) =
      pairEncode ((List.ofFn fun j : Fin (m.eval n) => pairEncode (List.ofFn (ρ j.castSucc))
          [firstBit (g (ρ j.castSucc))]).foldr pairEncode [])
        (List.ofFn (ρ (Fin.last _))) := by
  obtain ⟨hsplit, hlen⟩ := tupleWord_split m ρ g
  have hb : 0 < MultiMsg.histBlockLen.eval n := by rw [MultiMsg.eval_histBlockLen]; omega
  have hblocks : ∀ x ∈ List.ofFn (fun j : Fin (m.eval n) => (ρ j.castSucc, g (ρ j.castSucc))),
      (blk x).length = MultiMsg.histBlockLen.eval n := fun x _ => length_blk x
  have hflat : (List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten =
      (List.ofFn fun j : Fin (m.eval n) => (ρ j.castSucc, g (ρ j.castSucc))).flatMap blk :=
    (MultiMsg.flatMap_ofFn _ blk).symm
  rw [learnIn_eq, sampleOf_eq, lastPair_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, hsplit, List.take_left' hlen, List.drop_left' hlen, blk,
    pairFstD_pairEncode, pairFstD_pairEncode, hflat,
    MultiMsg.flatMap_range_blocks blk relabel hb _ hblocks, foldr_pairEncode_nil,
    MultiMsg.flatMap_ofFn, MultiMsg.flatMap_ofFn]
  congr 2
  exact congrArg List.ofFn (funext fun j => relabel_blk _)

/-- **The last label on an encoded tuple:** on `⟨1^n, tupleWord ρ g⟩`, `lastLabel m` is the first
bit of the last answer, `firstBit (g ρ_m)`. -/
theorem lastLabel_tupleWord :
    lastLabel m (pairEncode (List.replicate n true) (tupleWord ρ g)) =
      firstBit (g (ρ (Fin.last _))) := by
  obtain ⟨hsplit, hlen⟩ := tupleWord_split m ρ g
  rw [lastLabel_eq, lastPair_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    hsplit, List.drop_left' hlen, blk, pairFstD_pairEncode, pairSndD_pairEncode, firstBit_eq]

end Values

end TCSlib.Cryptography.Randomness.LearnPRF
