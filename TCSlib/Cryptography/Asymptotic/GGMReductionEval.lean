/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.GGMReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The GGM reduction machine and its functional identity (Theorem 97.3, machine step)

The second half of the machine infrastructure for the last paragraph of the proof of
[PS10, Theorem 97.3] (the first half, the components of the state loop and their
polynomial-time proofs, is `TCSlib.Cryptography.Asymptotic.GGMReduction`): the concrete
sub-hybrid distinguisher `ggmBitsDist` of the Garg layer as a recursion on rounds
(`concrete`, `pureStep`), the evaluation of the machine's state loop on its genuine input
(`rawFun_rawInput`), the reduction machine `ggmRedMachine` as a `Complexity.NUPPT`, and the
identity `ggmRedMachine_distinguisher` between the machine's verdict and the concrete
distinguisher's verdict.

**The identity.** The concrete distinguisher is `QueryTree.evalLazy` of the simulated query
tree (`levelAdv`, `tableDist` of the Garg layer); its recursion (`concrete_zero`,
`concrete_succ`) matches one round of the machine (`step_eq`: the lookup of the prefix, the
fresh value of a new prefix, the walk down the tree and the extension of the history), and
`concrete_iterate` telescopes the rounds up to the first verdict of `D`. The query tree of the
text is `buildTree` of `TCSlib.Cryptography.Asymptotic.PRF`; this file uses the equivalent
`Option`-valued form `buildTreeQ`, identified with `buildTree` in `PRF.lean`.

## Main definitions

* `TCSlib.Cryptography.GGMRed.Data` — the data of one activation (generator, indices,
  challenge, fresh randomness, `D`'s coins); `GGMRed.rawInput`, `GGMRed.coinStr` — the raw
  input and the coin string of the machine.
* `TCSlib.Cryptography.GGMRed.pureStep`, `GGMRed.concrete` — the pure simulation and the
  concrete verdict with a budget.
* `TCSlib.Cryptography.GGMRed.encState` — the encoding of a pure state as a machine state.
* `TCSlib.Cryptography.GGMRed.ggmRedMachine` — the reduction machine.

## Main results

* `TCSlib.Cryptography.GGMRed.concrete_iterate` — the recursion of the concrete distinguisher.
* `TCSlib.Cryptography.GGMRed.step_eq`, `GGMRed.orbit_eq_encState` — one round of the machine
  on an encoded state, and the closed form of its orbit.
* `TCSlib.Cryptography.GGMRed.rawFun_rawInput` — the machine's run on the genuine input.
* `TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher` — the machine computes the concrete
  sub-hybrid distinguisher `ggmBitsDist`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8.3, proof of Theorem 97.3, last paragraph.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2 (proof of Theorem 3.3, the outer adversary `B`, footnote 9
  on lazy sampling).
-/

namespace TCSlib.Cryptography.GGMRed

open Complexity Turing Finset QueryTree

/-! ## The concrete distinguisher as a recursion on rounds -/

section Concrete

variable {n : ℕ} (next : List ((Fin n → Bool) × (Fin n → Bool)) → List Bool)
  {P : Type} [DecidableEq P] (π : (Fin n → Bool) → P)
  (ans : (Fin n → Bool) → (Fin n → Bool) × (Fin n → Bool) → Fin n → Bool)
  (a : ℕ → (Fin n → Bool) × (Fin n → Bool))

/-- The pure state of the simulation: the history handed to `D` and the list of distinct
prefixes seen so far. -/
abbrev PureState (n : ℕ) (P : Type) : Type := List ((Fin n → Bool) × (Fin n → Bool)) × List P

/-- One round of the simulation on the pure state: a query `x` is answered through the lazily
sampled table (`QueryTree.noteQuery`, position `idxOf`) and appended to the history; a verdict
leaves the state unchanged. -/
def pureStep (s : PureState n P) : PureState n P :=
  match queryOf n (next s.1) with
  | some x => (s.1 ++ [(x, ans x (a ((noteQuery s.2 (π x)).idxOf (π x))))], noteQuery s.2 (π x))
  | none => s

/-- The concrete distinguisher's verdict from the pure state with budget `b`: the lazy
evaluation of the simulated tree. -/
def concrete (b : ℕ) (s : PureState n P) : Bool :=
  ((buildTreeQ next b s.1).simulate π ans).evalLazy a s.2

/-- The round is a query round. -/
def IsQ (s : PureState n P) : Prop := ∃ x, queryOf n (next s.1) = some x

/-- Budget `0`: a query is the forced verdict `false`, otherwise the verdict of `D`. -/
theorem concrete_zero (s : PureState n P) :
    concrete next π ans a 0 s =
      match queryOf n (next s.1) with
      | some _ => false
      | none => verdictOf (next s.1) := by
  unfold concrete
  rw [buildTreeQ_zero]
  cases queryOf n (next s.1) <;> rfl

/-- Budget `b + 1`: a query round continues with budget `b` from the next pure state. -/
theorem concrete_succ (b : ℕ) (s : PureState n P) :
    concrete next π ans a (b + 1) s =
      match queryOf n (next s.1) with
      | some _ => concrete next π ans a b (pureStep next π ans a s)
      | none => verdictOf (next s.1) := by
  unfold concrete pureStep
  rw [buildTreeQ_succ]
  cases queryOf n (next s.1) with
  | none => rfl
  | some x => rfl

/-- **Telescoping the rounds:** if the first `t` rounds are query rounds, the concrete verdict
with budget `t + b` is the verdict with budget `b` from the pure state after `t` rounds. -/
theorem concrete_iterate :
    ∀ (t b : ℕ) (s : PureState n P),
      (∀ t' < t, IsQ next ((pureStep next π ans a)^[t'] s)) →
      concrete next π ans a (t + b) s = concrete next π ans a b ((pureStep next π ans a)^[t] s)
  | 0, b, s, _ => by rw [Nat.zero_add]; rfl
  | t + 1, b, s, hq => by
    rw [show t + 1 + b = (t + b) + 1 by omega, concrete_succ, Function.iterate_succ_apply]
    obtain ⟨x, hx⟩ := hq 0 (Nat.succ_pos t)
    simp only [Function.iterate_zero, id] at hx
    rw [hx]
    exact concrete_iterate t b _ fun t' ht' => by
      have := hq (t' + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this

/-- The history grows by at most one entry per round, and the prefix list stays at most as
long as the history. -/
theorem pureStep_length (s : PureState n P) (h : s.2.length ≤ s.1.length) :
    (pureStep next π ans a s).2.length ≤ (pureStep next π ans a s).1.length ∧
      (pureStep next π ans a s).1.length ≤ s.1.length + 1 := by
  unfold pureStep
  cases queryOf n (next s.1) with
  | none => exact ⟨h, Nat.le_succ _⟩
  | some x =>
    simp only [List.length_append, List.length_singleton]
    have := length_noteQuery_le s.2 (π x)
    omega

/-- Along the pure evolution from the empty state, the prefix list is at most as long as the
history, which has at most one entry per round. -/
theorem pureStep_iterate_length (t : ℕ) :
    ((pureStep next π ans a)^[t] ([], [])).2.length ≤
        ((pureStep next π ans a)^[t] ([], [])).1.length ∧
      ((pureStep next π ans a)^[t] ([], [])).1.length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have h := pureStep_length next π ans a ((pureStep next π ans a)^[t] ([], [])) ih.1
    omega

end Concrete


/-! ## Decoding queries -/

/-- `decodeFin ℓ w = some x` iff `w` is the encoding of `x`. -/
theorem decodeFin_eq_some_iff (ℓ : ℕ) (w : List Bool) (x : Fin ℓ → Bool) :
    decodeFin ℓ w = some x ↔ w = List.ofFn x := by
  constructor
  · intro h
    have hw : w.length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · rintro rfl
    exact decodeFin_ofFn x

/-- `queryOf` recognises exactly the pairs `⟨[false], x⟩` with `x` an `ℓ`-bit string. -/
theorem queryOf_eq_some_iff (ℓ : ℕ) (w : List Bool) (x : Fin ℓ → Bool) :
    queryOf ℓ w = some x ↔ pairDecode w = some ([false], List.ofFn x) := by
  constructor
  · intro h
    unfold queryOf at h
    split at h
    next x' hx' => rw [hx', (decodeFin_eq_some_iff ℓ x' x).1 h]
    next => simp at h
  · intro h
    unfold queryOf
    rw [h]
    exact decodeFin_ofFn x

/-- The encoding of the padding of a string of the right length is the string. -/
theorem ofFn_padFin_of_length {ℓ : ℕ} {w : List Bool} (h : w.length = ℓ) :
    List.ofFn (padFin ℓ w) = w := by
  refine List.ext_getElem (by simp [h]) fun k hk₁ hk₂ => ?_
  simp [padFin, List.getElem?_eq_getElem hk₂]

/-- A machine output is a query iff its first component is `[false]` and its second has
length `ℓ`. -/
theorem exists_queryOf_iff (ℓ : ℕ) (w : List Bool) :
    (∃ x, queryOf ℓ w = some x) ↔ pairFstD w = [false] ∧ (pairSndD w).length = ℓ := by
  constructor
  · rintro ⟨x, hx⟩
    rw [queryOf_eq_some_iff] at hx
    simp [pairFstD, pairSndD, hx]
  · rintro ⟨h1, h2⟩
    cases hd : pairDecode w with
    | none => simp [pairFstD, hd] at h1
    | some ab =>
      obtain ⟨a, b⟩ := ab
      simp only [pairFstD, pairSndD, hd, Option.map_some, Option.getD_some] at h1 h2
      subst h1
      exact ⟨padFin ℓ b, (queryOf_eq_some_iff ℓ w _).2 (by rw [hd, ofFn_padFin_of_length h2])⟩

/-- The query string of a query move. -/
theorem pairSndD_of_queryOf {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : queryOf ℓ w = some x) : pairSndD w = List.ofFn x := by
  rw [queryOf_eq_some_iff] at h
  simp [pairSndD, h]

/-! ## Evaluation on the genuine input -/

/-- The data of one activation of the reduction at parameter `n`: the generator, the hybrid
indices, the challenge, the fresh randomness of the lazily sampled tables and `D`'s coins. -/
structure Data (D : NUPPT) (q : PolyExpr) (n : ℕ) where
  /-- The length-doubling generator at parameter `n`. -/
  G : (Fin n → Bool) → Fin (2 * n) → Bool
  /-- The level index `i`. -/
  i : ℕ
  /-- The sub-hybrid index `j`. -/
  j : ℕ
  /-- The challenge `z ∈ {0,1}^{2n}`. -/
  z : Fin (2 * n) → Bool
  /-- The fresh seeds `W₀` and pairs `W₁` of the lazily sampled tables. -/
  W : (Fin (q.eval n) → Fin n → Bool) × (Fin (q.eval n) → (Fin n → Bool) × (Fin n → Bool))
  /-- `D`'s coins. -/
  r : D.Coins n

section Eval

variable {D : NUPPT} {q : PolyExpr} {n : ℕ} (d : Data D q n)

/-- The coin string of the machine: the `q(n)` seeds, the `q(n)` pairs (each a `2n`-bit
string), and `D`'s coins. -/
def coinStr : List Bool :=
  List.ofFn ((FunFamily.blocks (q.eval n) n).symm d.W.1) ++
    (List.ofFn ((FunFamily.blocks (q.eval n) (2 * n)).symm fun k => splitHalves.symm (d.W.2 k)) ++
      List.ofFn d.r)

/-- The raw input of the machine at parameter `n`: `⟨⟨⟨1^n, z⟩, ⟨⟨1^i, 1^j⟩, α_D⟩⟩, coins⟩`. -/
def rawInput : List Bool :=
  NUPPT.layout (List.replicate n true) (List.ofFn d.z)
    (pairEncode (pairEncode (List.replicate d.i true) (List.replicate d.j true)) (D.advice n))
    (coinStr d)

/-- The answer stream of the concrete distinguisher: `challengeStream` at index `j` with the
split challenge. -/
noncomputable def stream : ℕ → (Fin n → Bool) × (Fin n → Bool) :=
  challengeStream (splitHalves ∘ d.G) d.j (splitHalves d.z) d.W

/-- The stored value strings: the `k`-th distinct prefix stores the `2n`-bit string whose
halves are `stream k`. -/
noncomputable def valStr (k : ℕ) : List Bool := List.ofFn (splitHalves.symm (stream d k))

/-- The next-query function of `D` with the fixed coins `r`. -/
def nextQ (hist : List ((Fin n → Bool) × (Fin n → Bool))) : List Bool :=
  D.runAt n (histEnc hist) d.r

/-- The prefix map of the level-`i` simulation. -/
def prefMap (x : Fin n → Bool) : Fin d.i → Bool := prefixAt x d.i

/-- The answer map of the level-`i` simulation. -/
def ansMap (hi : d.i < n) (x : Fin n → Bool) (v : (Fin n → Bool) × (Fin n → Bool)) :
    Fin n → Bool :=
  ggmFrom (splitHalves ∘ d.G) x (d.i + 1) (pairSel (x ⟨d.i, hi⟩) v)

/-- The encoding of a pure state at round `t`: encoded history, encoded table, table size and
round counter in unary. -/
noncomputable def encState (s : PureState n (Fin d.i → Bool)) (t : ℕ) : List Bool :=
  pairEncode (histEnc s.1) (pairEncode (tblEnc (tblOf (valStr d) s.2 0))
    (pairEncode (List.replicate s.2.length true) (List.replicate t true)))

/-- Every stored value has `2n` bits. -/
theorem length_valStr (k : ℕ) : (valStr d k).length = 2 * n := List.length_ofFn

/-- The initial state encodes the empty pure state at round `0`. -/
theorem start_rawInput : start (rawInput d) = encState d ([], []) 0 := rfl

/-- The length of an encoded state. -/
theorem length_encState (s : PureState n (Fin d.i → Bool)) (t : ℕ) :
    (encState d s t).length =
      2 * (s.1.length * (6 * n + 6)) + 2 +
        (2 * (s.2.length * (4 * d.i + 2 * (2 * n) + 6)) + 2 + (2 * s.2.length + 2 + t)) := by
  simp only [encState, length_pairEncode, List.length_replicate, length_histEnc,
    length_tblEnc_tblOf (valStr d) (length_valStr d)]

/-- The length of the raw input is at least `n`. -/
theorem le_length_rawInput : n ≤ (rawInput d).length := by
  simp only [rawInput, NUPPT.layout, length_pairEncode, List.length_replicate]
  omega

variable (s : PureState n (Fin d.i → Bool)) (t : ℕ)

/-- The parameter slot of the encoded state word. -/
theorem paramU_eq : paramU (pairEncode (rawInput d) (encState d s t)) = List.replicate n true := by
  simp [paramU, inX, rawInput]

/-- The challenge slot of the encoded state word. -/
theorem chal_eq : chal (pairEncode (rawInput d) (encState d s t)) = List.ofFn d.z := by
  simp [chal, inX, rawInput]

/-- The level index of the encoded state word. -/
theorem unI_eq : unI (pairEncode (rawInput d) (encState d s t)) = List.replicate d.i true := by
  simp [unI, inX, rawInput]

/-- The sub-hybrid index of the encoded state word. -/
theorem unJ_eq : unJ (pairEncode (rawInput d) (encState d s t)) = List.replicate d.j true := by
  simp [unJ, inX, rawInput]

/-- `D`'s advice in the encoded state word. -/
theorem advD_eq : advD (pairEncode (rawInput d) (encState d s t)) = D.advice n := by
  simp [advD, inX, rawInput]

/-- The coins of the encoded state word. -/
theorem coinsAll_eq : coinsAll (pairEncode (rawInput d) (encState d s t)) = coinStr d := by
  simp [coinsAll, inX, rawInput]

/-- The seeds of the encoded state word. -/
theorem seeds_eq : seeds q (pairEncode (rawInput d) (encState d s t)) =
    List.ofFn ((FunFamily.blocks (q.eval n) n).symm d.W.1) := by
  rw [seeds, coinsAll_eq, paramU_eq, coinStr]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_var]
  exact List.take_left' List.length_ofFn

/-- The coins after the seeds of the encoded state word. -/
theorem coinsRest_eq : coinsRest q (pairEncode (rawInput d) (encState d s t)) =
    List.ofFn ((FunFamily.blocks (q.eval n) (2 * n)).symm fun k => splitHalves.symm (d.W.2 k)) ++
      List.ofFn d.r := by
  rw [coinsRest, coinsAll_eq, paramU_eq, coinStr]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_var]
  exact List.drop_left' List.length_ofFn

/-- The pairs of the encoded state word. -/
theorem pairs_eq : pairs q (pairEncode (rawInput d) (encState d s t)) =
    List.ofFn ((FunFamily.blocks (q.eval n) (2 * n)).symm fun k => splitHalves.symm (d.W.2 k)) := by
  rw [pairs, coinsRest_eq, paramU_eq]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  exact List.take_left' List.length_ofFn

/-- `D`'s coins in the encoded state word. -/
theorem coinsD_eq : coinsD q (pairEncode (rawInput d) (encState d s t)) = List.ofFn d.r := by
  rw [coinsD, coinsRest_eq, paramU_eq]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  exact List.drop_left' List.length_ofFn

/-- The history of the encoded state word. -/
theorem hist_eq : hist (pairEncode (rawInput d) (encState d s t)) = histEnc s.1 := by
  simp [hist, inS, encState]

/-- The table of the encoded state word. -/
theorem tbl_eq : tbl (pairEncode (rawInput d) (encState d s t)) =
    tblEnc (tblOf (valStr d) s.2 0) := by
  simp [tbl, inS, encState]

/-- The table size of the encoded state word. -/
theorem cnt_eq : cnt (pairEncode (rawInput d) (encState d s t)) =
    List.replicate s.2.length true := by
  simp [cnt, inS, encState]

/-- The round counter of the encoded state word. -/
theorem rnd_eq : rnd (pairEncode (rawInput d) (encState d s t)) = List.replicate t true := by
  simp [rnd, inS, encState]

/-- The move of the machine on the encoded state is `D`'s move on the history. -/
theorem move_eq : move D q (pairEncode (rawInput d) (encState d s t)) = nextQ d s.1 := by
  rw [move, paramU_eq, hist_eq, advD_eq, coinsD_eq]
  rfl

/-- The query test of the machine is the query test of the pure state. -/
theorem isQ_iff : isQ D q (pairEncode (rawInput d) (encState d s t)) = true ↔ IsQ (nextQ d) s := by
  rw [isQ, move_eq, paramU_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    List.length_replicate, IsQ, exists_queryOf_iff]

/-- The stopping test on the encoded state. -/
theorem acc_eq : acc D q (pairEncode (rawInput d) (encState d s t)) =
    (!isQ D q (pairEncode (rawInput d) (encState d s t)) || decide (q.eval n ≤ t)) := by
  rw [acc, unQ, paramU_eq, rnd_eq]
  simp only [List.length_replicate]

/-- The output on the encoded state. -/
theorem out_eq : out D q (pairEncode (rawInput d) (encState d s t)) =
    if isQ D q (pairEncode (rawInput d) (encState d s t)) then [false]
    else [verdictOf (nextQ d s.1)] := by
  rw [out, move_eq]

/-- The unary offset of the next seed. -/
theorem mul1_length : (mul1 (pairEncode (rawInput d) (encState d s t))).length = n * s.2.length := by
  simp [mul1, paramU_eq, cnt_eq]

/-- The unary string `1^{2n}` of the encoded state word. -/
theorem un2_length : (un2 (pairEncode (rawInput d) (encState d s t))).length = 2 * n := by
  simp [un2, paramU_eq]

/-- The unary offset of the next pair. -/
theorem mul2_length :
    (mul2 (pairEncode (rawInput d) (encState d s t))).length = (2 * n) * s.2.length := by
  simp [mul2, un2_length, cnt_eq]

/-- **The fresh value is the stored value of the next distinct prefix:** on the encoded state
with `|L| < q(n)`, `fresh` computes `valStr |L|`.

**Proof sketch.** The tests of the machine read `|L| < j` and `|L| = j` off the unary strings;
`challengeStream` unfolds by the same cases. For `|L| < j` the machine reads block `|L|` of the
pairs (`drop_take_ofFn_blocks`), which is `W₁ |L|` re-encoded; for `|L| = j` it returns the
challenge; otherwise it applies `E` to block `|L|` of the seeds, which is `G (W₀ |L|)` by
`hG`. -/
theorem fresh_eq (E : List Bool → List Bool)
    (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (d.G s)) (hk : s.2.length < q.eval n) :
    fresh E q (pairEncode (rawInput d) (encState d s t)) = valStr d s.2.length := by
  have hlt : ltJ (pairEncode (rawInput d) (encState d s t)) = decide (s.2.length < d.j) := by
    simp only [ltJ, unJ_eq, cnt_eq, List.length_replicate, ← decide_not, not_le]
  have heq : eqJ (pairEncode (rawInput d) (encState d s t)) = decide (s.2.length = d.j) := by
    simp [eqJ, unJ_eq, cnt_eq]
  have hstream : ∀ (k : ℕ) (hk : k < q.eval n), stream d k =
      if k < d.j then d.W.2 ⟨k, hk⟩ else if k = d.j then splitHalves d.z
        else splitHalves (d.G (d.W.1 ⟨k, hk⟩)) := by
    intro k hk
    simp [stream, challengeStream, extendStream, hk]
  rw [fresh, hlt, heq, valStr, hstream _ hk]
  by_cases h1 : s.2.length < d.j
  · rw [if_pos (by simpa using h1), if_pos h1, pairs_eq, mul2_length, un2_length,
      drop_take_ofFn_blocks (q.eval n) (2 * n) _ hk, Equiv.apply_symm_apply]
  · rw [if_neg (by simpa using h1), if_neg h1]
    by_cases h2 : s.2.length = d.j
    · rw [if_pos (by simpa using h2), if_pos h2, chal_eq, Equiv.symm_apply_apply]
    · rw [if_neg (by simpa using h2), if_neg h2, seeds_eq, mul1_length, paramU_eq,
        List.length_replicate, drop_take_ofFn_blocks (q.eval n) n _ hk, Equiv.apply_symm_apply,
        hG, Equiv.symm_apply_apply]

/-- **One round of the machine on an encoded query state** is the encoding of the next pure
state.

**Proof sketch.** The move is `D`'s move on the history (`move_eq`), a query `x` whose string
is `List.ofFn x`; its prefix is looked up in the table (`lookup_tblOf`). If the prefix is
known, the stored value is `valStr (idxOf)` and the table is unchanged; otherwise the fresh
value `valStr |L|` (`fresh_eq`) is appended (`tblOf_append_single`, `tblEnc_append_single`) and
the counter grows. In both cases the answer is the walk from the half of the value selected by
bit `x_{i+1}` (`selHalf_ofFn`, `ggmEval_ofFn_walk`, `ggmFrom_eq_walk`), which is the answer map
of the simulation, and the history is extended by `⟨x, answer⟩` (`histEnc_append_single`). -/
theorem step_eq (E : List Bool → List Bool)
    (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (d.G s)) (hi : d.i < n)
    (hk : s.2.length < q.eval n) {x : Fin n → Bool} (hx : queryOf n (nextQ d s.1) = some x) :
    step E D q (pairEncode (rawInput d) (encState d s t)) =
      encState d (pureStep (nextQ d) (prefMap d) (ansMap d hi) (stream d) s) (t + 1) := by
  classical
  have hquery : query D q (pairEncode (rawInput d) (encState d s t)) = List.ofFn x := by
    rw [query, move_eq, pairSndD_of_queryOf hx]
  have hpfx : pfx D q (pairEncode (rawInput d) (encState d s t)) = List.ofFn (prefixAt x d.i) := by
    rw [pfx, hquery, unI_eq, List.length_replicate, ofFn_prefixAt x hi.le]
  have hlook : look D q (pairEncode (rawInput d) (encState d s t)) =
      if prefixAt x d.i ∈ s.2 then pairEncode [] (valStr d (s.2.idxOf (prefixAt x d.i)))
      else [] := by
    rw [look, hpfx, tbl_eq, lookup_tblOf]
  have hbit : ((List.ofFn x).drop d.i).headD false = x ⟨d.i, hi⟩ := by
    rw [List.drop_eq_getElem_cons (by simpa using hi), List.headD_cons, List.getElem_ofFn]
  have hrest : ((List.ofFn x).drop d.i).tail = (List.ofFn x).drop (d.i + 1) := List.tail_drop
  have hans : ∀ k, vstr E D q (pairEncode (rawInput d) (encState d s t)) = valStr d k →
      ans E D q (pairEncode (rawInput d) (encState d s t)) =
        List.ofFn (ansMap d hi x (stream d k)) := by
    intro k hv
    rw [ans, lab, hv, hquery, unI_eq, List.length_replicate, hbit, hrest, paramU_eq, valStr,
      selHalf_ofFn _ (List.length_replicate ..) _, Equiv.apply_symm_apply, ggmEval_ofFn_walk hG,
      ansMap, ggmFrom_eq_walk]
  have hpure : pureStep (nextQ d) (prefMap d) (ansMap d hi) (stream d) s =
      (s.1 ++ [(x, ansMap d hi x (stream d
        ((noteQuery s.2 (prefixAt x d.i)).idxOf (prefixAt x d.i))))],
        noteQuery s.2 (prefixAt x d.i)) := by
    rw [pureStep, hx]
    rfl
  rw [hpure]
  by_cases hmem : prefixAt x d.i ∈ s.2
  · have hnf : notFound D q (pairEncode (rawInput d) (encState d s t)) = false := by
      simp [notFound, hlook, hmem, pairEncode_ne_nil]
    have hv : vstr E D q (pairEncode (rawInput d) (encState d s t)) =
        valStr d (s.2.idxOf (prefixAt x d.i)) := by
      rw [vstr, hnf, hlook, if_pos hmem]
      simp
    rw [noteQuery_of_mem hmem]
    simp only [step, hist', tbl', cnt', hnf, Bool.false_eq_true, if_false, hist_eq, tbl_eq,
      cnt_eq, rnd_eq, hquery, hans _ hv]
    simp only [encState, histEnc_append_single, List.replicate_succ]
  · have hnf : notFound D q (pairEncode (rawInput d) (encState d s t)) = true := by
      simp [notFound, hlook, hmem]
    have hv : vstr E D q (pairEncode (rawInput d) (encState d s t)) = valStr d s.2.length := by
      rw [vstr, hnf, if_pos rfl, fresh_eq d s t E hG hk]
    have hidx : (noteQuery s.2 (prefixAt x d.i)).idxOf (prefixAt x d.i) = s.2.length := by
      rw [noteQuery_of_not_mem hmem, List.idxOf_append_of_notMem hmem, List.idxOf_cons_self,
        Nat.add_zero]
    rw [hidx, noteQuery_of_not_mem hmem]
    simp only [step, hist', tbl', cnt', hnf, if_true, hist_eq, tbl_eq, cnt_eq, rnd_eq, hquery,
      hans _ hv, hpfx, fresh_eq d s t E hG hk]
    simp only [encState, histEnc_append_single, List.replicate_succ, tblOf_append_single,
      zero_add, tblEnc_append_single, List.length_append, List.length_singleton]

end Eval


/-! ## The run of the machine on the genuine input -/

section Main

variable {D : NUPPT} {q : PolyExpr} {n : ℕ} (d : Data D q n) (E : List Bool → List Bool)
  (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (d.G s)) (hi : d.i < n)

/-- The pure state after `t` rounds from the empty state. -/
noncomputable def pureAt (t : ℕ) : PureState n (Fin d.i → Bool) :=
  (pureStep (nextQ d) (prefMap d) (ansMap d hi) (stream d))^[t] ([], [])

/-- The pure state after `t + 1` rounds. -/
theorem pureAt_succ (t : ℕ) :
    pureAt d hi (t + 1) = pureStep (nextQ d) (prefMap d) (ansMap d hi) (stream d) (pureAt d hi t) :=
  Function.iterate_succ_apply' _ _ _

/-- The length bounds along the pure evolution. -/
theorem pureAt_length (t : ℕ) :
    (pureAt d hi t).2.length ≤ (pureAt d hi t).1.length ∧ (pureAt d hi t).1.length ≤ t :=
  pureStep_iterate_length (nextQ d) (prefMap d) (ansMap d hi) (stream d) t

include hG in
/-- **Closed form of the machine's orbit:** while every earlier round was rejected by the
stopping test (a query round within budget), the state after `t` rounds encodes the pure
state after `t` rounds (`step_eq`). -/
theorem orbit_eq_encState :
    ∀ t, (∀ t' < t, acc D q (pairEncode (rawInput d)
        (StateLoop.orbit start (step E D q) (rawInput d) t')) = false) →
      StateLoop.orbit start (step E D q) (rawInput d) t = encState d (pureAt d hi t) t
  | 0, _ => start_rawInput d
  | t + 1, h => by
    have ih := orbit_eq_encState t (fun t' ht' => h t' (Nat.lt_succ_of_lt ht'))
    have hacc := h t (Nat.lt_succ_self t)
    rw [ih, acc_eq] at hacc
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, not_le] at hacc
    obtain ⟨hq, ht⟩ := hacc
    obtain ⟨x, hx⟩ := (isQ_iff d _ t).1 hq
    have hlen := pureAt_length d hi t
    rw [StateLoop.orbit_succ, ih, step_eq d _ t E hG hi (by omega) hx, pureAt_succ]

include hG hi in
/-- The stopping test fires at some round (at the latest when the budget is exhausted). -/
theorem exists_acc :
    ∃ t, acc D q (pairEncode (rawInput d) (StateLoop.orbit start (step E D q) (rawInput d) t)) =
      true := by
  by_contra hno
  have hfalse : ∀ t, acc D q (pairEncode (rawInput d)
      (StateLoop.orbit start (step E D q) (rawInput d) t)) = false := by
    intro t
    have := not_exists.1 hno t
    simpa using this
  have h := hfalse (q.eval n)
  rw [orbit_eq_encState d E hG hi (q.eval n) (fun t' _ => hfalse t'), acc_eq] at h
  simp at h

/-- The first accepted round. -/
noncomputable def firstRound : ℕ := Nat.find (exists_acc d E hG hi)

/-- Before the first accepted round the test is `false`. -/
theorem acc_of_lt_firstRound {t : ℕ} (ht : t < firstRound d E hG hi) :
    acc D q (pairEncode (rawInput d) (StateLoop.orbit start (step E D q) (rawInput d) t)) =
      false := by
  have := Nat.find_min (exists_acc d E hG hi) ht
  simpa using this

/-- The first accepted round is within the budget. -/
theorem firstRound_le : firstRound d E hG hi ≤ q.eval n := by
  by_contra h
  push_neg at h
  have hq := acc_of_lt_firstRound d E hG hi h
  rw [orbit_eq_encState d E hG hi (q.eval n)
    (fun t' ht' => acc_of_lt_firstRound d E hG hi (ht'.trans h)), acc_eq] at hq
  simp at hq

/-- Every round before the first accepted round is a query round of the pure evolution. -/
theorem isQ_of_lt_firstRound {t : ℕ} (ht : t < firstRound d E hG hi) :
    IsQ (nextQ d) (pureAt d hi t) := by
  have h := acc_of_lt_firstRound d E hG hi ht
  rw [orbit_eq_encState d E hG hi t
    (fun t' ht' => acc_of_lt_firstRound d E hG hi (ht'.trans ht)), acc_eq] at h
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, not_le] at h
  exact (isQ_iff d _ t).1 h.1

/-- The states of the first `t ≤ q(n)` rounds fit the orbit bound. -/
theorem length_encState_pureAt_le {t : ℕ} (ht : t ≤ q.eval n) :
    (encState d (pureAt d hi t) t).length ≤ (bound q).eval (rawInput d).length := by
  refine le_trans ?_ ((bound q).eval_mono (le_length_rawInput d))
  rw [length_encState]
  have hlen := pureAt_length d hi t
  simp only [bound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hA : (pureAt d hi t).1.length ≤ q.eval n := by omega
  have hB : (pureAt d hi t).2.length ≤ q.eval n := by omega
  have h1 : (pureAt d hi t).1.length * (6 * n + 6) ≤ q.eval n * (6 * n + 6) :=
    Nat.mul_le_mul_right _ hA
  have h2 : (pureAt d hi t).2.length * (4 * d.i + 2 * (2 * n) + 6) ≤ q.eval n * (8 * n + 6) :=
    Nat.mul_le_mul hB (by omega)
  have hsum : q.eval n * (28 * n + 27) =
      2 * (q.eval n * (6 * n + 6)) + 2 * (q.eval n * (8 * n + 6)) + 3 * q.eval n := by ring
  rw [hsum]
  omega

include hG in
/-- **The machine's raw function on the genuine input is the concrete verdict.**

**Proof sketch.** The state loop stops at the first accepted round `N ≤ q(n)`
(`stateLoopFun_eval` with the closed form `orbit_eq_encState` and the bound
`length_encState_pureAt_le`), where the machine outputs `D`'s verdict or the forced `false`.
Telescoping the concrete recursion over the `N` query rounds (`concrete_iterate`) reduces the
concrete verdict to budget `q(n) − N` at the pure state after `N` rounds: a verdict of `D` is
returned as is (`concrete_zero`, `concrete_succ`), and a query at `N = q(n)` is the forced
`false`. -/
theorem rawFun_rawInput :
    rawFun E D q (rawInput d) =
      [concrete (nextQ d) (prefMap d) (ansMap d hi) (stream d) (q.eval n) ([], [])] := by
  have hNq := firstRound_le d E hG hi
  have hfirst : ∀ t < firstRound d E hG hi, acc D q (pairEncode (rawInput d)
      (StateLoop.orbit start (step E D q) (rawInput d) t)) = false :=
    fun t ht => acc_of_lt_firstRound d E hG hi ht
  have hlast : acc D q (pairEncode (rawInput d)
      (StateLoop.orbit start (step E D q) (rawInput d) (firstRound d E hG hi))) = true :=
    Nat.find_spec (exists_acc d E hG hi)
  have horbN := orbit_eq_encState d E hG hi (firstRound d E hG hi) hfirst
  have hbound : ∀ t ≤ firstRound d E hG hi,
      (StateLoop.orbit start (step E D q) (rawInput d) t).length ≤
        (bound q).eval (rawInput d).length := by
    intro t ht
    rw [orbit_eq_encState d E hG hi t (fun t' ht' => hfirst t' (lt_of_lt_of_le ht' ht))]
    exact length_encState_pureAt_le d hi (ht.trans hNq)
  have hNR : firstRound d E hG hi ≤ q.eval (rawInput d).length :=
    hNq.trans (q.eval_mono (le_length_rawInput d))
  rw [rawFun, stateLoopFun_eval start (step E D q) (acc D q) (out D q) q (bound q) (rawInput d)
    (firstRound d E hG hi) hNR hbound hfirst hlast, horbN, out_eq]
  have hconc : concrete (nextQ d) (prefMap d) (ansMap d hi) (stream d) (q.eval n) ([], []) =
      concrete (nextQ d) (prefMap d) (ansMap d hi) (stream d) (q.eval n - firstRound d E hG hi)
        (pureAt d hi (firstRound d E hG hi)) := by
    have h := concrete_iterate (nextQ d) (prefMap d) (ansMap d hi) (stream d)
      (firstRound d E hG hi) (q.eval n - firstRound d E hG hi) ([], [])
      (fun t' ht' => isQ_of_lt_firstRound d E hG hi ht')
    rwa [Nat.add_sub_cancel' hNq] at h
  rw [hconc]
  have hlast' := hlast
  rw [horbN, acc_eq] at hlast'
  by_cases hQ : isQ D q (pairEncode (rawInput d)
      (encState d (pureAt d hi (firstRound d E hG hi)) (firstRound d E hG hi))) = true
  · rw [if_pos hQ]
    have hqN : q.eval n ≤ firstRound d E hG hi := by simpa [hQ] using hlast'
    rw [Nat.sub_eq_zero_of_le hqN, concrete_zero]
    obtain ⟨x, hx⟩ := (isQ_iff d _ _).1 hQ
    rw [hx]
  · rw [if_neg hQ]
    have hnone : queryOf n (nextQ d (pureAt d hi (firstRound d E hG hi)).1) = none := by
      rw [Option.eq_none_iff_forall_ne_some]
      intro x hx
      exact hQ ((isQ_iff d _ _).2 ⟨x, hx⟩)
    cases q.eval n - firstRound d E hG hi with
    | zero => rw [concrete_zero, hnone]
    | succ b => rw [concrete_succ, hnone]

end Main

/-! ## The reduction machine -/

/-- The advice-length polynomial of the reduction machine: `2(2n + 2 + q(n)) + 2 + adv_D(n)`. -/
def advPoly (D : NUPPT) (q : PolyExpr) : PolyExpr :=
  .add (.mul (.const 2) (.add (.mul (.const 2) .var) (.add (.const 2) q))) (.add (.const 2) D.adv)

/-- The coin polynomial of the reduction machine: `q(n)·n + q(n)·2n + coins_D(n)`. -/
def coinPoly (D : NUPPT) (q : PolyExpr) : PolyExpr :=
  .add (.mul q .var) (.add (.mul q (.mul (.const 2) .var)) D.coins)

/-- The advice of the reduction machine: the hybrid indices in unary (clamped to their
ranges, so that the advice is polynomially bounded at every parameter) and `D`'s advice. -/
def adviceOf (D : NUPPT) (q : PolyExpr) (i j : ℕ → ℕ) (n : ℕ) : List Bool :=
  pairEncode (pairEncode (List.replicate (min (i n) n) true)
    (List.replicate (min (j n) (q.eval n)) true)) (D.advice n)

/-- The advice is polynomially bounded. -/
theorem length_adviceOf_le (D : NUPPT) (q : PolyExpr) (i j : ℕ → ℕ) (n : ℕ) :
    (adviceOf D q i j n).length ≤ (advPoly D q).eval n := by
  simp only [adviceOf, advPoly, length_pairEncode, List.length_replicate, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have h1 := D.advice_length n
  have h2 := min_le_right (i n) n
  have h3 := min_le_right (j n) (q.eval n)
  omega

/-- **The reduction machine** of [PS10, proof of Theorem 97.3, last paragraph]: the
non-uniform PPT with advice `⟨⟨1^i, 1^j⟩, α_D⟩`, coins `q(n)·n + q(n)·2n + coins_D`, and raw
function `rawFun` (the state loop hosting `D`'s next-query function). -/
noncomputable def ggmRedMachine {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (D : NUPPT) (q : PolyExpr) (i j : ℕ → ℕ) : NUPPT :=
  NUPPT.ofPolyTime (rawFun_poly E D q hE) (coinPoly D q) (advPoly D q) (adviceOf D q i j)
    (length_adviceOf_le D q i j)

/-- The coin polynomial of the reduction machine. -/
@[simp] theorem coins_ggmRedMachine {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (D : NUPPT) (q : PolyExpr) (i j : ℕ → ℕ) :
    (ggmRedMachine hE D q i j).coins = coinPoly D q := rfl

/-- The activation of the reduction machine is the raw function on the layout. -/
theorem runAt_ggmRedMachine {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (D : NUPPT) (q : PolyExpr) (i j : ℕ → ℕ) (n : ℕ) (y : List Bool)
    (c : (ggmRedMachine hE D q i j).Coins n) :
    (ggmRedMachine hE D q i j).runAt n y c =
      rawFun E D q (NUPPT.layout (List.replicate n true) y (adviceOf D q i j n) (List.ofFn c)) := by
  show (NUPPT.ofPolyTime (rawFun_poly E D q hE) (coinPoly D q) (advPoly D q) (adviceOf D q i j)
    (length_adviceOf_le D q i j)).runAt n y c = _
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTime]
  rfl

/-- **The reduction machine computes the concrete sub-hybrid distinguisher** `ggmBitsDist`
(Thm-97.3.3, functional identity): at a parameter `n` where the hybrid indices are in range,
on the challenge `z` and coins encoding `(W, r)`, the machine's verdict is the verdict of
`ggmBitsDist (G n) D^{(q n)} (q n) i j` on `z` with coins `(W, r)`, where `D^{(q n)}` is the query
tree `buildTreeQ` of `D`'s next-query function.

**Proof sketch.** `runAt_ggmRedMachine` and `rawFun_rawInput` evaluate the machine to the
verdict `concrete … (q n) ([], [])`, which is by definition `evalLazy` of the simulated tree
with the answer stream `challengeStream`, i.e. `ggmBitsDist` unfolded (`ggmDist`, `tableDist`,
`levelAdv`). -/
theorem ggmRedMachine_distinguisher {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (D : NUPPT) (q : PolyExpr) (i j : ℕ → ℕ) {n : ℕ} (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s)) (hi : i n < n)
    (hj : j n < q.eval n) (z : Fin (2 * n) → Bool)
    (W : (Fin (q.eval n) → Fin n → Bool) × (Fin (q.eval n) → (Fin n → Bool) × (Fin n → Bool)))
    (r : D.Coins n) (c : (ggmRedMachine hE D q i j).Coins n)
    (hc : List.ofFn c = coinStr (⟨G, i n, j n, z, W, r⟩ : Data D q n)) :
    (ggmRedMachine hE D q i j).distinguisher n (2 * n) z c =
      ggmBitsDist G (fun r => buildTreeQ (fun hist => D.runAt n (histEnc hist) r) (q.eval n) [])
        (q.eval n) ⟨i n, hi⟩ ⟨j n, hj⟩ z (W, r) := by
  set d : Data D q n := ⟨G, i n, j n, z, W, r⟩ with hd
  have hraw : NUPPT.layout (List.replicate n true) (List.ofFn z) (adviceOf D q i j n)
      (List.ofFn c) = rawInput d := by
    rw [hc, rawInput, adviceOf, min_eq_left hi.le, min_eq_left hj.le]
  have hdist : (ggmRedMachine hE D q i j).distinguisher n (2 * n) z c =
      decide ([concrete (nextQ d) (prefMap d) (ansMap d hi) (stream d) (q.eval n) ([], [])] =
        [true]) := by
    rw [NUPPT.distinguisher, runAt_ggmRedMachine, hraw, rawFun_rawInput d E hG hi]
  have hrhs : ggmBitsDist G (fun r => buildTreeQ (fun hist => D.runAt n (histEnc hist) r)
      (q.eval n) []) (q.eval n) ⟨i n, hi⟩ ⟨j n, hj⟩ z (W, r) =
        concrete (nextQ d) (prefMap d) (ansMap d hi) (stream d) (q.eval n) ([], []) := rfl
  rw [hdist, hrhs]
  cases concrete (nextQ d) (prefMap d) (ansMap d hi) (stream d) (q.eval n) ([], []) <;> rfl

end TCSlib.Cryptography.GGMRed
