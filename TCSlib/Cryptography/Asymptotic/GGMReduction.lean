/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PRFLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The GGM reduction as a non-uniform PPT (machine infrastructure for Theorem 97.3)

The machine behind the last paragraph of the proof of [PS10, Theorem 97.3] ("queries to
`HHF^j` can be emulated in p.p.t. … it follows by closure under efficient operations that `D`
contradicts the pseudorandom property of `g`"): from a next-query oracle machine `D`
(foundation decision D7 of `PassShelatChapter2-4Plan.md`), the evaluator `E` of the
length-doubling generator, a query budget `q` and hybrid indices `i, j` (non-uniform advice),
a `Complexity.NUPPT` `ggmRedMachine` whose verdict on a challenge `z ∈ {0,1}^{2n}` is exactly
the verdict of the concrete sub-hybrid distinguisher `ggmBitsDist (G n) D^{(q n)} (q n) i j`
of the Garg layer (`TCSlib.Cryptography.Pseudorandom.Functions.GGM`). The identity is proved
in `ggmRedMachine_distinguisher`; `TCSlib.Cryptography.Asymptotic.PRF` wraps it into
`exists_ggmBitsDist_nuppt` (Thm-97.3.3).

**The machine.** On the raw layout `⟨⟨⟨1^n, z⟩, ⟨⟨1^i, 1^j⟩, α_D⟩⟩, W₀ ‖ W₁ ‖ r⟩` (advice: the
two indices in unary and `D`'s advice; coins: `q n` fresh `n`-bit seeds `W₀`, `q n` fresh
`2n`-bit pairs `W₁` and `D`'s coins `r`) it runs a *state loop*
(`Complexity.polyTimeComputable_iterateFind` on the length-guarded step
`Complexity.StateLoop.gstep`) over at most `q n` rounds. The state `⟨H, ⟨T, ⟨1^{|T|}, 1^t⟩⟩⟩`
holds the encoded history `H` of (query, answer) pairs handed to `D`, the lazily sampled table
`T` of (distinct `i`-bit prefix, `2n`-bit value) pairs in order of first appearance
(`QueryTree.noteQuery` / `challengeStream` of the Garg layer) with its size in unary, and the
round counter. A round runs `D` on the history (`Complexity.NUPPT.output`), decodes the move,
looks the prefix of the query up in the table (an inner `iterateFind` loop, `lookup`), draws
the value of a new prefix from the coins — the `k`-th distinct prefix gets `W₁ k` if `k < j`,
the challenge `z` if `k = j` and `E(W₀ k)` otherwise — and answers by walking the lower part
of the tree from the selected half of the value (`ggmEval` of
`TCSlib.Cryptography.Asymptotic.PRFLemmas`). The loop stops at the first verdict of `D`, or
with the forced verdict `false` after `q n` queries (D7).

**The identity.** The concrete distinguisher is `evalLazy` of the simulated query tree; its
recursion (`concrete_zero`, `concrete_succ`) matches one round of the machine
(`step_enc`), and `concrete_iterate` telescopes the rounds up to the first verdict. The
history of the text's tree is `buildTree` of `TCSlib.Cryptography.Asymptotic.PRF`; this file
uses the equivalent `Option`-valued form `buildTreeQ` (no `OracleMove`), identified with
`buildTree` in `PRF.lean`.

## Main definitions

* `TCSlib.Cryptography.GGMRed.queryOf`, `GGMRed.verdictOf`, `GGMRed.buildTreeQ`,
  `GGMRed.histEnc` — the next-query semantics in `Option` form.
* `TCSlib.Cryptography.GGMRed.tblEnc`, `GGMRed.tblOf`, `GGMRed.lookup` — the lazily sampled
  table and its lookup loop.
* `TCSlib.Cryptography.GGMRed.stateLoopFun` — the state-loop function (retained input, guarded
  step).
* `TCSlib.Cryptography.GGMRed.step`, `GGMRed.acc`, `GGMRed.out`, `GGMRed.start`,
  `GGMRed.rawFun` — the round, the stopping test, the output and the raw function of the
  reduction machine.

## Main results

* `TCSlib.Cryptography.GGMRed.stateLoopFun_poly`, `GGMRed.stateLoopFun_eval` — the state loop
  is polynomial-time and evaluates to the output at the first accepted round.
* `TCSlib.Cryptography.GGMRed.lookup_poly`, `GGMRed.lookup_tblOf` — the table lookup.
* `TCSlib.Cryptography.GGMRed.rawFun_poly` — the raw function of the reduction machine is
  polynomial-time.

The evaluation of the machine on its genuine input, the machine itself (`ggmRedMachine`) and
the functional identity with `ggmBitsDist` are in
`TCSlib.Cryptography.Asymptotic.GGMReductionEval`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8.3, proof of Theorem 97.3, last paragraph.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2 (proof of Theorem 3.3, the outer adversary `B`, footnote 9
  on lazy sampling).
-/

namespace TCSlib.Cryptography.GGMRed

open Complexity Turing Finset QueryTree

/-! ## The next-query semantics in `Option` form -/

/-- The query decoded from a machine output: `⟨[false], x⟩` with `x` an `ℓ₁`-bit string is
the query `x`; anything else is `none` (a verdict). -/
def queryOf (ℓ₁ : ℕ) (w : List Bool) : Option (Fin ℓ₁ → Bool) :=
  match pairDecode w with
  | some ([false], x) => decodeFin ℓ₁ x
  | _ => none

/-- The verdict read off a machine output that is not a query: `true` iff the output is the
two-bit string `[true, true]`. -/
def verdictOf (w : List Bool) : Bool := decide (w = [true, true])

/-- The query tree of a next-query string function `next` with budget `b` from the history
`hist` (`Option` form of `buildTree`): a verdict stops, a query within budget becomes a node,
a query at budget `0` is the forced verdict `false`. -/
def buildTreeQ {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → List Bool) :
    ℕ → List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, hist => match queryOf ℓ₁ (next hist) with
    | some _ => .ret false
    | none => .ret (verdictOf (next hist))
  | b + 1, hist => match queryOf ℓ₁ (next hist) with
    | some x => .query x (fun o => buildTreeQ next b (hist ++ [(x, o)]))
    | none => .ret (verdictOf (next hist))

/-- Unfolding `buildTreeQ` at budget `0`. -/
theorem buildTreeQ_zero {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → List Bool)
    (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
    buildTreeQ next 0 hist =
      match queryOf ℓ₁ (next hist) with
      | some _ => .ret false
      | none => .ret (verdictOf (next hist)) := rfl

/-- Unfolding `buildTreeQ` at budget `b + 1`. -/
theorem buildTreeQ_succ {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → List Bool)
    (b : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
    buildTreeQ next (b + 1) hist =
      match queryOf ℓ₁ (next hist) with
      | some x => .query x (fun o => buildTreeQ next b (hist ++ [(x, o)]))
      | none => .ret (verdictOf (next hist)) := rfl

/-- The encoding of a history of (query, answer) pairs as nested pairs (the same term as
`encodeHist` of `TCSlib.Cryptography.Asymptotic.PRF`). -/
def histEnc {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

/-- Pairing distributes over a concatenation in the second component. -/
theorem pairEncode_append_right (a b c : List Bool) :
    pairEncode a (b ++ c) = pairEncode a b ++ c := by
  simp [pairEncode_eq_dbl]

/-- A pair is never the empty word. -/
theorem pairEncode_ne_nil (a b : List Bool) : pairEncode a b ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [length_pairEncode] at this
  simp at this

/-- The encoding of a history is a flat concatenation: appending one entry appends its
encoding `⟨⟨x, y⟩, []⟩`. -/
theorem histEnc_append_single {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)))
    (p : (Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :
    histEnc (h ++ [p]) = histEnc h ++ pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) [] := by
  induction h with
  | nil => simp [histEnc]
  | cons e h ih =>
    simp only [List.cons_append, histEnc, List.foldr_cons] at ih ⊢
    rw [ih, pairEncode_append_right]

/-- The length of an encoded history: `6ℓ + 6` bits per entry (`ℓ`-bit queries and answers). -/
theorem length_histEnc {ℓ : ℕ} (h : List ((Fin ℓ → Bool) × (Fin ℓ → Bool))) :
    (histEnc h).length = h.length * (6 * ℓ + 6) := by
  induction h with
  | nil => simp [histEnc]
  | cons e h ih =>
    simp only [histEnc, List.foldr_cons] at ih ⊢
    rw [length_pairEncode, length_pairEncode, ih, List.length_ofFn, List.length_ofFn,
      List.length_cons]
    ring

/-! ## The lazily sampled table -/

/-- The encoding of a table of (prefix, value) string pairs as nested pairs
`⟨⟨p₁, v₁⟩, ⟨⟨p₂, v₂⟩, …, []⟩⟩`. -/
def tblEnc (tbl : List (List Bool × List Bool)) : List Bool :=
  tbl.foldr (fun e acc => pairEncode (pairEncode e.1 e.2) acc) []

/-- The encoding of a table is a flat concatenation: appending one entry appends its
encoding. -/
theorem tblEnc_append_single (tbl : List (List Bool × List Bool)) (e : List Bool × List Bool) :
    tblEnc (tbl ++ [e]) = tblEnc tbl ++ pairEncode (pairEncode e.1 e.2) [] := by
  induction tbl with
  | nil => simp [tblEnc]
  | cons e' tbl ih =>
    simp only [List.cons_append, tblEnc, List.foldr_cons] at ih ⊢
    rw [ih, pairEncode_append_right]

/-- The encoding of a nonempty table is `⟨⟨p, v⟩, rest⟩`. -/
@[simp] theorem tblEnc_cons (e : List Bool × List Bool) (tbl : List (List Bool × List Bool)) :
    tblEnc (e :: tbl) = pairEncode (pairEncode e.1 e.2) (tblEnc tbl) := rfl

/-- The encoding of the empty table is empty. -/
@[simp] theorem tblEnc_nil : tblEnc [] = [] := rfl

/-- A table has at most as many entries as its encoding has bits. -/
theorem length_le_length_tblEnc (tbl : List (List Bool × List Bool)) :
    tbl.length ≤ (tblEnc tbl).length := by
  induction tbl with
  | nil => simp
  | cons e tbl ih =>
    rw [tblEnc_cons, length_pairEncode, List.length_cons]
    omega

/-- The table of the distinct prefixes `L` (typed `i`-bit strings) numbered from `k`, with the
values `val k, val (k+1), …`: the entry of the `m`-th prefix is `(List.ofFn L[m], val (k + m))`. -/
def tblOf {i : ℕ} (val : ℕ → List Bool) : List (Fin i → Bool) → ℕ → List (List Bool × List Bool)
  | [], _ => []
  | p :: L, k => (List.ofFn p, val k) :: tblOf val L (k + 1)

/-- The table of `L ++ [p]` is the table of `L` with one more entry. -/
theorem tblOf_append_single {i : ℕ} (val : ℕ → List Bool) (L : List (Fin i → Bool))
    (p : Fin i → Bool) :
    ∀ k, tblOf val (L ++ [p]) k = tblOf val L k ++ [(List.ofFn p, val (k + L.length))] := by
  induction L with
  | nil => intro k; simp [tblOf]
  | cons p' L ih =>
    intro k
    simp only [List.cons_append, tblOf, ih (k + 1), List.length_cons]
    rw [show k + 1 + L.length = k + (L.length + 1) by omega]

/-- The table has one entry per prefix. -/
@[simp] theorem length_tblOf {i : ℕ} (val : ℕ → List Bool) (L : List (Fin i → Bool)) :
    ∀ k, (tblOf val L k).length = L.length := by
  induction L with
  | nil => intro k; rfl
  | cons p L ih => intro k; simp [tblOf, ih]

/-- The prefixes of the table are the encoded prefixes. -/
theorem tblOf_getElem_fst {i : ℕ} (val : ℕ → List Bool) (L : List (Fin i → Bool)) :
    ∀ (k m : ℕ) (hm : m < (tblOf val L k).length),
      (tblOf val L k)[m].1 = List.ofFn (L[m]'(by simpa using hm)) := by
  induction L with
  | nil => intro k m hm; simp at hm
  | cons p L ih =>
    intro k m hm
    cases m with
    | zero => rfl
    | succ m => exact ih (k + 1) m (by simpa using hm)

/-- The values of the table are `val (k + m)`. -/
theorem tblOf_getElem_snd {i : ℕ} (val : ℕ → List Bool) (L : List (Fin i → Bool)) :
    ∀ (k m : ℕ) (hm : m < (tblOf val L k).length), (tblOf val L k)[m].2 = val (k + m) := by
  induction L with
  | nil => intro k m hm; simp at hm
  | cons p L ih =>
    intro k m hm
    cases m with
    | zero => rfl
    | succ m =>
      simp only [tblOf, List.getElem_cons_succ]
      rw [ih (k + 1) m (by simpa using hm)]
      congr 1
      omega

/-- The length of the encoded table of `L` when every value has `v` bits: `4i + 2v + 6` bits
per entry. -/
theorem length_tblEnc_tblOf {i : ℕ} (val : ℕ → List Bool) {v : ℕ}
    (hval : ∀ k, (val k).length = v) (L : List (Fin i → Bool)) :
    ∀ k, (tblEnc (tblOf val L k)).length = L.length * (4 * i + 2 * v + 6) := by
  induction L with
  | nil => intro k; simp [tblOf]
  | cons p L ih =>
    intro k
    simp only [tblOf, tblEnc_cons, length_pairEncode, List.length_ofFn, hval, ih (k + 1),
      List.length_cons]
    ring


/-! ## State loops with a retained input -/

/-- **The state-loop function** (the function form of the private
`Complexity.polyTimeComputable_stateFind` of `TCSlib.Complexity.Randomized.Repetition`): on the
input `x`, run the length-guarded step `Complexity.StateLoop.gstep step B` from `⟨x, start x⟩`
for at most `R|⟨x, start x⟩|` rounds and return `out` of the first state word accepted by `acc`
(`[]` if none). -/
def stateLoopFun (start step : List Bool → List Bool) (acc : List Bool → Bool)
    (out : List Bool → List Bool) (R B : PolyExpr) (x : List Bool) : List Bool :=
  match (List.range (R.eval (pairEncode x (start x)).length + 1)).find?
      (fun i => acc ((StateLoop.gstep step B)^[i] (pairEncode x (start x)))) with
  | some i => out ((StateLoop.gstep step B)^[i] (pairEncode x (start x)))
  | none => []

/-- The state-loop function is polynomial-time (`Complexity.polyTimeComputable_iterateFind` on
the guarded step, whose orbit from every word is bounded by `StateLoop.gstepBound B`). -/
theorem stateLoopFun_poly {start step : List Bool → List Bool} {acc : List Bool → Bool}
    {out : List Bool → List Bool} (hstart : PolyTimeComputable start)
    (hstep : PolyTimeComputable step) (hacc : PolyTimeComputable fun w => [acc w])
    (hout : PolyTimeComputable out) (R B : PolyExpr) :
    PolyTimeComputable (stateLoopFun start step acc out R B) := by
  have hF := polyTimeComputable_iterateFind (StateLoop.gstep_poly hstep B) hacc hout R
    (StateLoop.gstepBound B) (fun w i _ => StateLoop.length_gstep_iterate_le step B w i)
  have hpre : PolyTimeComputable fun x => pairEncode x (start x) :=
    polyTimeComputable_id.pairEncode hstart
  exact hF.comp hpre

/-- **Evaluation of the state loop on a good input:** if the test first fires at round
`N ≤ R|x|` and the states of the first `N` rounds fit the bound `B|x|`, the loop returns
`out ⟨x, orbit x N⟩`.

**Proof sketch.** On the genuine orbit the guard never fires (`StateLoop.gstep_iterate_eq`
from the bound on the first `N` states), so the loop's `find?` over
`List.range (R|⟨x, start x⟩| + 1)` — a range containing `N`, as `R` is monotone — returns
`some N` (`StateLoop.find?_range_eq_some`), and the payload is `out ⟨x, orbit x N⟩`. -/
theorem stateLoopFun_eval (start step : List Bool → List Bool) (acc : List Bool → Bool)
    (out : List Bool → List Bool) (R B : PolyExpr) (x : List Bool) (N : ℕ)
    (hN : N ≤ R.eval x.length)
    (hbound : ∀ i ≤ N, (StateLoop.orbit start step x i).length ≤ B.eval x.length)
    (hfirst : ∀ i < N, acc (pairEncode x (StateLoop.orbit start step x i)) = false)
    (hlast : acc (pairEncode x (StateLoop.orbit start step x N)) = true) :
    stateLoopFun start step acc out R B x = out (pairEncode x (StateLoop.orbit start step x N)) := by
  unfold stateLoopFun
  have horb := StateLoop.gstep_iterate_eq start step B x N hbound
  have hle : N ≤ R.eval (pairEncode x (start x)).length :=
    hN.trans (R.eval_mono (by rw [length_pairEncode]; omega))
  have hfind : (List.range (R.eval (pairEncode x (start x)).length + 1)).find?
      (fun i => acc ((StateLoop.gstep step B)^[i] (pairEncode x (start x)))) = some N := by
    apply StateLoop.find?_range_eq_some hle
    · intro i hi
      rw [horb i hi.le]
      exact hfirst i hi
    · rw [horb N le_rfl]
      exact hlast
  rw [hfind]
  show out ((StateLoop.gstep step B)^[N] (pairEncode x (start x))) = _
  rw [horb N le_rfl]

/-! ## The table lookup loop -/

/-- The step of the lookup loop on the word `⟨p, T⟩`: pop the first entry of the table. -/
def lookStep (v : List Bool) : List Bool := pairEncode (pairFstD v) (pairSndD (pairSndD v))

/-- The acceptance test of the lookup loop: the table is exhausted or its first entry has the
prefix `p`. -/
def lookAcc (v : List Bool) : Bool :=
  decide (pairSndD v = []) || decide (pairFstD (pairFstD (pairSndD v)) = pairFstD v)

/-- The output of the lookup loop: `[]` if the table is exhausted (not found), else `⟨[], v⟩`
with `v` the value of the first entry. -/
def lookOut (v : List Bool) : List Bool :=
  if pairSndD v = [] then [] else pairEncode [] (pairSndD (pairFstD (pairSndD v)))

/-- **The table lookup:** on `⟨p, T⟩` pop entries until the table is exhausted or the first
entry has prefix `p`; at most `|⟨p, T⟩|` rounds (`Complexity.polyTimeComputable_iterateFind`). -/
def lookup (v : List Bool) : List Bool :=
  match (List.range ((PolyExpr.var).eval v.length + 1)).find? (fun k => lookAcc (lookStep^[k] v)) with
  | some k => lookOut (lookStep^[k] v)
  | none => []

/-- The lookup step is polynomial-time. -/
theorem lookStep_poly : PolyTimeComputable lookStep :=
  polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The lookup test is polynomial-time (`StateLoop.isNil_poly`, `polyTimeComputable_pairEq`,
`StateLoop.or_poly`). -/
theorem lookAcc_poly : PolyTimeComputable fun v => [lookAcc v] := by
  have h1 : PolyTimeComputable fun v => [decide (pairSndD v = [])] :=
    StateLoop.isNil_poly.comp polyTimeComputable_pairSndD
  have h2 : PolyTimeComputable fun v => [decide (pairFstD (pairFstD (pairSndD v)) = pairFstD v)] := by
    convert polyTimeComputable_pairEq.comp
      ((polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
        polyTimeComputable_pairSndD)).pairEncode polyTimeComputable_pairFstD) using 1
    funext v
    simp
  exact StateLoop.or_poly h1 h2

/-- The lookup output is polynomial-time. -/
theorem lookOut_poly : PolyTimeComputable lookOut := by
  have h1 : PolyTimeComputable fun v => [decide (pairSndD v = [])] :=
    StateLoop.isNil_poly.comp polyTimeComputable_pairSndD
  convert polyTimeComputable_ite h1 (polyTimeComputable_const [])
    ((polyTimeComputable_const []).pairEncode (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))) using 1
  funext v
  simp [lookOut]

/-- The orbit of the lookup step from any word stays within two bits of the word.

**Proof sketch.** Every point of the orbit after the first step is a pair `⟨p, T⟩`, and the step
on a pair pops the first entry of `T`, which never lengthens the word; the first step itself adds
at most the two separator bits (a malformed word is turned into `⟨[], []⟩`). -/
theorem length_lookStep_iterate_le (v : List Bool) (k : ℕ) :
    (lookStep^[k] v).length ≤ v.length + 2 := by
  have hpair : ∀ a b : List Bool, (lookStep (pairEncode a b)).length ≤ (pairEncode a b).length := by
    intro a b
    unfold lookStep
    rw [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode, length_pairEncode]
    have h1 := StateLoop.length_pairFstD_add_pairSndD_le b
    omega
  have hone : (lookStep v).length ≤ v.length + 2 := by
    cases hd : pairDecode v with
    | none =>
      have h1 : pairFstD v = [] := by simp [pairFstD, hd]
      have h2 : pairSndD v = [] := by simp [pairSndD, hd]
      have h3 : pairSndD ([] : List Bool) = [] := rfl
      unfold lookStep
      rw [h1, h2, h3, length_pairEncode]
      simp
    | some ab =>
      obtain ⟨a, b⟩ := ab
      rw [eq_pairEncode_of_pairDecode v a b hd]
      exact (hpair a b).trans (Nat.le_add_right _ _)
  cases k with
  | zero => exact Nat.le_add_right _ _
  | succ k =>
    induction k with
    | zero => exact hone
    | succ k ih =>
      rw [Function.iterate_succ_apply' lookStep (k + 1) v]
      refine le_trans ?_ ih
      rw [Function.iterate_succ_apply' lookStep k v]
      exact hpair (pairFstD (lookStep^[k] v)) (pairSndD (pairSndD (lookStep^[k] v)))

/-- The lookup is polynomial-time (`Complexity.polyTimeComputable_iterateFind` with `R = var`
and the orbit bound `var + 2`). -/
theorem lookup_poly : PolyTimeComputable lookup :=
  polyTimeComputable_iterateFind lookStep_poly lookAcc_poly lookOut_poly .var
    (.add .var (.const 2)) (fun v k _ => by
      simpa using length_lookStep_iterate_le v k)

/-- The orbit of the lookup step on `⟨p, tblEnc tbl⟩`: after `k` steps the first `k` entries
are gone. -/
theorem lookStep_iterate_tblEnc (p : List Bool) :
    ∀ (k : ℕ) (tbl : List (List Bool × List Bool)),
      lookStep^[k] (pairEncode p (tblEnc tbl)) = pairEncode p (tblEnc (tbl.drop k))
  | 0, tbl => by simp
  | k + 1, tbl => by
    rw [Function.iterate_succ_apply]
    cases tbl with
    | nil =>
      have h : lookStep (pairEncode p (tblEnc [])) = pairEncode p (tblEnc []) := by
        show pairEncode (pairFstD _) (pairSndD (pairSndD _)) = _
        rw [pairFstD_pairEncode, pairSndD_pairEncode]
        rfl
      rw [h, lookStep_iterate_tblEnc p k []]
      simp
    | cons e tbl =>
      have h : lookStep (pairEncode p (tblEnc (e :: tbl))) = pairEncode p (tblEnc tbl) := by
        simp [lookStep]
      rw [h, lookStep_iterate_tblEnc p k tbl, List.drop_succ_cons]

/-- The lookup test on `⟨p, tblEnc tbl⟩`: the table is empty or its first prefix is `p`. -/
theorem lookAcc_tblEnc (p : List Bool) (tbl : List (List Bool × List Bool)) :
    lookAcc (pairEncode p (tblEnc tbl)) =
      match tbl with
      | [] => true
      | e :: _ => decide (e.1 = p) := by
  cases tbl with
  | nil => simp [lookAcc]
  | cons e tbl =>
    simp only [lookAcc, pairSndD_pairEncode, tblEnc_cons, pairFstD_pairEncode]
    have hne : pairEncode (pairEncode e.1 e.2) (tblEnc tbl) ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [length_pairEncode] at this
      simp at this
    simp [hne]

/-- **The lookup on an encoded table of the distinct prefixes `L`** (with `p` a typed prefix):
`⟨[], val (L.idxOf p)⟩` if `p ∈ L`, else `[]`.

**Proof sketch.** The orbit is `⟨p, tblEnc (tbl.drop k)⟩` (`lookStep_iterate_tblEnc`); the test
fails at round `k < L.idxOf p` because the `k`-th prefix differs from `p`
(`List.not_of_lt_findIdx`, `List.ofFn_injective`) and succeeds at round `L.idxOf p`, where the
table either starts with `p` (`List.getElem_idxOf`) or is exhausted (`List.idxOf_eq_length`);
`StateLoop.find?_range_eq_some` evaluates the `find?`. -/
theorem lookup_tblOf {i : ℕ} (val : ℕ → List Bool) (L : List (Fin i → Bool)) (p : Fin i → Bool) :
    lookup (pairEncode (List.ofFn p) (tblEnc (tblOf val L 0))) =
      if p ∈ L then pairEncode [] (val (L.idxOf p)) else [] := by
  classical
  have hlen : (tblOf val L 0).length = L.length := length_tblOf val L 0
  have hacc : ∀ k, lookAcc (lookStep^[k] (pairEncode (List.ofFn p) (tblEnc (tblOf val L 0)))) =
      match (tblOf val L 0).drop k with
      | [] => true
      | e :: _ => decide (e.1 = List.ofFn p) := by
    intro k
    rw [lookStep_iterate_tblEnc, lookAcc_tblEnc]
  have hidx_le : L.idxOf p ≤ L.length := List.idxOf_le_length
  have hrange : L.idxOf p ≤
      (PolyExpr.var).eval (pairEncode (List.ofFn p) (tblEnc (tblOf val L 0))).length := by
    simp only [PolyExpr.eval_var, length_pairEncode]
    have := length_le_length_tblEnc (tblOf val L 0)
    omega
  have hfirst : ∀ k < L.idxOf p,
      lookAcc (lookStep^[k] (pairEncode (List.ofFn p) (tblEnc (tblOf val L 0)))) = false := by
    intro k hk
    rw [hacc]
    have hkL : k < L.length := lt_of_lt_of_le hk hidx_le
    have hkt : k < (tblOf val L 0).length := by rw [hlen]; exact hkL
    rw [List.drop_eq_getElem_cons hkt]
    simp only
    have hne : L[k] ≠ p := by
      have := List.not_of_lt_findIdx (p := (· == p)) (xs := L) hk
      simpa using this
    rw [tblOf_getElem_fst val L 0 k hkt]
    simp only [decide_eq_false_iff_not]
    intro h
    exact hne (List.ofFn_injective h)
  by_cases hp : p ∈ L
  · have hlt : L.idxOf p < L.length := List.idxOf_lt_length_of_mem hp
    have hltt : L.idxOf p < (tblOf val L 0).length := by rw [hlen]; exact hlt
    have hlast : lookAcc (lookStep^[L.idxOf p]
        (pairEncode (List.ofFn p) (tblEnc (tblOf val L 0)))) = true := by
      rw [hacc, List.drop_eq_getElem_cons hltt]
      simp only
      rw [tblOf_getElem_fst val L 0 _ hltt]
      simp [List.getElem_idxOf hlt]
    unfold lookup
    rw [StateLoop.find?_range_eq_some hrange hfirst hlast, if_pos hp]
    show lookOut _ = _
    rw [lookStep_iterate_tblEnc, List.drop_eq_getElem_cons hltt]
    simp only [lookOut, pairSndD_pairEncode, tblEnc_cons, pairFstD_pairEncode]
    have hne : pairEncode (pairEncode (tblOf val L 0)[L.idxOf p].1 (tblOf val L 0)[L.idxOf p].2)
        (tblEnc ((tblOf val L 0).drop (L.idxOf p + 1))) ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [length_pairEncode] at this
      simp at this
    rw [if_neg hne, tblOf_getElem_snd val L 0 _ hltt, zero_add]
  · have heq : L.idxOf p = L.length := List.idxOf_eq_length hp
    have hlast : lookAcc (lookStep^[L.idxOf p]
        (pairEncode (List.ofFn p) (tblEnc (tblOf val L 0)))) = true := by
      rw [hacc, List.drop_of_length_le (by rw [hlen, heq])]
    unfold lookup
    rw [StateLoop.find?_range_eq_some hrange hfirst hlast, if_neg hp]
    show lookOut _ = _
    rw [lookStep_iterate_tblEnc, List.drop_of_length_le (by rw [hlen, heq])]
    simp [lookOut]



/-! ## The components of the reduction machine -/

section Machine

variable (E : List Bool → List Bool) (D : NUPPT) (q : PolyExpr)

/-- The retained raw input of the state word `⟨X, S⟩`. -/
def inX (w : List Bool) : List Bool := pairFstD w

/-- The state of the state word `⟨X, S⟩`. -/
def inS (w : List Bool) : List Bool := pairSndD w

/-- The unary parameter `1^n` of the raw input. -/
def paramU (w : List Bool) : List Bool := NUPPT.inParam (inX w)

/-- The challenge `z` (the argument of the raw input). -/
def chal (w : List Bool) : List Bool := NUPPT.inArg (inX w)

/-- The level index `1^i` (first half of the first advice component). -/
def unI (w : List Bool) : List Bool := pairFstD (pairFstD (NUPPT.inAdvice (inX w)))

/-- The sub-hybrid index `1^j` (second half of the first advice component). -/
def unJ (w : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inAdvice (inX w)))

/-- `D`'s advice (second advice component). -/
def advD (w : List Bool) : List Bool := pairSndD (NUPPT.inAdvice (inX w))

/-- The whole coin string `W₀ ‖ W₁ ‖ r`. -/
def coinsAll (w : List Bool) : List Bool := NUPPT.inCoins (inX w)

/-- The `q(n)` fresh `n`-bit seeds `W₀` (the first `q(n)·n` coins). -/
def seeds (w : List Bool) : List Bool :=
  (coinsAll w).take ((PolyExpr.mul q .var).eval (paramU w).length)

/-- The coins after the seeds. -/
def coinsRest (w : List Bool) : List Bool :=
  (coinsAll w).drop ((PolyExpr.mul q .var).eval (paramU w).length)

/-- The `q(n)` fresh `2n`-bit pairs `W₁` (the next `q(n)·2n` coins). -/
def pairs (w : List Bool) : List Bool :=
  (coinsRest q w).take ((PolyExpr.mul q (.mul (.const 2) .var)).eval (paramU w).length)

/-- `D`'s coins (the remaining coins). -/
def coinsD (w : List Bool) : List Bool :=
  (coinsRest q w).drop ((PolyExpr.mul q (.mul (.const 2) .var)).eval (paramU w).length)

/-- The encoded history in the state. -/
def hist (w : List Bool) : List Bool := pairFstD (inS w)

/-- The encoded table in the state. -/
def tbl (w : List Bool) : List Bool := pairFstD (pairSndD (inS w))

/-- The table size `1^{|T|}` in the state. -/
def cnt (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (inS w)))

/-- The round counter `1^t` in the state. -/
def rnd (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (inS w)))

/-- `D`'s move on the current history: `D(1^n, H; r)` with `D`'s advice. -/
def move (w : List Bool) : List Bool :=
  D.output (NUPPT.layout (paramU w) (hist w) (advD w) (coinsD q w))

/-- The move is a query: `⟨[false], x⟩` with `|x| = n`. -/
def isQ (w : List Bool) : Bool :=
  decide (pairFstD (move D q w) = [false]) &&
    decide ((pairSndD (move D q w)).length = (paramU w).length)

/-- The query string `x`. -/
def query (w : List Bool) : List Bool := pairSndD (move D q w)

/-- The `i`-bit prefix of the query. -/
def pfx (w : List Bool) : List Bool := (query D q w).take (unI w).length

/-- The table lookup of the prefix. -/
def look (w : List Bool) : List Bool := lookup (pairEncode (pfx D q w) (tbl w))

/-- The unary string `1^{2n}`. -/
def un2 (w : List Bool) : List Bool :=
  List.replicate ((PolyExpr.mul (.const 2) .var).eval (paramU w).length) true

/-- The unary product `1^{n·|T|}` (offset of seed number `|T|`). -/
def mul1 (w : List Bool) : List Bool :=
  List.replicate ((paramU w).length * (cnt w).length) true

/-- The unary product `1^{2n·|T|}` (offset of pair number `|T|`). -/
def mul2 (w : List Bool) : List Bool :=
  List.replicate ((un2 w).length * (cnt w).length) true

/-- The test `|T| < j`. -/
def ltJ (w : List Bool) : Bool := !decide ((unJ w).length ≤ (cnt w).length)

/-- The test `|T| = j`. -/
def eqJ (w : List Bool) : Bool := decide ((cnt w).length = (unJ w).length)

/-- The value of a new (the `|T|`-th distinct) prefix: the pair `W₁ |T|` if `|T| < j`, the
challenge if `|T| = j`, `E(W₀ |T|)` otherwise (`challengeStream`). -/
def fresh (w : List Bool) : List Bool :=
  if ltJ w then ((pairs q w).drop (mul2 w).length).take (un2 w).length
  else if eqJ w then chal w
  else E (((seeds q w).drop (mul1 w).length).take (paramU w).length)

/-- The prefix is not in the table. -/
def notFound (w : List Bool) : Bool := decide (look D q w = [])

/-- The value of the query's prefix: looked up, or fresh. -/
def vstr (w : List Bool) : List Bool :=
  if notFound D q w then fresh E q w else pairSndD (look D q w)

/-- The updated table: a new prefix is appended with its fresh value. -/
def tbl' (w : List Bool) : List Bool :=
  if notFound D q w then tbl w ++ pairEncode (pairEncode (pfx D q w) (fresh E q w)) [] else tbl w

/-- The updated table size. -/
def cnt' (w : List Bool) : List Bool := if notFound D q w then true :: cnt w else cnt w

/-- The label at level `i + 1`: the half of the value selected by bit `x_{i+1}` of the query. -/
def lab (w : List Bool) : List Bool :=
  selHalf (((query D q w).drop (unI w).length).headD false) (paramU w) (vstr E D q w)

/-- The answer: the walk down the tree from the label along the remaining bits of the query. -/
def ans (w : List Bool) : List Bool :=
  ggmEval E (pairEncode (lab E D q w) ((query D q w).drop (unI w).length).tail)

/-- The updated history. -/
def hist' (w : List Bool) : List Bool :=
  hist w ++ pairEncode (pairEncode (query D q w) (ans E D q w)) []

/-- **One round of the reduction machine** on the state word `⟨X, S⟩`. -/
def step (w : List Bool) : List Bool :=
  pairEncode (hist' E D q w) (pairEncode (tbl' E D q w) (pairEncode (cnt' D q w) (true :: rnd w)))

/-- The query budget `1^{q(n)}`. -/
def unQ (w : List Bool) : List Bool := List.replicate (q.eval (paramU w).length) true

/-- The stopping test: the move is a verdict, or the budget is exhausted. -/
def acc (w : List Bool) : Bool := !(isQ D q w) || decide ((unQ q w).length ≤ (rnd w).length)

/-- The output: the forced verdict `false` on a query (budget exhausted), else `D`'s verdict. -/
def out (w : List Bool) : List Bool := if isQ D q w then [false] else [verdictOf (move D q w)]

/-- The initial state: empty history, empty table, zero counters. -/
def start (_X : List Bool) : List Bool := pairEncode [] (pairEncode [] (pairEncode [] []))

/-- The orbit bound of the state loop: `q(n)(28n + 27) + 6`. -/
def bound : PolyExpr := .add (.mul q (.add (.mul (.const 28) .var) (.const 27))) (.const 6)

/-- **The raw function of the reduction machine:** the state loop with at most `q(|X|)`
rounds. -/
def rawFun : List Bool → List Bool := stateLoopFun start (step E D q) (acc D q) (out D q) q (bound q)

/-! ### Polynomial time -/

/-- Unary multiplication of two polynomial-time unary lengths
(`Turing.FinTM.computesFunInTime_unaryMul`). -/
theorem unaryMul_poly {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun w => List.replicate ((f w).length * (g w).length) true := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  have hmul : PolyTimeComputable (fun z => match pairDecode z with
      | some (u, v) => List.replicate (u.length * v.length) true
      | none => []) := ⟨M, c, 2, hM⟩
  convert hmul.comp (hf.pairEncode hg) using 1
  funext w
  simp [pairDecode_pairEncode]

/-- The retained input of the state word is polynomial-time. -/
theorem inX_poly : PolyTimeComputable inX := polyTimeComputable_pairFstD
/-- The state of the state word is polynomial-time. -/
theorem inS_poly : PolyTimeComputable inS := polyTimeComputable_pairSndD
/-- The unary parameter is polynomial-time. -/
theorem paramU_poly : PolyTimeComputable paramU := NUPPT.polyTimeComputable_inParam.comp inX_poly
/-- The challenge is polynomial-time. -/
theorem chal_poly : PolyTimeComputable chal := NUPPT.polyTimeComputable_inArg.comp inX_poly
/-- The level index is polynomial-time. -/
theorem unI_poly : PolyTimeComputable unI :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
    (NUPPT.polyTimeComputable_inAdvice.comp inX_poly))
/-- The sub-hybrid index is polynomial-time. -/
theorem unJ_poly : PolyTimeComputable unJ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
    (NUPPT.polyTimeComputable_inAdvice.comp inX_poly))
/-- `D`'s advice is polynomial-time. -/
theorem advD_poly : PolyTimeComputable advD :=
  polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inAdvice.comp inX_poly)
/-- The coin string is polynomial-time. -/
theorem coinsAll_poly : PolyTimeComputable coinsAll := NUPPT.polyTimeComputable_inCoins.comp inX_poly

/-- The seeds are polynomial-time (`Complexity.polyTimeComputable_pairTakePoly`). -/
theorem seeds_poly : PolyTimeComputable (seeds q) := by
  convert (polyTimeComputable_pairTakePoly (.mul q .var)).comp (paramU_poly.pairEncode coinsAll_poly)
    using 1
  funext w
  simp [seeds]

/-- The coins after the seeds are polynomial-time (`Complexity.polyTimeComputable_pairDropPoly`). -/
theorem coinsRest_poly : PolyTimeComputable (coinsRest q) := by
  convert (polyTimeComputable_pairDropPoly (.mul q .var)).comp (paramU_poly.pairEncode coinsAll_poly)
    using 1
  funext w
  simp [coinsRest]

/-- The pairs are polynomial-time. -/
theorem pairs_poly : PolyTimeComputable (pairs q) := by
  convert (polyTimeComputable_pairTakePoly (.mul q (.mul (.const 2) .var))).comp
    (paramU_poly.pairEncode (coinsRest_poly q)) using 1
  funext w
  simp [pairs]

/-- `D`'s coins are polynomial-time. -/
theorem coinsD_poly : PolyTimeComputable (coinsD q) := by
  convert (polyTimeComputable_pairDropPoly (.mul q (.mul (.const 2) .var))).comp
    (paramU_poly.pairEncode (coinsRest_poly q)) using 1
  funext w
  simp [coinsD]

/-- The encoded history is polynomial-time. -/
theorem hist_poly : PolyTimeComputable hist := polyTimeComputable_pairFstD.comp inS_poly
/-- The encoded table is polynomial-time. -/
theorem tbl_poly : PolyTimeComputable tbl :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp inS_poly)
/-- The table size is polynomial-time. -/
theorem cnt_poly : PolyTimeComputable cnt :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp inS_poly))
/-- The round counter is polynomial-time. -/
theorem rnd_poly : PolyTimeComputable rnd :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp inS_poly))

/-- `D`'s move is polynomial-time (`Complexity.NUPPT.polyTimeComputable_output`). -/
theorem move_poly : PolyTimeComputable (move D q) :=
  D.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout paramU_poly hist_poly advD_poly (coinsD_poly q))

/-- The query test is polynomial-time (`polyTimeComputable_pairEq`, `polyTimeComputable_lenEq`). -/
theorem isQ_poly : PolyTimeComputable fun w => [isQ D q w] := by
  have h1 : PolyTimeComputable fun w => [decide (pairFstD (move D q w) = [false])] := by
    convert polyTimeComputable_pairEq.comp
      ((polyTimeComputable_pairFstD.comp (move_poly D q)).pairEncode
        (polyTimeComputable_const [false])) using 1
    funext w
    simp
  have h2 : PolyTimeComputable fun w =>
      [decide ((pairSndD (move D q w)).length = (paramU w).length)] := by
    convert polyTimeComputable_lenEq.comp
      ((polyTimeComputable_pairSndD.comp (move_poly D q)).pairEncode paramU_poly) using 1
    funext w
    simp
  exact polyTimeComputable_and h1 h2

/-- The query string is polynomial-time. -/
theorem query_poly : PolyTimeComputable (query D q) := polyTimeComputable_pairSndD.comp (move_poly D q)
/-- The prefix of the query is polynomial-time (`takeLen_poly`). -/
theorem pfx_poly : PolyTimeComputable (pfx D q) := takeLen_poly unI_poly (query_poly D q)
/-- The table lookup is polynomial-time (`lookup_poly`). -/
theorem look_poly : PolyTimeComputable (look D q) := lookup_poly.comp ((pfx_poly D q).pairEncode tbl_poly)
/-- The unary string `1^{2n}` is polynomial-time. -/
theorem un2_poly : PolyTimeComputable un2 := StateLoop.unaryPoly_comp (.mul (.const 2) .var) paramU_poly
/-- The seed offset is polynomial-time (`unaryMul_poly`). -/
theorem mul1_poly : PolyTimeComputable mul1 := unaryMul_poly paramU_poly cnt_poly
/-- The pair offset is polynomial-time (`unaryMul_poly`). -/
theorem mul2_poly : PolyTimeComputable mul2 := unaryMul_poly un2_poly cnt_poly
/-- The test `|T| < j` is polynomial-time. -/
theorem ltJ_poly : PolyTimeComputable fun w => [ltJ w] :=
  StateLoop.not_poly (StateLoop.lenLe_comp cnt_poly unJ_poly)

/-- The test `|T| = j` is polynomial-time. -/
theorem eqJ_poly : PolyTimeComputable fun w => [eqJ w] := by
  convert polyTimeComputable_lenEq.comp (cnt_poly.pairEncode unJ_poly) using 1
  funext w
  simp [eqJ]

/-- The fresh value is polynomial-time (two branches, `takeLen_poly`/`dropLen_poly`, `E`). -/
theorem fresh_poly (hE : PolyTimeComputable E) : PolyTimeComputable (fresh E q) :=
  polyTimeComputable_ite ltJ_poly (takeLen_poly un2_poly (dropLen_poly mul2_poly (pairs_poly q)))
    (polyTimeComputable_ite eqJ_poly chal_poly
      (hE.comp (takeLen_poly paramU_poly (dropLen_poly mul1_poly (seeds_poly q)))))

/-- The not-found test is polynomial-time. -/
theorem notFound_poly : PolyTimeComputable fun w => [notFound D q w] :=
  StateLoop.isNil_poly.comp (look_poly D q)

/-- The value of the prefix is polynomial-time. -/
theorem vstr_poly (hE : PolyTimeComputable E) : PolyTimeComputable (vstr E D q) :=
  polyTimeComputable_ite (notFound_poly D q) (fresh_poly E q hE)
    (polyTimeComputable_pairSndD.comp (look_poly D q))

/-- The updated table is polynomial-time. -/
theorem tbl'_poly (hE : PolyTimeComputable E) : PolyTimeComputable (tbl' E D q) :=
  polyTimeComputable_ite (notFound_poly D q)
    (tbl_poly.append (((pfx_poly D q).pairEncode (fresh_poly E q hE)).pairEncode
      (polyTimeComputable_const []))) tbl_poly

/-- The updated table size is polynomial-time. -/
theorem cnt'_poly : PolyTimeComputable (cnt' D q) :=
  polyTimeComputable_ite (notFound_poly D q) ((StateLoop.cons_poly true).comp cnt_poly) cnt_poly

/-- The label is polynomial-time (`selHalf_poly`). -/
theorem lab_poly (hE : PolyTimeComputable E) : PolyTimeComputable (lab E D q) :=
  selHalf_poly (StateLoop.headBit_poly.comp (dropLen_poly unI_poly (query_poly D q))) paramU_poly
    (vstr_poly E D q hE)

/-- The answer is polynomial-time (`ggmEval_poly`). -/
theorem ans_poly (hE : PolyTimeComputable E) : PolyTimeComputable (ans E D q) :=
  (ggmEval_poly hE).comp ((lab_poly E D q hE).pairEncode
    (StateLoop.tail_poly.comp (dropLen_poly unI_poly (query_poly D q))))

/-- The updated history is polynomial-time. -/
theorem hist'_poly (hE : PolyTimeComputable E) : PolyTimeComputable (hist' E D q) :=
  hist_poly.append (((query_poly D q).pairEncode (ans_poly E D q hE)).pairEncode
    (polyTimeComputable_const []))

/-- One round of the machine is polynomial-time. -/
theorem step_poly (hE : PolyTimeComputable E) : PolyTimeComputable (step E D q) :=
  (hist'_poly E D q hE).pairEncode ((tbl'_poly E D q hE).pairEncode
    ((cnt'_poly D q).pairEncode ((StateLoop.cons_poly true).comp rnd_poly)))

/-- The query budget is polynomial-time (`Complexity.polyTimeComputable_unaryPoly`). -/
theorem unQ_poly : PolyTimeComputable (unQ q) := StateLoop.unaryPoly_comp q paramU_poly

/-- The stopping test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun w => [acc D q w] :=
  StateLoop.or_poly (StateLoop.not_poly (isQ_poly D q)) (StateLoop.lenLe_comp rnd_poly (unQ_poly q))

/-- The output is polynomial-time (`polyTimeComputable_pairEq` for the verdict). -/
theorem out_poly : PolyTimeComputable (out D q) := by
  have hv : PolyTimeComputable fun w => [verdictOf (move D q w)] := by
    convert polyTimeComputable_pairEq.comp
      ((move_poly D q).pairEncode (polyTimeComputable_const [true, true])) using 1
    funext w
    simp [verdictOf]
  exact polyTimeComputable_ite (isQ_poly D q) (polyTimeComputable_const [false]) hv

/-- The initial state is polynomial-time (a constant). -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_const (pairEncode [] (pairEncode [] (pairEncode [] [])))

/-- **The raw function of the reduction machine is polynomial-time.** -/
theorem rawFun_poly (hE : PolyTimeComputable E) : PolyTimeComputable (rawFun E D q) :=
  stateLoopFun_poly start_poly (step_poly E D q hE) (acc_poly D q) (out_poly D q) q (bound q)

end Machine

end TCSlib.Cryptography.GGMRed
