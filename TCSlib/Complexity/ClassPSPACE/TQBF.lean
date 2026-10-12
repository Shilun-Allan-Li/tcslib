/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.QBFEncoding
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.Inclusions
import TCSlib.Complexity.TuringMachine.Build.CfgRecord

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `PSPACE`-completeness and `TQBF`

[AB09, §4.2]: `PSPACE`-hardness and -completeness (Definition 4.9), the
adjacency-formula half of Claim 4.4(2), and the Stockmeyer-Meyer theorem that
`TQBF` is `PSPACE`-complete (Theorem 4.13). Phase P4.3 of
`AroraBarakChapters3-4Plan.md`.

## Design

* **Def 4.9 verbatim over the campaign's `≤ₚ`** (`Complexity.PolyTimeReducible`,
  chapter 2); the logspace-reduction variant ([AB09, Exercise 4.9]) waits for
  phase P4.4's `≤ₗ`.
* **Claim 4.4(2) at polynomial size, over a packaged quotient codec.** The
  statement supplies, for each machine and each `(n, s)`: a configuration
  bit-codec of fixed length linear in `s + n`, **factoring through the input
  and the P4.2 vertex quotient** `Turing.NDTM.coreSum` — full configurations
  are *not* injectively codable at fixed length, the output tape being
  unbounded (round-1 blocker, finding 1) — together with **three** CNFs over
  the code bits: a validity predicate characterizing exactly the codec image
  (unguarded midpoint quantification admits paths through junk codes —
  round-1 finding 3), the adjacency test (true on same-input windowed pairs
  iff the step descends to the vertex quotient; false across distinct
  inputs), and the acceptance test (halted state with `accept` summary).
  Declared deviations from the book's Claim 4.4(2), each argued harmless to
  Theorem 4.13: (i) the codec length is `O(s + n)` rather than `O(s)` — the
  code carries the **input content** and a one-hot input-position track, so
  every check is *local* and the formulas are input-independent (Cook-Levin's
  marker discipline; round-1 finding 7); (ii) the CNF sizes are bounded
  through their **serialized lengths** — polynomial, not linear; a
  literal-occurrence count alone misses empty clauses (round-1 finding 8) —
  at base `s + n + 2`, which gives the description room the code width does
  not (round-2 finding 1);
  (iii) adjacency compares `coreSum (step c)` with `coreSum d`, so halted
  vertices are self-adjacent while live ones **need not** be (a stationary
  silent live loop is — round-2 finding 3); the ψ-recursion's base case
  supplies `a = b` separately (round-1 finding 6). **The package is
  existence, not an algorithm** (round-1 major 2): the uniform
  polynomial-time emitter of the three formulas is a private, named fill
  obligation of `TQBF`'s hardness proof, never a claim of this statement.
  Sole consumer unchanged; D6-style promotion recorded for a second consumer
  (the phase-P4.4 `PATH` encoding remains the candidate).
* **The facade discipline**: `ClassPSPACE.lean` is this phase's own new
  facade; nothing frozen is touched.

## Main definitions

* `Complexity.PSPACEHard`, `Complexity.PSPACEComplete` — [AB09, Definition 4.9].
* `Complexity.TQBF` — the true quantified Boolean formulas, over
  `Complexity.QBF.decode`. [AB09, §4.2, before Theorem 4.13]

## Main results (three phase-P4.3 statements remain sorried)

* `Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P` — a `PSPACE`-complete
  language in `P` collapses `PSPACE` to `P`. [AB09, §4.2, after Definition 4.9]
* `Complexity.exists_adjacency_codec_cnf` — Claim 4.4(2), packaged quotient form.
* `Complexity.TQBF_mem_PSPACE` — [AB09, Theorem 4.13, membership half].
* `Complexity.TQBF_PSPACEHard` — [AB09, Theorem 4.13, hardness half]; a fill
  summit (the `ψᵢ` emitter).
* `Complexity.TQBF_PSPACEComplete` — [AB09, Theorem 4.13].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Definition 4.9, Claim 4.4,
  Theorem 4.13.)
* [SM73] L. Stockmeyer, A. Meyer, *Word problems requiring exponential time*,
  STOC 1973. (Cited through [AB09]; no external text required.)
-/

namespace Complexity

open Std.Sat (CNF)
open Turing

/-- **`PSPACE`-hardness** [AB09, Definition 4.9]: every `PSPACE` language
Karp-reduces to `L'` in polynomial time. (The logspace variant is phase
P4.4's.) -/
def PSPACEHard (L' : Language Bool) : Prop :=
  ∀ L ∈ PSPACE, L ≤ₚ L'

/-- **`PSPACE`-completeness** [AB09, Definition 4.9]: `PSPACE`-hard and in
`PSPACE`. -/
def PSPACEComplete (L' : Language Bool) : Prop :=
  L' ∈ PSPACE ∧ PSPACEHard L'

/-- **A `PSPACE`-complete language in `P` collapses the class**
([AB09, §4.2, the paragraph after Definition 4.9]; proved, citing `P_subset_PSPACE`):
if some `PSPACE`-complete `L'` lies in `P`, then `PSPACE = P`.

**Proof sketch.** `⊇` is `Complexity.P_subset_PSPACE` (phase P4.1). `⊆`: a
`PSPACE` member reduces to `L'` (hardness), and `P` is closed downward under
`≤ₚ` (`Complexity.mem_P_of_polyTimeReducible`, chapter 2). -/
theorem PSPACE_eq_P_of_pspaceComplete_mem_P {L' : Language Bool}
    (h : PSPACEComplete L') (hP : L' ∈ P) : PSPACE = P := by
  exact Set.Subset.antisymm
    (fun L hL => mem_P_of_polyTimeReducible (h.2 L hL) hP) P_subset_PSPACE

/-! ### Fill appendix: finite marker tracks for the quotient codec

The finite row below factors through `ConfigCount.coreCode`. Its Boolean coordinates
are the input contents, one-hot input head and state, three bits per work cell
(two mutually exclusive symbol bits and one head marker), and two summary bits.
Coordinates are numbered by a finite equivalence; the rest of the prescribed width
is zero padding. No output history other than `outSummary` is retained.

For adjacency, each joint head tuple and finite scanned-symbol/state case guards
one output-coordinate gate. Its `3k+7` ports include the guard markers, the scanned
input and work bits, the summary flags, and the old/new coordinate. Thus every use
of Boolean universality has machine-only arity. Exact integer successor markers
reject outward moves; the code itself is only compared on windowed configurations.
Normalizing the output history before a transition uses `NDTM.coreSum_stepWith`.
With `u=s+n+2`, the validity and acceptance ledgers have degree three, and adjacency
has degree `k+3`. A single constant absorbs all coefficients and the padded width.
-/

/-- The finite fields of a windowed configuration, together with its input. -/
private structure CodecRow (M : FinTM Bool) (n s : ℕ) where
  input : Fin n → Bool
  state : Option M.State
  inputHead : Fin (n + 2)
  symbols : Fin M.k → Fin (2 * s + 1) → Option Bool
  heads : Fin M.k → Fin (2 * s + 1)
  summary : OutSummary

/-- One coordinate for each bit in the marker discipline of Claim 4.4(2). -/
private inductive CodecBit (M : FinTM Bool) (n s : ℕ)
  | input : Fin n → CodecBit M n s
  | inputHead : Fin (n + 2) → CodecBit M n s
  | state : Option M.State → CodecBit M n s
  | work : Fin M.k → Fin (2 * s + 1) → Fin 3 → CodecBit M n s
  | summary : Bool → CodecBit M n s
  deriving Fintype, DecidableEq

/-- The unpadded track width, with three bits for every work cell. -/
private theorem codecBit_card (M : FinTM Bool) (n s : ℕ) :
    Fintype.card (CodecBit M n s) =
      n + (n + 2) + (Fintype.card M.State + 1) + M.k * (2 * s + 1) * 3 + 2 := by
  rw [← Fintype.card_congr (CodecBit.proxyTypeEquiv M n s)]
  simp
  ring

/-- A machine-dependent linear coefficient sufficient for all raw tracks. -/
private def codecCoefficient (M : FinTM Bool) : ℕ :=
  Fintype.card M.State + 6 * M.k + 5

/-- The raw tracks fit every requested width with coefficient at least this one. -/
private theorem codecBit_card_le (M : FinTM Bool) (n s C : ℕ)
    (hC : codecCoefficient M ≤ C) :
    Fintype.card (CodecBit M n s) ≤ C * (s + n + 1) := by
  rw [codecBit_card]
  unfold codecCoefficient at hC
  calc
    _ ≤ (Fintype.card M.State + 6 * M.k + 5) * (s + n + 1) := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ hC

/-- Marker encoding of a finite row. Blank symbols and the empty summary use `00`;
false/true symbols and accept/dead summaries use the two singleton patterns. -/
private def codecRowBits {M : FinTM Bool} {n s : ℕ} (r : CodecRow M n s) :
    CodecBit M n s → Bool
  | .input i => r.input i
  | .inputHead j => decide (r.inputHead = j)
  | .state q => decide (r.state = q)
  | .work i j b =>
      if b.val = 0 then decide (r.symbols i j = some false)
      else if b.val = 1 then decide (r.symbols i j = some true)
      else decide (r.heads i = j)
  | .summary b => decide (r.summary = if b then .dead else .accept)

/-- Two singleton flags distinguish all three values of an optional bit. -/
private theorem codec_symbol_ext (u v : Option Bool)
    (h0 : decide (u = some false) = decide (v = some false))
    (h1 : decide (u = some true) = decide (v = some true)) : u = v := by
  cases u with
  | none => cases v with
    | none => rfl
    | some b => cases b <;> simp_all
  | some a => cases v with
    | none => cases a <;> simp_all
    | some b => cases a <;> cases b <;> simp_all

/-- Marker equality recovers every field of a finite row.

**Proof sketch.** Read the true marker at the first row's state and head positions.
The two symbol flags distinguish blank, false and true; the two summary flags
similarly distinguish the three output summaries. Input bits are direct coordinates. -/
private theorem codecRowBits_injective {M : FinTM Bool} {n s : ℕ} :
    Function.Injective (@codecRowBits M n s) := by
  intro r t h
  have hi : r.input = t.input := funext fun j => congrFun h (.input j)
  have hs : r.state = t.state := by
    have := congrFun h (.state r.state)
    exact Eq.symm (of_decide_eq_true (show decide (t.state = r.state) = true from by
      simpa only [codecRowBits, decide_true] using this.symm))
  have hp : r.inputHead = t.inputHead := by
    have := congrFun h (.inputHead r.inputHead)
    exact Eq.symm (of_decide_eq_true (show decide (t.inputHead = r.inputHead) = true from by
      simpa only [codecRowBits, decide_true] using this.symm))
  have hw : r.symbols = t.symbols := by
    funext i j
    apply codec_symbol_ext
    · exact congrFun h (.work i j 0)
    · exact congrFun h (.work i j 1)
  have hh : r.heads = t.heads := by
    funext i
    have := congrFun h (.work i (r.heads i) 2)
    exact Eq.symm (of_decide_eq_true (show decide (t.heads i = r.heads i) = true from by
      simpa [codecRowBits] using this.symm))
  have ho : r.summary = t.summary := by
    have h0 := congrFun h (.summary false)
    have h1 := congrFun h (.summary true)
    cases hr : r.summary <;> cases ht : t.summary <;>
      simp_all [codecRowBits]
  cases r
  cases t
  cases hi
  cases hs
  cases hp
  cases hw
  cases hh
  cases ho
  rfl

/-- Restriction of a configuration to its finite core code, with input and summary. -/
private def codecRowOf (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) : CodecRow M n s :=
  let t := MultiTapeTM.ConfigCount.coreCode s c
  { input := fun i => x.getD i.val false
    state := t.1
    inputHead := ⟨t.2.1.val, by simpa [hx] using t.2.1.isLt⟩
    symbols := t.2.2.1
    heads := t.2.2.2
    summary := outSummary c.output }

/-- Translate the public window predicate into the hypotheses of `coreCode_inj`. -/
private theorem codec_core_window {k : ℕ} {S : Type} {x : List Bool} {s : ℕ}
    {c : Cfg k Bool S x} (hc : c.InWindow s) :
    ∀ i, |c.workTapePos i| ≤ s ∧ ∀ z, c.workTapes i z ≠ none → |z| ≤ s := by
  intro i
  refine ⟨hc.1 i, ?_⟩
  intro z hz
  by_contra hn
  exact hz (hc.2 i z (lt_of_not_ge hn))

/-- Equality of the finite rows recovers the input content. -/
private theorem codecRowOf_input_eq (M : FinTM Bool) (n s : ℕ)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y)
    (h : (codecRowOf M n s x hx c).input = (codecRowOf M n s y hy d).input) : x = y := by
  apply List.ext_getElem
  · omega
  · intro i hix hiy
    have he := congrFun h ⟨i, by omega⟩
    simpa [codecRowOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hix, hiy] using he

/-- The finite row identifies exactly the configuration-graph vertex at a fixed input.

**Proof sketch.** Forward, the four finite core fields agree, so `coreCode_inj`
recovers the core using the window bounds; the fifth field supplies the summary.
Backward, equality of cores and summaries directly makes all finite fields equal. -/
private theorem codecRowOf_eq_iff (M : FinTM Bool) (n s : ℕ)
    (x : List Bool) (hx : x.length = n) (c d : Cfg M.k Bool M.State x)
    (hc : c.InWindow s) (hd : d.InWindow s) :
    codecRowOf M n s x hx c = codecRowOf M n s x hx d ↔
      NDTM.coreSum c = NDTM.coreSum d := by
  constructor
  · intro h
    apply Prod.ext
    · apply MultiTapeTM.ConfigCount.coreCode_inj s (codec_core_window hc) (codec_core_window hd)
      apply Prod.ext (congrArg CodecRow.state h)
      apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun r => r.inputHead.val) h
      · exact Prod.ext (congrArg CodecRow.symbols h) (congrArg CodecRow.heads h)
    · exact congrArg CodecRow.summary h
  · intro h
    have hc := congrArg Prod.fst h
    have ho := congrArg Prod.snd h
    change MultiTapeTM.ConfigCount.core c = MultiTapeTM.ConfigCount.core d at hc
    change outSummary c.output = outSummary d.output at ho
    simp only [MultiTapeTM.ConfigCount.core, Prod.mk.injEq] at hc
    rcases hc with ⟨hs, hp, hw, hh⟩
    simp only [codecRowOf, MultiTapeTM.ConfigCount.coreCode, hs, hp, hw, hh, ho]

/-- Pad an arbitrary finite bit assignment to exactly `L` bits (truncate if necessary).
The application below always proves that truncation cannot occur. -/
private noncomputable def codecWord {α : Type} [Fintype α] (L : ℕ) (a : α → Bool) :
    List Bool :=
  List.ofFn fun i : Fin L =>
    if h : i.val < Fintype.card α then
      a ((Fintype.equivFin α).symm ⟨i.val, h⟩)
    else false

/-- The padded word has its prescribed length on all arguments. -/
private theorem codecWord_length {α : Type} [Fintype α] (L : ℕ) (a : α → Bool) :
    (codecWord L a).length = L := by simp [codecWord]

/-- Reading the coordinate of a finite bit assignment after sufficient padding. -/
private theorem codecWord_get {α : Type} [Fintype α] (L : ℕ) (a : α → Bool)
    (hL : Fintype.card α ≤ L) (i : α) :
    (codecWord L a).getD (Fintype.equivFin α i).val false = a i := by
  have hi := (Fintype.equivFin α i).isLt
  simp [codecWord, List.getD_eq_getElem?_getD, hi, lt_of_lt_of_le hi hL]

/-- Sufficiently padded words agree exactly when their underlying bits agree. -/
private theorem codecWord_eq_iff {α : Type} [Fintype α] (L : ℕ)
    (hL : Fintype.card α ≤ L) (a b : α → Bool) :
    codecWord L a = codecWord L b ↔ a = b := by
  constructor
  · intro h
    funext i
    have he := congrArg (fun w : List Bool => w.getD (Fintype.equivFin α i).val false) h
    simpa only [codecWord_get L a hL i, codecWord_get L b hL i] using he
  · rintro rfl
    rfl

/-- The total configuration codec. Wrong-length inputs receive the all-zero word. -/
private noncomputable def configurationCodec (M : FinTM Bool) (C n s : ℕ)
    (x : List Bool) (c : Cfg M.k Bool M.State x) : List Bool :=
  if hx : x.length = n then
    codecWord (C * (s + n + 1)) (codecRowBits (codecRowOf M n s x hx c))
  else List.replicate (C * (s + n + 1)) false

/-- Exact length holds even for wrong-length inputs and nonwindowed configurations. -/
private theorem configurationCodec_length (M : FinTM Bool) (C n s : ℕ)
    (x : List Bool) (c : Cfg M.k Bool M.State x) :
    (configurationCodec M C n s x c).length = C * (s + n + 1) := by
  unfold configurationCodec
  split <;> simp [codecWord_length]

/-- The codec separates inputs of the prescribed length. -/
private theorem configurationCodec_input_eq (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y)
    (h : configurationCodec M C n s x c = configurationCodec M C n s y d) : x = y := by
  simp only [configurationCodec, dif_pos hx, dif_pos hy] at h
  have hbits := (codecWord_eq_iff _ (codecBit_card_le M n s C hC) _ _).mp h
  exact codecRowOf_input_eq M n s x y hx hy c d (congrArg CodecRow.input (codecRowBits_injective hbits))

/-- The padded codec factors through, and separates, the windowed vertex quotient. -/
private theorem configurationCodec_eq_iff (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x : List Bool) (hx : x.length = n)
    (c d : Cfg M.k Bool M.State x) (hc : c.InWindow s) (hd : d.InWindow s) :
    configurationCodec M C n s x c = configurationCodec M C n s x d ↔
      NDTM.coreSum c = NDTM.coreSum d := by
  simp only [configurationCodec, dif_pos hx,
    codecWord_eq_iff _ (codecBit_card_le M n s C hC), codecRowBits_injective.eq_iff]
  exact codecRowOf_eq_iff M n s x hx c d hc hd

/-- A flattened family conjoins exactly its member formulas. -/
private theorem codecCnf_eval_flatMap {α β : Type} (xs : List β) (f : β → CNF α)
    (a : α → Bool) : CNF.eval a (xs.flatMap f) = true ↔ ∀ i ∈ xs, (f i).eval a = true := by
  simp [CNF.eval, List.all_flatMap, List.all_eq_true]

/-- A list of clauses conjoins their individual evaluations. -/
private theorem codecCnf_eval_map {α β : Type} (xs : List β) (f : β → CNF.Clause α)
    (a : α → Bool) : CNF.eval a (xs.map f) = true ↔ ∀ i ∈ xs, (f i).eval a = true := by
  simp [CNF.eval, List.all_eq_true]

/-- Exactly one positive marker, expressed by one positive clause and pairwise exclusions. -/
private noncomputable def codecOneHot (α : Type) [Fintype α] [DecidableEq α] : CNF α :=
  [(Finset.univ.toList.map fun i : α => (i, true))] ++
    Finset.univ.toList.flatMap fun i : α =>
      (Finset.univ.toList.filter fun j : α => decide (i ≠ j)).map fun j =>
        [(i, false), (j, false)]

/-- Pairwise exclusions give precisely a one-hot assignment.

**Proof sketch.** The positive clause selects a true coordinate. Its exclusion clause
with any other coordinate forces that other coordinate false. Conversely, an assignment
with a single true coordinate satisfies the positive clause and every exclusion. -/
private theorem codecOneHot_eval (α : Type) [Fintype α] [DecidableEq α] (a : α → Bool) :
    (codecOneHot α).eval a = true ↔ ∃ j : α, ∀ i : α, a i = decide (j = i) := by
  classical
  have he : (codecOneHot α).eval a = true ↔
      (∃ j : α, a j = true) ∧ ∀ i j : α, i ≠ j → (a i = false ∨ a j = false) := by
    simp [codecOneHot, CNF.eval, CNF.Clause.eval, List.all_flatMap,
      List.all_filter, Bool.or_eq_true]
    intro _ _
    constructor
    · intro h i j hij
      exact (h i j).resolve_left hij
    · intro h i j
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr (h i j hij)
  rw [he]
  constructor
  · rintro ⟨⟨j, hj⟩, hpair⟩
    refine ⟨j, fun i => ?_⟩
    by_cases hji : j = i
    · subst i
      simpa using hj
    · have hi := hpair j i hji
      simpa [hji, hj] using hi
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, by simpa using hj j⟩, ?_⟩
    intro u v huv
    by_cases hju : j = u
    · right
      have hjv : j ≠ v := by simpa [hju] using huv
      simpa [hjv] using hj v
    · left
      simpa [hju] using hj u

/-- Valid marker assignments consist of one-hot heads and state, with the forbidden
`11` pattern excluded from each symbol and summary pair. -/
private def codecBitsValid (M : FinTM Bool) (n s : ℕ) (a : CodecBit M n s → Bool) : Prop :=
  (∃ j : Fin (n + 2), ∀ i, a (.inputHead i) = decide (j = i)) ∧
  (∃ q : Option M.State, ∀ p, a (.state p) = decide (q = p)) ∧
  (∀ i : Fin M.k, ∃ h : Fin (2 * s + 1),
    ∀ j, a (.work i j 2) = decide (h = j)) ∧
  (∀ i j, a (.work i j 0) = false ∨ a (.work i j 1) = false) ∧
  (a (.summary false) = false ∨ a (.summary true) = false)

/-- Every finite row produces a valid marker assignment. -/
private theorem codecRowBits_valid {M : FinTM Bool} {n s : ℕ} (r : CodecRow M n s) :
    codecBitsValid M n s (codecRowBits r) := by
  refine ⟨⟨r.inputHead, fun _ => rfl⟩, ⟨r.state, fun _ => rfl⟩,
    (fun i => ⟨r.heads i, fun _ => rfl⟩), ?_, ?_⟩
  · intro i j
    cases h : r.symbols i j with
    | none => simp [codecRowBits, h]
    | some b => cases b <;> simp [codecRowBits, h]
  · cases h : r.summary <;> simp [codecRowBits, h]

/-- Every valid marker assignment is the encoding of a finite row.

**Proof sketch.** Choose the unique head and state markers. Decode each two-bit symbol
pair as false, true or blank; its exclusion rules out `11`. Decode the summary in the
same way. Each coordinate of the constructed row then has the prescribed bit. -/
private theorem codecBitsValid_iff (M : FinTM Bool) (n s : ℕ)
    (a : CodecBit M n s → Bool) :
    codecBitsValid M n s a ↔ ∃ r : CodecRow M n s, codecRowBits r = a := by
  classical
  constructor
  · rintro ⟨⟨ip, hip⟩, ⟨q, hq⟩, hh, hw, ho⟩
    choose hp hhp using hh
    let r : CodecRow M n s :=
      { input := fun i => a (.input i)
        state := q
        inputHead := ip
        symbols := fun i j => if a (.work i j 0) then some false
          else if a (.work i j 1) then some true else none
        heads := hp
        summary := if a (.summary false) then .accept
          else if a (.summary true) then .dead else .empty }
    refine ⟨r, funext fun z => ?_⟩
    cases z with
    | input i => rfl
    | inputHead i => exact (hip i).symm
    | state p => exact (hq p).symm
    | work i j b =>
      have hij := hw i j
      fin_cases b <;>
        cases h0 : a (.work i j 0) <;> cases h1 : a (.work i j 1) <;>
        simp_all [codecRowBits, r]
    | summary b =>
      cases b <;> cases h0 : a (.summary false) <;>
        cases h1 : a (.summary true) <;> simp_all [codecRowBits, r]
  · rintro ⟨r, rfl⟩
    exact codecRowBits_valid r

/-- The validity CNF on unpadded tracks. Input contents are unrestricted. -/
private noncomputable def codecValidity (M : FinTM Bool) (n s : ℕ) : CNF (CodecBit M n s) :=
  (codecOneHot (Fin (n + 2))).relabel CodecBit.inputHead ++
  (codecOneHot (Option M.State)).relabel CodecBit.state ++
  (List.finRange M.k).flatMap (fun i =>
    (codecOneHot (Fin (2 * s + 1))).relabel (fun j => CodecBit.work i j 2)) ++
  (List.finRange M.k).flatMap (fun i => (List.finRange (2 * s + 1)).map fun j =>
    [(CodecBit.work i j 0, false), (CodecBit.work i j 1, false)]) ++
  [[(CodecBit.summary false, false), (CodecBit.summary true, false)]]

/-- The unpadded validity formula recognizes exactly the finite-row encodings. -/
private theorem codecValidity_eval (M : FinTM Bool) (n s : ℕ)
    (a : CodecBit M n s → Bool) :
    (codecValidity M n s).eval a = true ↔ ∃ r : CodecRow M n s, codecRowBits r = a := by
  rw [← codecBitsValid_iff]
  simp [codecValidity, codecBitsValid, CNF.eval_append, CNF.eval_relabel,
    codecOneHot_eval, codecCnf_eval_flatMap, codecCnf_eval_map, CNF.Clause.eval,
    Bool.or_eq_true]

/-- The finite position code decodes the designated cell of the window. -/
private theorem codec_posCode (s : ℕ) (j : Fin (2 * s + 1)) :
    MultiTapeTM.ConfigCount.posCode s ((j.val : ℤ) - s) = j := by
  apply Fin.ext
  dsimp [MultiTapeTM.ConfigCount.posCode]
  have hj := j.isLt
  omega

/-- Every finite row is realized by a genuine windowed configuration.

**Proof sketch.** Turn the input vector into a list and extend the finite work tracks
by blanks outside the window. Subtract the radius to recover work-head positions.
Use respectively `[]`, `[true]` and `[false]` for the three summaries. Reading the
finite core code of this configuration returns exactly the original row. -/
private theorem codecRow_realize (M : FinTM Bool) (n s : ℕ) (r : CodecRow M n s) :
    ∃ (x : List Bool) (hx : x.length = n) (c : Cfg M.k Bool M.State x),
      c.InWindow s ∧ codecRowOf M n s x hx c = r := by
  let x := List.ofFn r.input
  have hx : x.length = n := by simp [x]
  let c : Cfg M.k Bool M.State x :=
    { state := r.state
      inputPos := ⟨r.inputHead.val, by rw [hx]; exact r.inputHead.isLt⟩
      workTapes := fun i z => if |z| ≤ (s : ℤ) then
        r.symbols i (MultiTapeTM.ConfigCount.posCode s z) else none
      workTapePos := fun i => (r.heads i).val - (s : ℤ)
      output := match r.summary with
        | .empty => []
        | .accept => [true]
        | .dead => [false] }
  have hz (j : Fin (2 * s + 1)) : |(j.val : ℤ) - s| ≤ (s : ℤ) := by
    have hj := j.isLt
    rw [abs_le]
    omega
  refine ⟨x, hx, c, ⟨fun i => hz (r.heads i), ?_⟩, ?_⟩
  · intro i z h
    simp [c, not_le_of_gt h]
  · have hi : (fun i : Fin n => x.getD i.val false) = r.input := by
      funext i
      simp [x, List.getD_eq_getElem?_getD]
    have hw : (fun (i : Fin M.k) (j : Fin (2 * s + 1)) => c.workTapes i ((j.val : ℤ) - s)) = r.symbols := by
      funext i j
      simp [c, hz j, codec_posCode]
    have hh : (fun i => MultiTapeTM.ConfigCount.posCode s (c.workTapePos i)) = r.heads := by
      funext i
      exact codec_posCode s (r.heads i)
    have ho : outSummary c.output = r.summary := by
      cases h : r.summary <;> simp [c, h, outSummary]
    dsimp [codecRowOf, MultiTapeTM.ConfigCount.coreCode]
    rw [hi, hw, hh, ho]

/-- A padded word's unused suffix is zero. -/
private theorem codecWord_padding {α : Type} [Fintype α] (L : ℕ) (a : α → Bool)
    (j : ℕ) (hj : Fintype.card α ≤ j) : (codecWord L a).getD j false = false := by
  by_cases hL : j < L
  · simp [codecWord, List.getD_eq_getElem?_getD, hL, not_lt_of_ge hj]
  · simp [codecWord, List.getD_eq_getElem?_getD, hL]

/-- A word of length `L` with zero padding is recovered from its finite coordinates. -/
private theorem codecWord_reconstruct {α : Type} [Fintype α] (L : ℕ)
    (w : List Bool) (hw : w.length = L)
    (hpad : ∀ j, Fintype.card α ≤ j → j < L → w.getD j false = false) :
    codecWord L (fun i : α => w.getD (Fintype.equivFin α i).val false) = w := by
  apply List.ext_getElem
  · simpa [codecWord_length] using hw.symm
  · intro i hi hiw
    have hiL : i < L := by simpa only [codecWord_length] using hi
    by_cases hiα : i < Fintype.card α
    · simp [codecWord, hiα, List.getD_eq_getElem?_getD, hiw]
    · have he := hpad i (by omega) hiL
      simpa [codecWord, hiα, List.getD_eq_getElem?_getD, hiw] using he.symm

/-- The padding clauses fix every unused coordinate to false. -/
private def codecPadding (first L : ℕ) : CNF ℕ :=
  (List.range (L - first)).map fun i => [(first + i, false)]

/-- Evaluation of the padding clauses states exactly that the unused suffix is zero. -/
private theorem codecPadding_eval (first L : ℕ) (a : ℕ → Bool) :
    (codecPadding first L).eval a = true ↔ ∀ j, first ≤ j → j < L → a j = false := by
  simp only [codecPadding, CNF.eval, List.all_map, List.all_eq_true, List.mem_range,
    Function.comp_apply, CNF.Clause.eval_cons, CNF.Clause.eval_nil, Bool.or_false,
    beq_iff_eq]
  constructor
  · intro h j hj hjL
    simpa [Nat.add_sub_of_le hj] using h (j - first) (by omega)
  · intro h i hi
    exact h (first + i) (by omega) (by omega)

/-- Number the finite validity formula inside the prescribed width and add zero padding. -/
private noncomputable def configurationValidity (M : FinTM Bool) (C n s : ℕ) : CNF ℕ :=
  (codecValidity M n s).relabel (fun b => (Fintype.equivFin (CodecBit M n s) b).val) ++
    codecPadding (Fintype.card (CodecBit M n s)) (C * (s + n + 1))

/-- Validity recognizes exactly the padded codes of windowed configurations.

**Proof sketch.** The unpadded formula recovers a finite row and the padding clauses
recover the remaining zeros. Realize that row by the window extension lemma.
Conversely every configuration supplies a valid row and zero padding. -/
private theorem configurationValidity_eval (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (w : List Bool) (hw : w.length = C * (s + n + 1)) :
    (configurationValidity M C n s).eval (fun j => w.getD j false) = true ↔
      ∃ x : List Bool, x.length = n ∧ ∃ c : Cfg M.k Bool M.State x,
        c.InWindow s ∧ w = configurationCodec M C n s x c := by
  have hfit := codecBit_card_le M n s C hC
  simp only [configurationValidity, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel,
    codecValidity_eval, codecPadding_eval, Function.comp_def]
  constructor
  · rintro ⟨⟨r, hr⟩, hp⟩
    obtain ⟨x, hx, c, hc, he⟩ := codecRow_realize M n s r
    refine ⟨x, hx, c, hc, ?_⟩
    simp only [configurationCodec, dif_pos hx, he, hr]
    exact (codecWord_reconstruct _ w hw hp).symm
  · rintro ⟨x, hx, c, hc, rfl⟩
    simp only [configurationCodec, dif_pos hx]
    refine ⟨⟨codecRowOf M n s x hx c, ?_⟩, ?_⟩
    · funext b
      exact (codecWord_get _ _ hfit b).symm
    · intro j hj _
      exact codecWord_padding _ _ j hj

/-- Acceptance reads the halt marker and the accepting summary marker. -/
private def codecAcceptance (M : FinTM Bool) (n s : ℕ) : CNF (CodecBit M n s) :=
  [[(.state none, true)], [(.summary false, true)]]

/-- The acceptance formula has the required meaning on every finite row. -/
private theorem codecAcceptance_eval (M : FinTM Bool) (n s : ℕ) (r : CodecRow M n s) :
    (codecAcceptance M n s).eval (codecRowBits r) = true ↔
      r.state = none ∧ r.summary = .accept := by
  simp [codecAcceptance, CNF.eval, CNF.Clause.eval, codecRowBits]

/-- Number the two acceptance tests at their actual code positions. -/
private noncomputable def configurationAcceptance (M : FinTM Bool) (n s : ℕ) : CNF ℕ :=
  (codecAcceptance M n s).relabel (fun b => (Fintype.equivFin (CodecBit M n s) b).val)

/-- The numbered acceptance CNF recognizes halted configurations with accepting summary. -/
private theorem configurationAcceptance_eval (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x : List Bool) (hx : x.length = n)
    (c : Cfg M.k Bool M.State x) :
    (configurationAcceptance M n s).eval (fun j => (configurationCodec M C n s x c).getD j false)
      = true ↔ c.state = none ∧ outSummary c.output = .accept := by
  simp only [configurationAcceptance, CNF.eval_relabel, Function.comp_def,
    configurationCodec, dif_pos hx, codecWord_get _ _ (codecBit_card_le M n s C hC)]
  exact codecAcceptance_eval M n s (codecRowOf M n s x hx c)

/-- Clause count plus literal occurrences; empty clauses still cost one unit. -/
private def codecCnfCost {α : Type} (φ : CNF α) : ℕ :=
  (φ.map fun clause => clause.length + 1).sum

/-- Renumbering variables preserves the clause-and-literal cost. -/
private theorem codecCnfCost_relabel {α β : Type} (φ : CNF α) (f : α → β) :
    codecCnfCost (φ.relabel f) = codecCnfCost φ := by
  simp [codecCnfCost, CNF.relabel, CNF.Clause.relabel, List.map_map, Function.comp_def]

/-- Conjoining CNFs adds their clause-and-literal costs. -/
private theorem codecCnfCost_append {α : Type} (φ ψ : CNF α) :
    codecCnfCost (φ ++ ψ) = codecCnfCost φ + codecCnfCost ψ := by
  simp [codecCnfCost]

/-- A family of bounded-cost checks has at most its length times the common cost. -/
private theorem codecCnfCost_flatMap_le {α β : Type} (xs : List β) (f : β → CNF α)
    (B : ℕ) (h : ∀ x ∈ xs, codecCnfCost (f x) ≤ B) :
    codecCnfCost (xs.flatMap f) ≤ xs.length * B := by
  induction xs with
  | nil => simp [codecCnfCost]
  | cons x xs ih =>
    rw [List.flatMap_cons, codecCnfCost_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add (h x List.mem_cons_self)
      (ih fun y hy => h y (List.mem_cons_of_mem x hy))).trans_eq (Nat.add_comm _ _)

/-- The exactly-one constraint has a quadratic cost, including its positive clause.

**Proof sketch.** The positive clause costs the number of markers plus one.
There are at most the square of that many ordered exclusions, each costing three. -/
private theorem codecOneHot_cost (α : Type) [Fintype α] [DecidableEq α] :
    codecCnfCost (codecOneHot α) ≤
      Fintype.card α + 1 + 3 * (Fintype.card α) ^ 2 := by
  classical
  let xs := (Finset.univ : Finset α).toList
  have hx : xs.length = Fintype.card α := by simp [xs]
  have hpair (i : α) : codecCnfCost
      ((xs.filter fun j => decide (i ≠ j)).map fun j => [(i, false), (j, false)]) ≤
        Fintype.card α * 3 := by
    simp only [codecCnfCost, List.map_map, Function.comp_def, List.length_cons,
      List.length_nil, Nat.reduceAdd, List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
    exact Nat.mul_le_mul_right 3 ((List.length_filter_le _ _).trans_eq hx)
  have h := codecCnfCost_flatMap_le xs
    (fun i => (xs.filter fun j => decide (i ≠ j)).map fun j => [(i, false), (j, false)])
    (Fintype.card α * 3) (fun i _ => hpair i)
  unfold codecOneHot
  rw [codecCnfCost_append]
  have hsingle : codecCnfCost [xs.map fun i => (i, true)] = Fintype.card α + 1 := by
    simp [codecCnfCost, hx]
  change codecCnfCost [xs.map fun i => (i, true)] + _ ≤ _
  rw [hsingle]
  rw [hx] at h
  nlinarith

/-- A variable bound for an explicitly bounded relabeling of a finite formula. -/
private theorem codecCnf_numVars {α : Type} (φ : CNF α) (wire : α → ℕ) (N : ℕ)
    (hw : ∀ c ∈ φ, ∀ l ∈ c, wire l.1 < N) : (CNF.relabel wire φ).numVars ≤ N := by
  apply List.max_le_of_forall_le
  intro j hj
  simp only [CNF.relabel, CNF.Clause.relabel, List.flatMap_map, List.map_map,
    Function.comp_def, List.mem_flatMap, List.mem_map] at hj
  obtain ⟨clause, hc, lit, hl, rfl⟩ := hj
  exact Nat.succ_le_of_lt (hw clause hc lit hl)

/-- The chapter-2 grammar bounds serialization by the cost times the index bound.

**Proof sketch.** A literal at index below `N` serializes to at most `N+2` bits.
Each clause contributes its prefix and terminator, and the formula has one final
terminator. Counting one extra unit per clause covers both separators, including
empty clauses. The bound deliberately allows `N+3` bits per cost unit. -/
private theorem codecCnf_serialize {α : Type} (φ : CNF α) (wire : α → ℕ) (N : ℕ)
    (hw : ∀ c ∈ φ, ∀ l ∈ c, wire l.1 < N) :
    (CNF.serialize (CNF.relabel wire φ)).length ≤ codecCnfCost φ * (N + 3) + 1 := by
  have hlit (l : Std.Sat.Literal α) (hl : wire l.1 < N) :
      (CNF.serializeLit (wire l.1, l.2)).length ≤ N + 2 := by
    simp only [CNF.serializeLit, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hclause (c : CNF.Clause α) (hc : ∀ l ∈ c, wire l.1 < N) :
      (CNF.serializeClause (c.relabel wire)).length + 1 ≤ (c.length + 1) * (N + 3) := by
    have ht : ((c.relabel wire).flatMap CNF.serializeLit).length ≤ c.length * (N + 2) := by
      induction c with
      | nil => simp [CNF.Clause.relabel]
      | cons l c ih =>
        simp only [CNF.Clause.relabel, List.map_cons, List.flatMap_cons,
          List.length_append, List.length_cons] at *
        calc
          _ ≤ (N + 2) + c.length * (N + 2) := Nat.add_le_add (hlit l (hc l List.mem_cons_self))
            (ih fun t ht => hc t (List.mem_cons_of_mem l ht))
          _ = _ := by ring
    simp only [CNF.serializeClause, List.length_append, List.length_cons, List.length_nil]
    nlinarith
  induction φ with
  | nil => simp [CNF.serialize, CNF.relabel, codecCnfCost]
  | cons c φ ih =>
    have hc := hclause c (hw c List.mem_cons_self)
    have ih := ih (fun d hd => hw d (List.mem_cons_of_mem c hd))
    have he : (CNF.serialize (CNF.relabel wire (c :: φ))).length =
        (CNF.serializeClause (c.relabel wire)).length + 1 +
          (CNF.serialize (CNF.relabel wire φ)).length := by
      simp [CNF.serialize, CNF.relabel]
      omega
    rw [he]
    simp only [codecCnfCost, List.map_cons, List.sum_cons] at *
    nlinarith

/-- Explicit polynomial coefficient for the unpadded validity clauses. -/
private def codecValidityCoefficient (M : FinTM Bool) : ℕ :=
  let q := Fintype.card M.State + 1
  3 * q ^ 2 + q + 9 + 21 * M.k

/-- Counting one-hot exclusions and trit ranges gives the raw validity cost.

**Proof sketch.** Apply the exactly-one ledger to the input head, state and each
work head. Each work cell adds one two-literal exclusion, as does the summary.
There are `k(2s+1)` work cells, and no constraint on the input-content bits. -/
private theorem codecValidity_cost_raw (M : FinTM Bool) (n s : ℕ) :
    codecCnfCost (codecValidity M n s) ≤
      ((n + 2) + 1 + 3 * (n + 2) ^ 2) +
      ((Fintype.card M.State + 1) + 1 + 3 * (Fintype.card M.State + 1) ^ 2) +
      M.k * ((2 * s + 1) + 1 + 3 * (2 * s + 1) ^ 2) +
      M.k * (3 * (2 * s + 1)) + 3 := by
  classical
  have hinput := codecOneHot_cost (Fin (n + 2))
  have hstate := codecOneHot_cost (Option M.State)
  have hhead := codecCnfCost_flatMap_le (List.finRange M.k)
    (fun i => (codecOneHot (Fin (2 * s + 1))).relabel
      (fun j => CodecBit.work (M := M) (n := n) i j 2))
    ((2 * s + 1) + 1 + 3 * (2 * s + 1) ^ 2) (by
      intro i _
      simpa [codecCnfCost_relabel] using codecOneHot_cost (Fin (2 * s + 1)))
  have hcell := codecCnfCost_flatMap_le (List.finRange M.k)
    (fun i => (List.finRange (2 * s + 1)).map fun j =>
      [(CodecBit.work (M := M) (n := n) i j 0, false), (CodecBit.work i j 1, false)])
    (3 * (2 * s + 1)) (by
      intro i _
      simp [codecCnfCost, List.map_map, Function.comp_def]
      omega)
  simp only [Fintype.card_option, Fintype.card_fin, List.length_finRange] at hinput hstate hhead hcell
  simp only [codecValidity, codecCnfCost_append, codecCnfCost_relabel]
  have hsummary : codecCnfCost
      [[(CodecBit.summary (M := M) (n := n) (s := s) false, false),
        (CodecBit.summary true, false)]] = 3 := rfl
  rw [hsummary]
  omega

/-- The raw validity cost is bounded quadratically in `s+n+2`.

**Proof sketch.** Bound the input track by the common base and each work track by
twice that base. The state count is a machine constant; collect the quadratic terms. -/
private theorem codecValidity_cost (M : FinTM Bool) (n s : ℕ) :
    codecCnfCost (codecValidity M n s) ≤ codecValidityCoefficient M * (s + n + 2) ^ 2 := by
  let u := s + n + 2
  let q := Fintype.card M.State + 1
  have hu : 2 ≤ u := by omega
  have hu1 : 1 ≤ u ^ 2 := by nlinarith
  have hin : n + 2 ≤ u := by omega
  have hwork : 2 * s + 1 ≤ 2 * u := by omega
  have hi : (n + 2) + 1 + 3 * (n + 2) ^ 2 ≤ 5 * u ^ 2 := by
    have := Nat.pow_le_pow_left hin 2
    nlinarith
  have hw : (2 * s + 1) + 1 + 3 * (2 * s + 1) ^ 2 ≤ 15 * u ^ 2 := by
    have := Nat.pow_le_pow_left hwork 2
    nlinarith
  have hq : q + 1 + 3 * q ^ 2 ≤ (q + 1 + 3 * q ^ 2) * u ^ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (q + 1 + 3 * q ^ 2) hu1
  have hc : 3 * (2 * s + 1) ≤ 6 * u ^ 2 := by nlinarith
  have ht := codecValidity_cost_raw M n s
  have hh := Nat.mul_le_mul_left M.k hw
  have hs := Nat.mul_le_mul_left M.k hc
  change codecCnfCost (codecValidity M n s) ≤ (3 * q ^ 2 + q + 9 + 21 * M.k) * u ^ 2
  change codecCnfCost (codecValidity M n s) ≤
    _ + (q + 1 + 3 * q ^ 2) + _ + _ + 3 at ht
  nlinarith

/-- The padding contributes at most two cost units per code position. -/
private theorem codecPadding_cost (first L : ℕ) : codecCnfCost (codecPadding first L) ≤ 2 * L := by
  simp [codecPadding, codecCnfCost, List.map_map, Function.comp_def]
  omega

/-- All validity literals lie strictly inside the prescribed code width. -/
private theorem configurationValidity_literals (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    ∀ cl ∈ configurationValidity M C n s, ∀ l ∈ cl, l.1 < C * (s + n + 1) := by
  have hfit := codecBit_card_le M n s C hC
  intro cl hcl l hl
  simp only [configurationValidity, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · simp only [CNF.relabel, List.mem_map] at hcl
    obtain ⟨c, _, rfl⟩ := hcl
    simp only [CNF.Clause.relabel, List.mem_map] at hl
    obtain ⟨b, _, rfl⟩ := hl
    exact (Fintype.equivFin (CodecBit M n s) b.1).isLt.trans_le hfit
  · simp only [codecPadding, List.mem_map, List.mem_range] at hcl
    obtain ⟨j, hj, rfl⟩ := hcl
    simp only [List.mem_singleton] at hl
    subst l
    dsimp
    omega

/-- The validity CNF's variable count is inside the code width. -/
private theorem configurationValidity_numVars (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (configurationValidity M C n s).numVars ≤ C * (s + n + 1) := by
  simpa using codecCnf_numVars (configurationValidity M C n s) id _
    (configurationValidity_literals M C n s hC)

/-- A preliminary serialized-size ledger, before choosing the common theorem constant. -/
private theorem configurationValidity_size_raw (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (CNF.serialize (configurationValidity M C n s)).length ≤
      (codecValidityCoefficient M * (s + n + 2) ^ 2 + 2 * (C * (s + n + 1))) *
        (C * (s + n + 1) + 3) + 1 := by
  have h := codecCnf_serialize (configurationValidity M C n s) id _
    (configurationValidity_literals M C n s hC)
  simp only [CNF.relabel_id] at h
  have hw : codecCnfCost (configurationValidity M C n s) ≤
      codecValidityCoefficient M * (s + n + 2) ^ 2 + 2 * (C * (s + n + 1)) := by
    simpa only [configurationValidity, codecCnfCost_append, codecCnfCost_relabel] using
      Nat.add_le_add (codecValidity_cost M n s)
        (codecPadding_cost (Fintype.card (CodecBit M n s)) (C * (s + n + 1)))
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hw) 1)

/-- The acceptance CNF has two unit clauses and all its indices are inside the code. -/
private theorem configurationAcceptance_bounds (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (configurationAcceptance M n s).numVars ≤ C * (s + n + 1) ∧
    (CNF.serialize (configurationAcceptance M n s)).length ≤ 4 * (C * (s + n + 1) + 3) + 1 := by
  have hfit := codecBit_card_le M n s C hC
  have hb : ∀ cl ∈ codecAcceptance M n s, ∀ l ∈ cl,
      (Fintype.equivFin (CodecBit M n s) l.1).val < C * (s + n + 1) :=
    fun _ _ l _ => (Fintype.equivFin (CodecBit M n s) l.1).isLt.trans_le hfit
  refine ⟨codecCnf_numVars (codecAcceptance M n s) _ _ hb, ?_⟩
  have h := codecCnf_serialize (codecAcceptance M n s)
    (fun b => (Fintype.equivFin (CodecBit M n s) b).val) (C * (s + n + 1)) hb
  simpa only [codecAcceptance, codecCnfCost, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd] using h

/-- Normalize the validity serialization ledger to one cubic polynomial.

**Proof sketch.** Write `u=t+1≥2`. The cost is at most `(A+2)Cu²`, and every
serialized index costs at most `3Cu`. The extra final bit is covered by one
more copy of `C²u³`. -/
private theorem codec_size_normalize (A C t : ℕ) (hC : 1 ≤ C) (ht : 1 ≤ t) :
    (A * (t + 1) ^ 2 + 2 * (C * t)) * (C * t + 3) + 1 ≤
      (3 * A + 7) * C ^ 2 * (t + 1) ^ 3 := by
  have hu : t ≤ (t + 1) ^ 2 := by nlinarith
  have hA : A ≤ A * C := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left A hC
  have hcost : A * (t + 1) ^ 2 + 2 * (C * t) ≤ (A + 2) * C * (t + 1) ^ 2 := by
    have h1 := Nat.mul_le_mul_right ((t + 1) ^ 2) hA
    have h2 := Nat.mul_le_mul_left (2 * C) hu
    nlinarith
  have hindex : C * t + 3 ≤ 3 * C * (t + 1) := by nlinarith
  have hfinal : 1 ≤ C ^ 2 * (t + 1) ^ 3 := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))
  calc
    _ ≤ ((A + 2) * C * (t + 1) ^ 2) * (3 * C * (t + 1)) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul hcost hindex) 1
    _ ≤ ((A + 2) * C * (t + 1) ^ 2) * (3 * C * (t + 1)) + C ^ 2 * (t + 1) ^ 3 :=
      Nat.add_le_add_left hfinal _
    _ = _ := by ring

/-- Validity has a polynomial serialized-size bound uniform in the width coefficient. -/
private theorem configurationValidity_size (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (CNF.serialize (configurationValidity M C n s)).length ≤
      (3 * codecValidityCoefficient M + 7) * C ^ 2 * (s + n + 2) ^ 3 := by
  have hpos : 1 ≤ C := by unfold codecCoefficient at hC; omega
  have h := codec_size_normalize (codecValidityCoefficient M) C (s + n + 1) hpos (by omega)
  simpa only [show s + n + 1 + 1 = s + n + 2 by omega] using
    (configurationValidity_size_raw M C n s hC).trans h

/-- Acceptance also fits a cubic ledger, uniformly over all sufficient code widths. -/
private theorem configurationAcceptance_size (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (CNF.serialize (configurationAcceptance M n s)).length ≤
      13 * C ^ 2 * (s + n + 2) ^ 3 := by
  have hpos : 1 ≤ C := by unfold codecCoefficient at hC; omega
  have hi : C * (s + n + 1) + 3 ≤ 3 * C * (s + n + 2) := by nlinarith
  have hm : C * (s + n + 2) ≤ C ^ 2 * (s + n + 2) ^ 3 :=
    Nat.mul_le_mul (Nat.le_pow (by decide)) (Nat.le_pow (by decide))
  have hp : 1 ≤ C ^ 2 * (s + n + 2) ^ 3 := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))
  calc
    _ ≤ 4 * (C * (s + n + 1) + 3) + 1 := (configurationAcceptance_bounds M C n s hC).2
    _ ≤ 4 * (3 * C * (s + n + 2)) + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 4 hi) 1
    _ = 12 * (C * (s + n + 2)) + 1 := by ring
    _ ≤ 12 * (C ^ 2 * (s + n + 2) ^ 3) + C ^ 2 * (s + n + 2) ^ 3 :=
      Nat.add_le_add (Nat.mul_le_mul_left 12 hm) hp
    _ = _ := by ring

/-- A fixed-arity Boolean check becomes a CNF of bounded cost after arbitrary wiring.
This applies the chapter-2 universality theorem to a single gate, never to a row. -/
private theorem codecLocalCheck {α : Type} [Inhabited α] (arity : ℕ)
    (wire : Fin arity → α) (f : (Fin arity → Bool) → Bool) :
    ∃ φ : CNF α, codecCnfCost φ ≤ 2 ^ arity * (arity + 1) ∧
      ∀ a : α → Bool, φ.eval a = f (fun i => a (wire i)) := by
  classical
  obtain ⟨ψ, _, hlen, hwidth, heval⟩ := exists_cnf_boolFun arity f
  let wiring (j : ℕ) : α := if h : j < arity then wire ⟨j, h⟩ else default
  refine ⟨ψ.relabel wiring, ?_, ?_⟩
  · rw [codecCnfCost_relabel]
    have h := codecCnfCost_flatMap_le ψ (fun c => [c]) (arity + 1) (by
      intro c hc
      simpa [codecCnfCost] using Nat.add_le_add_right (hwidth c hc) 1)
    simpa using h.trans (Nat.mul_le_mul_right (arity + 1) hlen)
  · intro a
    rw [CNF.eval_relabel, heval]
    congr 1
    funext i
    simp [wiring, i.isLt]

/-- Positions jointly guarded by one local transition check. -/
private abbrev CodecPositions (M : FinTM Bool) (n s : ℕ) :=
  Fin (n + 2) × (Fin M.k → Fin (2 * s + 1))

/-- The joint head-position enumeration has polynomial size for a fixed machine.

**Proof sketch.** There are `n+2` input positions and `2s+1` independent positions
for each work head. Bound these factors by `u` and `2u`, with `u=s+n+2`. -/
private theorem codecPositions_card_le (M : FinTM Bool) (n s : ℕ) :
    Fintype.card (CodecPositions M n s) ≤
      2 ^ M.k * (s + n + 2) ^ (M.k + 1) := by
  simp only [CodecPositions, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  calc
    (n + 2) * (2 * s + 1) ^ M.k ≤
        (s + n + 2) * (2 * (s + n + 2)) ^ M.k :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [mul_pow, pow_succ]; ring

/-- Source and target bit tracks for a pair of finite rows. -/
private def codecPairBits {M : FinTM Bool} {n s : ℕ}
    (r t : CodecRow M n s) (p : Bool × CodecBit M n s) : Bool :=
  if p.1 then codecRowBits t p.2 else codecRowBits r p.2

/-- Place the target coordinates after one full padded source block. -/
private noncomputable def codecPairWire (M : FinTM Bool) (C n s : ℕ)
    (p : Bool × CodecBit M n s) : ℕ :=
  (if p.1 then C * (s + n + 1) else 0) + (Fintype.equivFin (CodecBit M n s) p.2).val

/-- Every pair coordinate lies inside the concatenation of the two code blocks. -/
private theorem codecPairWire_lt (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (p : Bool × CodecBit M n s) :
    codecPairWire M C n s p < 2 * (C * (s + n + 1)) := by
  have h := (Fintype.equivFin (CodecBit M n s) p.2).isLt.trans_le
    (codecBit_card_le M n s C hC)
  unfold codecPairWire
  cases p.1 <;> simp only [Bool.false_eq_true, if_false, if_true, zero_add] <;> omega

/-- Numbered pair coordinates read exactly the source or target finite-row bit. -/
private theorem configurationCodec_pair_get (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y)
    (p : Bool × CodecBit M n s) :
    (configurationCodec M C n s x c ++ configurationCodec M C n s y d).getD
        (codecPairWire M C n s p) false =
      codecPairBits (codecRowOf M n s x hx c) (codecRowOf M n s y hy d) p := by
  have hfit := codecBit_card_le M n s C hC
  have hi := (Fintype.equivFin (CodecBit M n s) p.2).isLt.trans_le hfit
  rcases p with ⟨side, bit⟩
  cases side
  · simp only [codecPairWire, Bool.false_eq_true, if_false, zero_add, codecPairBits]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa only [configurationCodec_length] using hi),
      ← List.getD_eq_getElem?_getD]
    simp only [configurationCodec, dif_pos hx, codecWord_get _ _ hfit]
  · simp only [codecPairWire, if_true, codecPairBits]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [configurationCodec_length]; omega),
      configurationCodec_length, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
    simp only [configurationCodec, dif_pos hy, codecWord_get _ _ hfit]

/-- Two clauses per input bit require equality of the carried input contents. -/
private def codecInputEquality (M : FinTM Bool) (n s : ℕ) : CNF (Bool × CodecBit M n s) :=
  (List.finRange n).flatMap fun i =>
    [[((false, .input i), false), ((true, .input i), true)],
      [((false, .input i), true), ((true, .input i), false)]]

/-- The input-equality conjunct compares exactly the input-content fields. -/
private theorem codecInputEquality_eval (M : FinTM Bool) (n s : ℕ) (r t : CodecRow M n s) :
    (codecInputEquality M n s).eval (codecPairBits r t) = true ↔ r.input = t.input := by
  have hbit (i : Fin n) : CNF.eval (codecPairBits r t)
      [[((false, CodecBit.input i), false), ((true, CodecBit.input i), true)],
        [((false, CodecBit.input i), true), ((true, CodecBit.input i), false)]] = true ↔
        r.input i = t.input i := by
    cases hr : r.input i <;> cases ht : t.input i <;>
      simp [CNF.eval, CNF.Clause.eval, codecPairBits, codecRowBits, hr, ht]
  simp only [codecInputEquality, codecCnf_eval_flatMap, List.mem_finRange, forall_const, hbit]
  exact funext_iff.symm

/-- Input equality costs six units per input position: two clauses of width two. -/
private theorem codecInputEquality_cost (M : FinTM Bool) (n s : ℕ) :
    codecCnfCost (codecInputEquality M n s) ≤ 6 * n := by
  have h := codecCnfCost_flatMap_le (List.finRange n)
    (fun i => [[((false, CodecBit.input (M := M) (s := s) i), false),
        ((true, .input i), true)], [((false, .input i), true), ((true, .input i), false)]])
    6 (fun _ _ => by simp [codecCnfCost])
  simpa only [List.length_finRange, Nat.mul_comm] using h

/-- Number the cross-input rejection conjunct in the two padded code blocks. -/
private noncomputable def configurationInputEquality (M : FinTM Bool) (C n s : ℕ) : CNF ℕ :=
  (codecInputEquality M n s).relabel (codecPairWire M C n s)

/-- Distinct carried inputs fail the equality conjunct, independently of transition checks. -/
private theorem configurationInputEquality_reject (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : x ≠ y) (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y) :
    (configurationInputEquality M C n s).eval
      (fun v => (configurationCodec M C n s x c ++ configurationCodec M C n s y d).getD v false)
      = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [configurationInputEquality, CNF.eval_relabel, Function.comp_def,
    configurationCodec_pair_get M C n s hC x y hx hy c d, codecInputEquality_eval] at h
  exact hxy (codecRowOf_input_eq M n s x y hx hy c d h)

/-- The cross-input equality conjunct has bounded indices and polynomial serialization. -/
private theorem configurationInputEquality_bounds (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (configurationInputEquality M C n s).numVars ≤ 2 * (C * (s + n + 1)) ∧
    (CNF.serialize (configurationInputEquality M C n s)).length ≤
      6 * n * (2 * (C * (s + n + 1)) + 3) + 1 := by
  have hb : ∀ cl ∈ codecInputEquality M n s, ∀ l ∈ cl,
      codecPairWire M C n s l.1 < 2 * (C * (s + n + 1)) :=
    fun _ _ l _ => codecPairWire_lt M C n s hC l.1
  refine ⟨codecCnf_numVars (codecInputEquality M n s) _ _ hb, ?_⟩
  exact (codecCnf_serialize (codecInputEquality M n s) _ _ hb).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (codecInputEquality_cost M n s)) 1)

/-- Equal windowed codes have equal successor vertices, through the public quotient bridge.
This is the deterministic instance of `NDTM.coreSum_stepWith`, not a second step proof. -/
private theorem configurationCodec_step_congr (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x : List Bool) (hx : x.length = n)
    (c d : Cfg M.k Bool M.State x) (hc : c.InWindow s) (hd : d.InWindow s)
    (h : configurationCodec M C n s x c = configurationCodec M C n s x d) :
    NDTM.coreSum (M.tm.step c) = NDTM.coreSum (M.tm.step d) := by
  have hv := (configurationCodec_eq_iff M C n s hC x hx c d hc hd).mp h
  exact NDTM.coreSum_stepWith M.tm.toNDTM false hv

/-- Beyond four, the exponential pays for a quadratic coefficient. -/
private theorem codec_square_le_pow (C : ℕ) (hC : 4 ≤ C) : C ^ 2 ≤ 2 ^ C := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hC
  induction t with
  | zero => norm_num
  | succ t ih =>
    have hi := ih (by omega)
    calc
      (4 + (t + 1)) ^ 2 ≤ 2 * (4 + t) ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ (4 + t) := Nat.mul_le_mul_left 2 hi
      _ = 2 ^ (4 + (t + 1)) := by
        rw [show 4 + (t + 1) = (4 + t) + 1 by omega, pow_succ]
        ring

/-- One constant can simultaneously dominate the width and the polynomial ledgers.

**Proof sketch.** Choose `C` at least four, the requested width coefficient, the
polynomial exponent, and `B·2^d`. Then `B·C·2^d ≤ C² ≤ 2^C`, so
`B·C ≤ 2^(C-d) ≤ u^(C-d)` for every `u≥2`. Multiply by `C·u^d`. -/
private theorem codec_absorb (B d K : ℕ) :
    ∃ C : ℕ, 0 < C ∧ K ≤ C ∧ ∀ u : ℕ, 2 ≤ u →
      B * C ^ 2 * u ^ d ≤ C * u ^ C := by
  let C := max 4 (max K (max d (B * 2 ^ d)))
  have h4 : 4 ≤ C := le_max_left _ _
  have hK : K ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hd : d ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hB : B * 2 ^ d ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, by omega, hK, fun u hu => ?_⟩
  have hpow : B * C ≤ 2 ^ (C - d) := by
    have hbig : (B * C) * 2 ^ d ≤ 2 ^ C := by
      calc
        _ = (B * 2 ^ d) * C := by ring
        _ ≤ C * C := Nat.mul_le_mul_right C hB
        _ ≤ 2 ^ C := by simpa [pow_two] using codec_square_le_pow C h4
    have hsplit : 2 ^ C = 2 ^ (C - d) * 2 ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [hsplit] at hbig
    have hp : 0 < 2 ^ d := by positivity
    nlinarith
  calc
    B * C ^ 2 * u ^ d = C * ((B * C) * u ^ d) := by ring
    _ ≤ C * (2 ^ (C - d) * u ^ d) :=
      Nat.mul_le_mul_left C (Nat.mul_le_mul_right _ hpow)
    _ ≤ C * (u ^ (C - d) * u ^ d) :=
      Nat.mul_le_mul_left C (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hu _))
    _ = C * u ^ C := by rw [← pow_add, Nat.sub_add_cancel hd]


/-- Exact window markers recover integer positions without clamping. -/
private theorem codec_posCode_eq_iff (s : ℕ) (z : ℤ) (hz : |z| ≤ s)
    (j : Fin (2 * s + 1)) :
    MultiTapeTM.ConfigCount.posCode s z = j ↔ z = (j.val : ℤ) - s := by
  constructor
  · intro h
    apply MultiTapeTM.ConfigCount.posCode_injOn s hz
    · have hj := j.isLt
      rw [abs_le]
      omega
    · simpa only [codec_posCode] using h
  · rintro rfl
    exact codec_posCode s j

/-- Observe the row coordinates using exact integer head markers. An exterior head
has no true marker; this prevents clamping from admitting an overflowing step. -/
private def codecObserve (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) : CodecBit M n s → Bool
  | .work i j b =>
      if b.val = 0 then decide (c.workTapes i ((j.val : ℤ) - s) = some false)
      else if b.val = 1 then decide (c.workTapes i ((j.val : ℤ) - s) = some true)
      else decide (c.workTapePos i = (j.val : ℤ) - s)
  | b => codecRowBits (codecRowOf M n s x hx c) b

/-- On windowed configurations, exact observations agree with the padded codec's row. -/
private theorem codecObserve_eq (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (hc : c.InWindow s) :
    codecObserve M n s x hx c = codecRowBits (codecRowOf M n s x hx c) := by
  funext b
  cases b with
  | work i j b =>
    simp only [codecObserve, codecRowBits, codecRowOf, MultiTapeTM.ConfigCount.coreCode]
    by_cases h0 : b.val = 0
    · simp only [h0, if_true]
    · by_cases h1 : b.val = 1
      · simp only [h1, if_true]
      · simp only [h0, h1, if_false, codec_posCode_eq_iff s _ (hc.1 i)]
  | _ => rfl

/-- Exact observations depend only on the public configuration-graph vertex. -/
private theorem codecObserve_congr (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c d : Cfg M.k Bool M.State x)
    (h : NDTM.coreSum c = NDTM.coreSum d) :
    codecObserve M n s x hx c = codecObserve M n s x hx d := by
  have hcore := congrArg Prod.fst h
  have hout := congrArg Prod.snd h
  change outSummary c.output = outSummary d.output at hout
  simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, Prod.mk.injEq] at hcore
  rcases hcore with ⟨hst, hip, hwt, hwp⟩
  funext b
  cases b <;> simp only [codecObserve, codecRowBits, codecRowOf,
    MultiTapeTM.ConfigCount.coreCode, hst, hip, hwt, hwp, hout]

/-- Applying a transition cannot write outside a window containing its old heads. -/
private theorem codec_step_blank (M : FinTM Bool) (s : ℕ) (x : List Bool)
    (c : Cfg M.k Bool M.State x) (hc : c.InWindow s) :
    ∀ i z, (s : ℤ) < |z| → (M.tm.step c).workTapes i z = none := by
  intro i z hz
  cases hs : c.state with
  | none => simpa only [MultiTapeTM.step, hs] using hc.2 i z hz
  | some q =>
    have hzhead : z ≠ c.workTapePos i := by
      intro he
      rw [he] at hz
      exact (not_lt_of_ge (hc.1 i)) hz
    simp only [MultiTapeTM.step, hs, Action.apply]
    cases hw : ((M.tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i).1 <;>
      simp [Function.update, hzhead, hc.2 i z hz]

/-- Equality of exact successor observations with a valid target is adjacency.

**Proof sketch.** The target's true head markers force each successor head into
the window. All exterior cells stay blank because writes occur at old heads.
The public finite-core injection then identifies the vertices. Conversely,
vertex equality preserves every observation. -/
private theorem codecObserve_step_iff (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c d : Cfg M.k Bool M.State x)
    (hc : c.InWindow s) (hd : d.InWindow s) :
    codecObserve M n s x hx (M.tm.step c) = codecRowBits (codecRowOf M n s x hx d) ↔
      NDTM.coreSum (M.tm.step c) = NDTM.coreSum d := by
  constructor
  · intro h
    have hwin : (M.tm.step c).InWindow s := by
      refine ⟨fun i => ?_, codec_step_blank M s x c hc⟩
      let j := (codecRowOf M n s x hx d).heads i
      have he := congrFun h (.work i j 2)
      have heq : (M.tm.step c).workTapePos i = (j.val : ℤ) - s := by
        apply of_decide_eq_true
        simpa [codecObserve, codecRowBits, j] using he
      rw [heq, abs_le]
      have hj := j.isLt
      omega
    rw [codecObserve_eq M n s x hx _ hwin] at h
    exact (codecRowOf_eq_iff M n s x hx _ d hwin hd).mp (codecRowBits_injective h)
  · intro h
    exact (codecObserve_congr M n s x hx _ d h).trans (codecObserve_eq M n s x hx d hd)

/-- A canonical representative of each of the three output summaries. -/
private def codecSummaryWord : OutSummary → List Bool
  | .empty => []
  | .accept => [true]
  | .dead => [false]

/-- The chosen representative has the prescribed output summary. -/
private theorem codecSummaryWord_summary (o : OutSummary) :
    outSummary (codecSummaryWord o) = o := by cases o <;> rfl

/-- Output histories may be normalized before taking a step, through the public
`coreSum_stepWith` bridge; the exact observed successor bits are unchanged. -/
private theorem codecObserve_step_normalize (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) :
    codecObserve M n s x hx (M.tm.step c) = codecObserve M n s x hx
      (M.tm.step { c with output := codecSummaryWord (outSummary c.output) }) := by
  apply codecObserve_congr
  apply NDTM.coreSum_stepWith M.tm.toNDTM false
  exact Prod.ext rfl (codecSummaryWord_summary (outSummary c.output)).symm

/-- The finite transition-table cases: control, scanned input, and scanned work symbols. -/
private abbrev CodecCase (M : FinTM Bool) :=
  Option M.State × Option Bool × (Fin M.k → Option Bool)

/-- Include a silent identity action for the halted case. -/
private def codecAction (M : FinTM Bool) (q : CodecCase M) : Action M.k Bool M.State :=
  match q.1 with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some st => M.tm.tr st q.2.1 q.2.2

/-- The case action computes the native step, including halted self-edges. -/
private theorem codecAction_apply (M : FinTM Bool) (x : List Bool)
    (c : Cfg M.k Bool M.State x) :
    (codecAction M (c.state, c.inputSymbol, c.workTapeSymbols)).apply c = M.tm.step c := by
  cases hs : c.state with
  | none =>
    apply Cfg.ext <;> simp [codecAction, hs, Action.apply, MultiTapeTM.step]
  | some q => simp only [codecAction, MultiTapeTM.step, hs]

/-- The constant number of Boolean ports read by a single guarded update gate. -/
private inductive CodecPort (M : FinTM Bool)
  | state | inputHead | inputSymbol
  | workHead : Fin M.k → CodecPort M
  | workSymbol : Fin M.k → Bool → CodecPort M
  | summary : Bool → CodecPort M
  | oldBit | newBit
  deriving Fintype, DecidableEq

/-- Gate arity is independent of the input length and window radius. -/
private theorem codecPort_card (M : FinTM Bool) : Fintype.card (CodecPort M) = 3 * M.k + 7 := by
  rw [← Fintype.card_congr (CodecPort.proxyTypeEquiv M)]
  simp
  ring

/-- A two-flag decoder for optional work symbols, with an arbitrary value on `11`. -/
private def codecReadSymbol (f t : Bool) : Option Bool :=
  if t then some true else if f then some false else none

/-- The symbol decoder recovers every legal two-flag encoding. -/
private theorem codecReadSymbol_flags (v : Option Bool) :
    codecReadSymbol (decide (v = some false)) (decide (v = some true)) = v := by
  cases v with
  | none => rfl
  | some b => cases b <;> rfl

/-- Decode the two summary flags; `11` is irrelevant on encoded configurations. -/
private def codecReadSummary (acc dead : Bool) : OutSummary :=
  if dead then .dead else if acc then .accept else .empty

/-- Summary decoding recovers the three canonical flag patterns. -/
private theorem codecReadSummary_flags (o : OutSummary) :
    codecReadSummary (decide (o = .accept)) (decide (o = .dead)) = o := by
  cases o <;> rfl

/-- Wire one input-symbol port; boundary cases ignore the arbitrary fallback wire. -/
private def codecInputWire (M : FinTM Bool) (n s : ℕ) (p : Fin (n + 2)) : CodecBit M n s :=
  if h : 0 < p.val ∧ p.val ≤ n then .input ⟨p.val - 1, by omega⟩ else .summary false

/-- The physical input boundaries read blank; interior positions read the wired bit. -/
private def codecInputRead {n : ℕ} (p : Fin (n + 2)) (b : Bool) : Option Bool :=
  if 0 < p.val ∧ p.val ≤ n then some b else none

/-- Wire the guard, scanned symbols, summary, and one old/new bit pair. -/
private def codecGateWire (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (b : CodecBit M n s) : CodecPort M → Bool × CodecBit M n s
  | .state => (false, .state q.1)
  | .inputHead => (false, .inputHead p.1)
  | .inputSymbol => (false, codecInputWire M n s p.1)
  | .workHead i => (false, .work i (p.2 i) 2)
  | .workSymbol i t => (false, .work i (p.2 i) (if t then 1 else 0))
  | .summary t => (false, .summary t)
  | .oldBit => (false, b)
  | .newBit => (true, b)

/-- A joint position/table guard. All quantification is over the machine's fixed tapes. -/
private def codecGuard (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (a : CodecPort M → Bool) : Prop :=
  a .state = true ∧ a .inputHead = true ∧ (∀ i, a (.workHead i) = true) ∧
    codecInputRead p.1 (a .inputSymbol) = q.2.1 ∧
    ∀ i, codecReadSymbol (a (.workSymbol i false)) (a (.workSymbol i true)) = q.2.2 i

/-- Under the input-position guard, the input-symbol port reads the actual input.

**Proof sketch.** An interior marker selects its predecessor-indexed input bit.
Either boundary instead gives blank, exactly as in the native input reader. -/
private theorem codecInputRead_wire (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (p : Fin (n + 2))
    (hp : (codecRowOf M n s x hx c).inputHead = p) :
    codecInputRead p (codecRowBits (codecRowOf M n s x hx c) (codecInputWire M n s p)) =
      c.inputSymbol := by
  have hv : c.inputPos.val = p.val := congrArg Fin.val hp
  by_cases hi : 0 < p.val ∧ p.val ≤ n
  · have h0 : c.inputPos ≠ 0 := by
      intro h
      have hz : c.inputPos.val = 0 := Fin.val_eq_zero_iff.mpr h
      omega
    have hn : c.inputPos.val ≠ x.length + 1 := by omega
    have hlt : c.inputPos.val - 1 < x.length := by omega
    simp only [codecInputRead, if_pos hi, codecInputWire, dif_pos hi, codecRowBits,
      codecRowOf, Cfg.inputSymbol, dif_neg h0, dif_neg hn]
    simp [List.getD_eq_getElem?_getD, ← hv, hlt]
  · have hboundary : c.inputPos = 0 ∨ c.inputPos.val = x.length + 1 := by
      have hp := p.isLt
      by_cases hz : c.inputPos.val = 0
      · exact Or.inl (Fin.ext hz)
      · exact Or.inr (by omega)
    rcases hboundary with h0 | hn
    · simp only [codecInputRead, if_neg hi, Cfg.inputSymbol, dif_pos h0]
    · simp only [codecInputRead, if_neg hi, Cfg.inputSymbol, dif_pos hn]
      split <;> rfl

/-- On encoded rows, the gate guard tests exactly the selected positions and reads. -/
private theorem codecGuard_rows (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (b : CodecBit M n s) (r t : CodecRow M n s) :
    codecGuard M n s p q (codecPairBits r t ∘ codecGateWire M n s p q b) ↔
      r.state = q.1 ∧ r.inputHead = p.1 ∧ (∀ i, r.heads i = p.2 i) ∧
      codecInputRead p.1 (codecRowBits r (codecInputWire M n s p.1)) = q.2.1 ∧
      ∀ i, r.symbols i (p.2 i) = q.2.2 i := by
  simp [codecGuard, codecGateWire, codecPairBits, codecRowBits,
    codecReadSymbol_flags]

/-- Native meaning of a true guard on a windowed configuration.

**Proof sketch.** The one-hot markers identify all head positions. Decode the
work-symbol flags at those positions, and use the carried input bit except at
the two blank boundaries. These are exactly the machine's scanned symbols. -/
private theorem codecGuard_spec (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (hc : c.InWindow s)
    (t : CodecRow M n s) (p : CodecPositions M n s) (q : CodecCase M) (b : CodecBit M n s) :
    codecGuard M n s p q
      (codecPairBits (codecRowOf M n s x hx c) t ∘ codecGateWire M n s p q b) ↔
      c.state = q.1 ∧ (codecRowOf M n s x hx c).inputHead = p.1 ∧
      (∀ i, c.workTapePos i = ((p.2 i).val : ℤ) - s) ∧
      c.inputSymbol = q.2.1 ∧ c.workTapeSymbols = q.2.2 := by
  rw [codecGuard_rows]
  have hh (i : Fin M.k) : (codecRowOf M n s x hx c).heads i = p.2 i ↔
      c.workTapePos i = ((p.2 i).val : ℤ) - s :=
    codec_posCode_eq_iff s _ (hc.1 i) _
  constructor
  · rintro ⟨hst, hip, hwp, hin, hws⟩
    have hp := fun i => (hh i).mp (hwp i)
    refine ⟨hst, hip, hp, ?_, ?_⟩
    · rwa [codecInputRead_wire M n s x hx c _ hip] at hin
    · funext i
      simpa only [codecRowOf, MultiTapeTM.ConfigCount.coreCode,
        Cfg.workTapeSymbols, hp i] using hws i
  · rintro ⟨hst, hip, hwp, hin, hws⟩
    refine ⟨hst, hip, fun i => (hh i).mpr (hwp i), ?_, ?_⟩
    · simpa only [codecInputRead_wire M n s x hx c _ hip] using hin
    · intro i
      simpa only [codecRowOf, MultiTapeTM.ConfigCount.coreCode,
        Cfg.workTapeSymbols, hwp i] using congrFun hws i

/-- One output bit of the selected action: copy unmarked cells, write at old
heads, shift markers, rewrite the state, and update the output summary. -/
private def codecExpected (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (act : Action M.k Bool M.State) (a : CodecPort M → Bool) : CodecBit M n s → Bool
  | .input _ => a .oldBit
  | .inputHead j => decide (moveInputPos p.1 act.inputTape = j)
  | .state st => decide (act.state = st)
  | .work i j b =>
      if b.val = 0 ∨ b.val = 1 then
        if p.2 i = j then
          match (act.workTapes i).1 with
          | none => a .oldBit
          | some v => decide (v = some (decide (b.val = 1)))
        else a .oldBit
      else decide (((p.2 i).val : ℤ) - s + ((act.workTapes i).2 : ℤ) = (j.val : ℤ) - s)
  | .summary dead => decide
      (outSummary (codecSummaryWord (codecReadSummary (a (.summary false)) (a (.summary true))) ++
        act.output.toList) = if dead then .dead else .accept)

/-- The guarded single-bit predicate compiled by per-gate Boolean universality. -/
private noncomputable def codecGate (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (b : CodecBit M n s) (a : CodecPort M → Bool) : Bool := by
  classical
  exact decide (codecGuard M n s p q a → a .newBit = codecExpected M n s p (codecAction M q) a b)

/-- Each expected bit is the exact bit of the action applied to the canonical
output representative; only the guard's positions and a constant number of bits enter.

**Proof sketch.** Input content is unchanged, state and input-head markers follow
the action, and the two work-symbol flags copy except at a written head cell.
The integer head equation retains an exterior move rather than clamping it.
The summary ports supply the canonical output word for the append table. -/
private theorem codecExpected_apply (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (t : CodecRow M n s)
    (p : CodecPositions M n s) (q : CodecCase M) (act : Action M.k Bool M.State)
    (hp : (codecRowOf M n s x hx c).inputHead = p.1)
    (hh : ∀ i, c.workTapePos i = ((p.2 i).val : ℤ) - s) (b : CodecBit M n s) :
    codecExpected M n s p act
      (codecPairBits (codecRowOf M n s x hx c) t ∘ codecGateWire M n s p q b) b =
    codecObserve M n s x hx
      (act.apply { c with output := codecSummaryWord (outSummary c.output) }) b := by
  cases b with
  | input i => rfl
  | inputHead j =>
    subst n
    have hpos : c.inputPos = p.1 := hp
    change decide (moveInputPos p.1 act.inputTape = j) =
      decide (moveInputPos c.inputPos act.inputTape = j)
    rw [hpos]
  | state st => rfl
  | summary d =>
    simp [codecExpected, codecObserve, codecGateWire, codecPairBits, codecRowBits,
      codecRowOf, Action.apply, codecReadSummary_flags]
  | work i j b =>
    have hcell : ((j.val : ℤ) - s = c.workTapePos i) ↔ p.2 i = j := by
      rw [hh i]
      constructor
      · intro h
        apply Fin.ext
        omega
      · rintro h
        rw [h]
    fin_cases b <;>
      simp only [codecExpected, codecObserve, Function.comp_apply, codecGateWire,
        codecPairBits, Bool.false_eq_true, if_false, codecRowBits, codecRowOf,
        MultiTapeTM.ConfigCount.coreCode, Action.apply]
    · rcases Option.eq_none_or_eq_some ((act.workTapes i).1) with hw | ⟨v, hw⟩ <;>
        by_cases hj : p.2 i = j <;>
        simp [hw, hj, Function.update, hcell]
    · rcases Option.eq_none_or_eq_some ((act.workTapes i).1) with hw | ⟨v, hw⟩ <;>
        by_cases hj : p.2 i = j <;>
        simp [hw, hj, Function.update, hcell]
    · simp [hh i]

/-- A true transition guard makes its expected bit the actual successor bit.
Output normalization is justified by `NDTM.coreSum_stepWith`. -/
private theorem codecExpected_step (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (hc : c.InWindow s)
    (t : CodecRow M n s) (p : CodecPositions M n s) (q : CodecCase M) (b : CodecBit M n s)
    (h : codecGuard M n s p q
      (codecPairBits (codecRowOf M n s x hx c) t ∘ codecGateWire M n s p q b)) :
    codecExpected M n s p (codecAction M q)
      (codecPairBits (codecRowOf M n s x hx c) t ∘ codecGateWire M n s p q b) b =
      codecObserve M n s x hx (M.tm.step c) b := by
  obtain ⟨hst, hip, hwp, hin, hws⟩ := (codecGuard_spec M n s x hx c hc t p q b).mp h
  have he : (c.state, c.inputSymbol, c.workTapeSymbols) = q :=
    Prod.ext hst (Prod.ext hin hws)
  have ha : (codecAction M q).apply { c with output := codecSummaryWord (outSummary c.output) } =
      M.tm.step { c with output := codecSummaryWord (outSummary c.output) } := by
    rw [← he]
    exact codecAction_apply M x { c with output := codecSummaryWord (outSummary c.output) }
  calc
    _ = codecObserve M n s x hx
        ((codecAction M q).apply { c with output := codecSummaryWord (outSummary c.output) }) b :=
      codecExpected_apply M n s x hx c t p q _ hip hwp b
    _ = codecObserve M n s x hx
        (M.tm.step { c with output := codecSummaryWord (outSummary c.output) }) b := by rw [ha]
    _ = _ := congrFun (codecObserve_step_normalize M n s x hx c).symm b

/-- Compile one finite-port gate, retaining a machine-only cost bound. -/
private theorem codecGate_cnf (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (b : CodecBit M n s) :
    ∃ φ : CNF (Bool × CodecBit M n s),
      codecCnfCost φ ≤ 2 ^ (3 * M.k + 7) * (3 * M.k + 8) ∧
      ∀ a, φ.eval a = codecGate M n s p q b (a ∘ codecGateWire M n s p q b) := by
  letI : Inhabited (Bool × CodecBit M n s) := ⟨(false, .summary false)⟩
  let e := Fintype.equivFin (CodecPort M)
  obtain ⟨φ, hcost, heval⟩ := codecLocalCheck (Fintype.card (CodecPort M))
    (fun i => codecGateWire M n s p q b (e.symm i))
    (fun a => codecGate M n s p q b (fun port => a (e port)))
  refine ⟨φ, ?_, ?_⟩
  · simpa only [codecPort_card, Nat.add_assoc] using hcost
  · intro a
    simpa only [e.symm_apply_apply, Function.comp_def] using heval a

/-- Choose the per-gate CNF from the proved constant-arity universality bound. -/
private noncomputable def codecGateCNF (M : FinTM Bool) (n s : ℕ)
    (p : CodecPositions M n s) (q : CodecCase M) (b : CodecBit M n s) :
    CNF (Bool × CodecBit M n s) := (codecGate_cnf M n s p q b).choose

/-- The chosen gate formula has exactly its local semantics and machine-only cost. -/
private theorem codecGateCNF_spec (M : FinTM Bool) (n s : ℕ)
    (p : CodecPositions M n s) (q : CodecCase M) (b : CodecBit M n s) :
    codecCnfCost (codecGateCNF M n s p q b) ≤ 2 ^ (3 * M.k + 7) * (3 * M.k + 8) ∧
    ∀ a, (codecGateCNF M n s p q b).eval a =
      codecGate M n s p q b (a ∘ codecGateWire M n s p q b) :=
  (codecGate_cnf M n s p q b).choose_spec

/-- Enumerate the guarded positions, finite table cases, and updated coordinates. -/
private abbrev CodecGateIndex (M : FinTM Bool) (n s : ℕ) :=
  CodecPositions M n s × CodecCase M × CodecBit M n s

/-- Conjoin one constant-arity gate for each guarded coordinate update. -/
private noncomputable def codecTransitionCNF (M : FinTM Bool) (n s : ℕ) :
    CNF (Bool × CodecBit M n s) :=
  (Finset.univ.toList : List (CodecGateIndex M n s)).flatMap fun ix =>
    codecGateCNF M n s ix.1 ix.2.1 ix.2.2

/-- The transition conjunction enforces exactly all of its local update gates. -/
private theorem codecTransitionCNF_eval (M : FinTM Bool) (n s : ℕ)
    (a : Bool × CodecBit M n s → Bool) :
    (codecTransitionCNF M n s).eval a = true ↔
      ∀ p q b, codecGate M n s p q b (a ∘ codecGateWire M n s p q b) = true := by
  have hg := fun p q b => (codecGateCNF_spec M n s p q b).2 a
  simp only [codecTransitionCNF, codecCnf_eval_flatMap, Finset.mem_toList,
    Finset.mem_univ, forall_const, CodecGateIndex, Prod.forall, hg]

/-- The local conjunction is equivalent to adjacency on windowed same-input pairs.

**Proof sketch.** For soundness, choose the actual head tuple and scanned-symbol
case. Its guard is true, so every target bit equals the exact successor bit;
the exact-marker lemma identifies the successor vertex. For completeness,
every true guard reads the same native transition, whose bits match the target.
This includes the silent halted identity action and exterior-head rejection. -/
private theorem codecTransitionCNF_step_iff (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c d : Cfg M.k Bool M.State x)
    (hc : c.InWindow s) (hd : d.InWindow s) :
    (codecTransitionCNF M n s).eval
      (codecPairBits (codecRowOf M n s x hx c) (codecRowOf M n s x hx d)) = true ↔
      NDTM.coreSum (M.tm.step c) = NDTM.coreSum d := by
  rw [codecTransitionCNF_eval, ← codecObserve_step_iff M n s x hx c d hc hd]
  constructor
  · intro h
    let p : CodecPositions M n s :=
      ((codecRowOf M n s x hx c).inputHead, (codecRowOf M n s x hx c).heads)
    let q : CodecCase M := (c.state, c.inputSymbol, c.workTapeSymbols)
    funext b
    have hg : codecGuard M n s p q
        (codecPairBits (codecRowOf M n s x hx c) (codecRowOf M n s x hx d) ∘
          codecGateWire M n s p q b) := by
      apply (codecGuard_spec M n s x hx c hc _ p q b).mpr
      refine ⟨rfl, rfl, ?_, rfl, rfl⟩
      intro i
      exact (codec_posCode_eq_iff s _ (hc.1 i) _).mp rfl
    have hb := h p q b
    simp only [codecGate, decide_eq_true_eq] at hb
    have he := hb hg
    change codecRowBits (codecRowOf M n s x hx d) b = _ at he
    exact (codecExpected_step M n s x hx c hc _ p q b hg).symm.trans he.symm
  · intro h p q b
    simp only [codecGate, decide_eq_true_eq]
    intro hg
    change codecRowBits (codecRowOf M n s x hx d) b = _
    rw [codecExpected_step M n s x hx c hc _ p q b hg, h]

/-- Counting local gates multiplies positions, fixed machine cases, coordinates,
and the constant per-gate cost; no row truth table appears. -/
private theorem codecTransitionCNF_cost (M : FinTM Bool) (n s : ℕ) :
    codecCnfCost (codecTransitionCNF M n s) ≤
      Fintype.card (CodecPositions M n s) * Fintype.card (CodecCase M) *
      Fintype.card (CodecBit M n s) * (2 ^ (3 * M.k + 7) * (3 * M.k + 8)) := by
  have h := codecCnfCost_flatMap_le (Finset.univ.toList : List (CodecGateIndex M n s))
    (fun ix => codecGateCNF M n s ix.1 ix.2.1 ix.2.2)
    (2 ^ (3 * M.k + 7) * (3 * M.k + 8)) (fun ix _ => (codecGateCNF_spec M n s _ _ _).1)
  simpa only [codecTransitionCNF, Finset.length_toList, Finset.card_univ,
    CodecGateIndex, Fintype.card_prod, Nat.mul_assoc] using h

/-- The numbered adjacency formula includes the separate carried-input equality conjunct. -/
private noncomputable def configurationAdjacency (M : FinTM Bool) (C n s : ℕ) : CNF ℕ :=
  (codecInputEquality M n s ++ codecTransitionCNF M n s).relabel (codecPairWire M C n s)

/-- The numbered adjacency formula has the required quotient-step interpretation. -/
private theorem configurationAdjacency_eval (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x : List Bool) (hx : x.length = n)
    (c d : Cfg M.k Bool M.State x) (hc : c.InWindow s) (hd : d.InWindow s) :
    (configurationAdjacency M C n s).eval
      (fun v => (configurationCodec M C n s x c ++ configurationCodec M C n s x d).getD v false)
      = true ↔ NDTM.coreSum (M.tm.step c) = NDTM.coreSum d := by
  simp only [configurationAdjacency, CNF.eval_relabel, Function.comp_def,
    configurationCodec_pair_get M C n s hC x x hx hx c d, CNF.eval_append,
    Bool.and_eq_true, codecInputEquality_eval, codecTransitionCNF_step_iff M n s x hx c d hc hd]
  exact and_iff_right rfl

/-- Different carried inputs fail the adjacency formula's equality conjunct. -/
private theorem configurationAdjacency_reject (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : x ≠ y) (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y) :
    (configurationAdjacency M C n s).eval
      (fun v => (configurationCodec M C n s x c ++ configurationCodec M C n s y d).getD v false)
      = false := by
  rw [configurationAdjacency, CNF.relabel_append, CNF.eval_append]
  change ((configurationInputEquality M C n s).eval _ && _) = false
  rw [configurationInputEquality_reject M C n s hC x y hx hy hxy c d]
  rfl

/-- Machine-only coefficient for the joint transition enumeration. -/
private def codecTransitionCoefficient (M : FinTM Bool) : ℕ :=
  2 ^ M.k * Fintype.card (CodecCase M) * (2 ^ (3 * M.k + 7) * (3 * M.k + 8))

/-- The transition gates have polynomial cost, of degree `k+2` before serialization. -/
private theorem codecTransitionCNF_cost_poly (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    codecCnfCost (codecTransitionCNF M n s) ≤
      codecTransitionCoefficient M * C * (s + n + 2) ^ (M.k + 2) := by
  have hp := codecPositions_card_le M n s
  have hb : Fintype.card (CodecBit M n s) ≤ C * (s + n + 2) :=
    (codecBit_card_le M n s C hC).trans (Nat.mul_le_mul_left _ (by omega))
  calc
    _ ≤ Fintype.card (CodecPositions M n s) * Fintype.card (CodecCase M) *
        Fintype.card (CodecBit M n s) * (2 ^ (3 * M.k + 7) * (3 * M.k + 8)) :=
      codecTransitionCNF_cost M n s
    _ ≤ (2 ^ M.k * (s + n + 2) ^ (M.k + 1)) * Fintype.card (CodecCase M) *
        (C * (s + n + 2)) * (2 ^ (3 * M.k + 7) * (3 * M.k + 8)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ hp) hb)
    _ = _ := by unfold codecTransitionCoefficient; rw [pow_succ]; ring

/-- Input equality and transition gates share the degree-`k+2` cost ledger. -/
private theorem codecAdjacency_cost (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    codecCnfCost (codecInputEquality M n s ++ codecTransitionCNF M n s) ≤
      (6 + codecTransitionCoefficient M) * C * (s + n + 2) ^ (M.k + 2) := by
  have hpos : 1 ≤ C := by unfold codecCoefficient at hC; omega
  have hn : n ≤ C * (s + n + 2) ^ (M.k + 2) := by
    calc
      n ≤ s + n + 2 := by omega
      _ ≤ (s + n + 2) ^ (M.k + 2) := Nat.le_pow (by omega)
      _ ≤ C * (s + n + 2) ^ (M.k + 2) := Nat.le_mul_of_pos_left _ (by omega)
  rw [codecCnfCost_append]
  calc
    _ ≤ 6 * n + codecTransitionCoefficient M * C * (s + n + 2) ^ (M.k + 2) :=
      Nat.add_le_add (codecInputEquality_cost M n s) (codecTransitionCNF_cost_poly M C n s hC)
    _ ≤ 6 * (C * (s + n + 2) ^ (M.k + 2)) +
        codecTransitionCoefficient M * C * (s + n + 2) ^ (M.k + 2) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 6 hn) _
    _ = _ := by ring

/-- Adjacency uses only the two code blocks and has a polynomial serialized length.

**Proof sketch.** Every variable is wired into one of the two padded blocks.
The cost ledger counts both literal occurrences and clause delimiters, including
empty clauses. The public serialization grammar adds one factor bounded by
`5 C (s+n+2)`, hence degree `k+3`; the final terminator is included explicitly. -/
private theorem configurationAdjacency_bounds (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (configurationAdjacency M C n s).numVars ≤ 2 * (C * (s + n + 1)) ∧
    (CNF.serialize (configurationAdjacency M C n s)).length ≤
      (5 * (6 + codecTransitionCoefficient M) + 1) * C ^ 2 * (s + n + 2) ^ (M.k + 3) := by
  have hb : ∀ cl ∈ codecInputEquality M n s ++ codecTransitionCNF M n s,
      ∀ l ∈ cl, codecPairWire M C n s l.1 < 2 * (C * (s + n + 1)) :=
    fun _ _ l _ => codecPairWire_lt M C n s hC l.1
  refine ⟨codecCnf_numVars _ _ _ hb, ?_⟩
  have hpos : 1 ≤ C := by unfold codecCoefficient at hC; omega
  have hindex : 2 * (C * (s + n + 1)) + 3 ≤ 5 * C * (s + n + 2) := by nlinarith
  have hterm : 1 ≤ C ^ 2 * (s + n + 2) ^ (M.k + 3) := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))
  calc
    _ ≤ codecCnfCost (codecInputEquality M n s ++ codecTransitionCNF M n s) *
        (2 * (C * (s + n + 1)) + 3) + 1 := codecCnf_serialize _ _ _ hb
    _ ≤ ((6 + codecTransitionCoefficient M) * C * (s + n + 2) ^ (M.k + 2)) *
        (5 * C * (s + n + 2)) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul (codecAdjacency_cost M C n s hC) hindex) 1
    _ = 5 * (6 + codecTransitionCoefficient M) * C ^ 2 *
        (s + n + 2) ^ (M.k + 3) + 1 := by rw [pow_succ]; ring
    _ ≤ 5 * (6 + codecTransitionCoefficient M) * C ^ 2 *
        (s + n + 2) ^ (M.k + 3) + C ^ 2 * (s + n + 2) ^ (M.k + 3) :=
      Nat.add_le_add_left hterm _
    _ = _ := by ring


/-- **Claim 4.4(2), packaged quotient form** (proved — phase
P4.3 round 2; see the module docstring's declared deviations): for every
machine there is a constant `C` such that for all `(n, s)` there are a
configuration bit-codec — fixed length `C · (s + n + 1)`, **factoring through the input and the
vertex quotient** `Turing.NDTM.coreSum` on windowed configurations (an iff:
equal codes exactly when equal vertices, at one input) — and three CNFs: `φv` characterizing exactly the codec image
among the length-matching strings, `φa` deciding adjacency (the step, read on
the vertex quotient) on same-input windowed pairs and rejecting cross-input
pairs, and `φacc` deciding acceptance (halted state, `accept` summary); all
three with `numVars` inside the code width and serialized lengths bounded by
`C · (s + n + 2) ^ C` — base `s + n + 2`, not the code width's `s + n + 1`:
at `n = s = 0` the code width equals `C` while one literal reading the
second block already serializes to `C + 6` (round-2 blocker, finding 1).

**Proof sketch.** The codec is the marker discipline of the Cook-Levin
tableau row (`TCSlib.Complexity.CookLevin` precedents), now carrying the
input: an input-content track of `n` bits, a one-hot input-position track of
length `n + 2`, a one-hot state block (halt included), per work tape a window
track of `2s + 1` cells — three-valued symbol plus a head-marker bit — and a
two-bit summary block; total length linear in `s + n` with the machine's
constants in `C`, padded to the exact `C · (s + n + 1)`. Injectivity to
`(x, coreSum)` mirrors `Turing.MultiTapeTM.ConfigCount.coreCode_inj` on the
window tracks plus the content track; the output enters only through the
summary block (full-output injectivity is impossible and not claimed —
round-1 finding 1). `φv` conjoins per-track well-formedness (one-hot blocks,
trit ranges, canonical padding); `φacc` reads the halt pattern and the
summary block; `φa` conjoins content-track equality, locality of unmarked
window cells, the marked-cell and neighbor updates by the transition table —
the scanned input bit read from the content track under the position
marker — the one-hot shifts by at most one, the state rewrite, and the
summary update (`Turing.outSummary`'s append table): the one-hot blocks' uniqueness
constraints are pairwise-exclusion clauses — quadratic in the block length,
polynomial overall — and the transition checks are enumerated over the
input-position and work-head tuples jointly with the finitely many
state/scanned-symbol cases (the head markers couple the tracks:
`(n + 2) · (2s + 1)^k` guarded cases for the fixed machine), each case a
constant-size CNF by the chapter-2 universality
(`Complexity.exists_cnf_boolFun`, applied per **gate**, never per row — a
whole-row truth table is exponential); the honest count is polynomial, not
linear (round-2 finding 4), bounding clause count, `numVars`, and the
serialized lengths (the chapter-2 grammar's serialization-length equation —
clause count enters it explicitly, round-1 finding 8). Fill obligations,
named: the codec definition with exact-length padding; the two injectivity
lemmas; the validity characterization in both directions; the per-position
check enumeration; the three serialized-size ledgers; the
step-iff-adjacency equivalence through `Turing.NDTM.coreSum_stepWith`. -/
theorem exists_adjacency_codec_cnf (M : Turing.FinTM Bool) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n s : ℕ),
      ∃ (code : (x : List Bool) → Cfg M.k Bool M.State x → List Bool)
        (φv φa φacc : CNF ℕ),
        (∀ (x : List Bool) (c : Cfg M.k Bool M.State x),
          (code x c).length = C * (s + n + 1)) ∧
        (∀ (x x' : List Bool), x.length = n → x'.length = n →
          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
            c.InWindow s → c'.InWindow s → code x c = code x' c' → x = x') ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
            (code x c = code x d ↔ NDTM.coreSum c = NDTM.coreSum d)) ∧
        (∀ w : List Bool, w.length = C * (s + n + 1) →
          (φv.eval (fun v => w.getD v false) = true ↔
            ∃ (x : List Bool), x.length = n ∧
              ∃ c : Cfg M.k Bool M.State x, c.InWindow s ∧ w = code x c)) ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
            (φa.eval (fun v => (code x c ++ code x d).getD v false) = true ↔
              NDTM.coreSum (M.tm.step c) = NDTM.coreSum d)) ∧
        (∀ (x x' : List Bool), x.length = n → x'.length = n → x ≠ x' →
          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
            c.InWindow s → c'.InWindow s →
            φa.eval (fun v => (code x c ++ code x' c').getD v false) = false) ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c : Cfg M.k Bool M.State x, c.InWindow s →
            (φacc.eval (fun v => (code x c).getD v false) = true ↔
              (c.state = none ∧ outSummary c.output = OutSummary.accept))) ∧
        φv.numVars ≤ C * (s + n + 1) ∧
        φacc.numVars ≤ C * (s + n + 1) ∧
        φa.numVars ≤ 2 * (C * (s + n + 1)) ∧
        (CNF.serialize φv).length ≤ C * (s + n + 2) ^ C ∧
        (CNF.serialize φa).length ≤ C * (s + n + 2) ^ C ∧
        (CNF.serialize φacc).length ≤ C * (s + n + 2) ^ C := by
  let B := (3 * codecValidityCoefficient M + 7) +
    (5 * (6 + codecTransitionCoefficient M) + 1) + 13
  obtain ⟨C, hC, hwidth, hsize⟩ := codec_absorb B (M.k + 3) (codecCoefficient M)
  refine ⟨C, hC, fun n s => ?_⟩
  have hp : (s + n + 2) ^ 3 ≤ (s + n + 2) ^ (M.k + 3) := by
    rw [pow_add]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hledger (a e : ℕ) (ha : a ≤ B)
      (he : (s + n + 2) ^ e ≤ (s + n + 2) ^ (M.k + 3)) :
      a * C ^ 2 * (s + n + 2) ^ e ≤ C * (s + n + 2) ^ C :=
    (Nat.mul_le_mul (Nat.mul_le_mul_right _ ha) he).trans (hsize _ (by omega))
  refine ⟨configurationCodec M C n s, configurationValidity M C n s,
    configurationAdjacency M C n s, configurationAcceptance M n s,
    configurationCodec_length M C n s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy c d _ _ he
    exact configurationCodec_input_eq M C n s hwidth x y hx hy c d he
  · intro x hx c d hc hd
    exact configurationCodec_eq_iff M C n s hwidth x hx c d hc hd
  · exact configurationValidity_eval M C n s hwidth
  · intro x hx c d hc hd
    exact configurationAdjacency_eval M C n s hwidth x hx c d hc hd
  · intro x y hx hy hxy c d _ _
    exact configurationAdjacency_reject M C n s hwidth x y hx hy hxy c d
  · intro x hx c _
    exact configurationAcceptance_eval M C n s hwidth x hx c
  · exact configurationValidity_numVars M C n s hwidth
  · exact (configurationAcceptance_bounds M C n s hwidth).1
  · exact (configurationAdjacency_bounds M C n s hwidth).1
  · exact (configurationValidity_size M C n s hwidth).trans
      (hledger _ 3 (by dsimp [B]; omega) hp)
  · exact (configurationAdjacency_bounds M C n s hwidth).2.trans
      (hledger _ (M.k + 3) (by dsimp [B]; omega) (Nat.le_refl _))
  · exact (configurationAcceptance_size M C n s hwidth).trans
      (hledger 13 3 (by dsimp [B]; omega) hp)

/-- **The language `TQBF`** [AB09, §4.2]: binary strings whose decoded
quantified formula is true. The decoding fallback is the true closed formula,
so non-well-formed strings are members — the `SAT`-polarity convention of
`Complexity.QBF.decode`. -/
def TQBF : Language Bool :=
  {x | (QBF.decode x).truth}

/-- **`TQBF ∈ PSPACE`** ([AB09, Theorem 4.13, membership half]; spec, fill
pending): truth of a quantified formula is decidable in polynomial space.

**Proof sketch.** Validate the **entire** encoding before any matrix
verdict: trailing garbage makes the total decoder select the true fallback,
so a scanned prefix that "looks unsatisfiable" must not short-circuit
(round-1 answer 5). Then the recursive evaluator `A` of [AB09]: peel the
first quantifier, evaluate both restrictions, combine by the quantifier —
realized iteratively with a partial-assignment word of one trit per prefix
variable (the book's footnote: the linear-space global-array variant) walked
depth-first by the loop combinator, with no per-level formula copies; the
base case evaluates the CNF matrix under the assembled assignment by one
scan per clause, re-reading prefix bits and matrix bytes from the input. Space: the assignment
word (linear), the matrix cursor (linear), the recursion is depth-first on
the word in place — `O(n)` cells, inside `SPACE (n + 1) ⊆ PSPACE`. Fill
obligations, named: the depth-first assignment walker (a §12 loop/catalog
consumer), the CNF evaluator machine (one-pass per clause over the decoded
matrix), the parser reuse (`Complexity.QBF.decode` realized by the chapter-2
parser machinery), and the `DecidesInSpace` packaging. -/
theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE := by
  sorry

/-- **`TQBF` is `PSPACE`-hard** ([AB09, Theorem 4.13, hardness half]; spec,
fill pending — **the phase-P4.3 fill summit**, the `ψᵢ` emitter).

**Proof sketch.** Let `L ∈ PSPACE`, decided by `M` in space `c₀ · (n^c + 1)`.
On input `x` (length `n`, window radius `s := c₀·(n^c + 1)`), the reduction
emits a quantified formula asserting "some accepting vertex is reachable
from the initial vertex within `2^ℓ` steps" over the packaged carrier of
`Complexity.exists_adjacency_codec_cnf`: vertices are the
`ℓ := C·(s + n + 1)`-bit codes of input-carrying windowed quotient
configurations, with `Valid := φv`, `Next := φa`, `Accept := φacc`. The
midpoint recursion is
`ψ₀(a, b) := Valid a ∧ Valid b ∧ (a = b ∨ Next (a, b))` — the base includes
length-zero paths — `Next` self-loops are guaranteed only at halted
vertices, and a live vertex may or may not be self-adjacent (round-1
finding 6; round-2 finding 3) — and
`ψᵢ₊₁(a, b) := ∃ z (Valid z ∧ ∀ u v, ((u,v) = (a,z) ∨ (u,v) = (z,b)) → ψᵢ(u,v))`
([AB09]'s succinct `∀`-trick keeping one copy of `ψᵢ`, with the midpoint
**guarded by `Valid`** — unguarded quantification admits paths through junk
codes, round-1 finding 3), unfolded to depth `ℓ` (at most `2^ℓ` codes, so a
shortest path fits), against the emitted initial-vertex code and an
existentially quantified `Accept` target (no unique accepting configuration
is needed). Prenex first, then Tseitin: the gate variables of the CNF
conversion are existentially quantified **after** the original prefix — gate
values must not be fixed before universal variables they depend on (round-1
answer 5) — with constant-arity gate constraints via the chapter-2
universality (`Complexity.exists_cnf_boolFun` per gate, never per level).
Size: `O(ℓ)` scaffolding per level over `ℓ` levels, with a `Valid` copy at
every level plus the two base guards — the packaged CNFs appear `O(ℓ)`
times, and index shifts change their unary serializations; all counted in
the ledger (round-2 finding 6) — polynomial by the serialized-length
clauses. Truth iff reachability
iff `M` accepts `x`: the quotient dictionary
(`Turing.NDTM.reflTransGen_cfgStep_iff` through `Turing.MultiTapeTM.toNDTM`)
with path lifting via `Turing.NDTM.coreSum_stepWith`, the space bound
keeping every genuine run inside the window. **The packaged existential
supplies no algorithm** (round-1 major 2): the uniform emitter — the
polynomial-time construction and serialization of `φv`/`φa`/`φacc`, the
initial-vertex code, the per-level scaffolding with its level-blocked
variable indexing, and the final assembly through
`Complexity.QBF.decode_encode` — is a set of **private, named fill
obligations of this proof**, in the chapter-2 streaming-emitter discipline
(`CookLevin/Hardness.lean`, the six-stage output-silence contract; §12
catalog routines); **continuation budget certain**. Fill obligations, named:
the three-CNF emitter family and its serialization-length ledger; the
initial-code computation; the level-blocked indexing scheme (unary-serialized
per the CNF grammar); the truth-preservation induction
`ψᵢ ↔ reachability within 2^i`, both directions of the guarded recursion;
the Tseitin-after-prefix equivalence; the final assembly through
`Complexity.QBF.decode_encode`. -/
theorem TQBF_PSPACEHard : PSPACEHard TQBF := by
  sorry

/-- **The Stockmeyer-Meyer theorem**: `TQBF` is `PSPACE`-complete.
[AB09, Theorem 4.13]

**Proof sketch.** `Complexity.TQBF_mem_PSPACE` with
`Complexity.TQBF_PSPACEHard`. -/
theorem TQBF_PSPACEComplete : PSPACEComplete TQBF := by
  sorry

end Complexity
