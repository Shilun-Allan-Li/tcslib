/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleNondeterministic
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.TuringMachine.Build.OracleCall

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle complexity classes: `Pᴼ` and `NPᴼ`

[AB09, Definition 3.5]: for a language `O`, `Pᴼ` is the class of languages
decided by polynomial-time deterministic oracle machines with oracle `O`, and
`NPᴼ` the class decided by polynomial-time nondeterministic oracle machines with
oracle `O`. Both are rendered in the campaign's exact class normal forms —
`DTIMEOracle`/`NTIMEOracle` with the `c · T n` constant absorption and the
`⋃ c, (n ^ c + 1)` polynomial union — so that every lemma about `DTIME`/`NTIME`
has a mechanical oracle counterpart.

## Design

* **`NPᴼ` is machine-first.** Unrelativized `NP` is verifier-first and
  `NP = ⋃ c, NTIME (fun n => n ^ c + 1)` is Theorem 2.6 (the `+ 1` is load-bearing
  under the exact-budget conventions — P3.1 round 1, finding 1); but
  [AB09, Definition 3.5] *defines*
  `NPᴼ` directly by nondeterministic oracle machines, so here the `NTIMEOracle`
  union **is** the definition and no certificate form is claimed (a relativized
  certificate characterization would need oracle-aware verifiers and is not in
  the campaign's scope).
* **Clocks are relative to the given oracle.** `DecidesInTime` is stated at the
  oracle `O` being used, so a machine's time bound is a promise about its runs
  with *that* oracle only. [BGS75] instead clocks its enumerated machines under
  *every* oracle; that stronger, enumeration-friendly reading is a property of
  the *stage construction* of [AB09, Theorem 3.7] and is introduced there
  (phase P3.2), not baked into the classes. (Seeded to the P3.1 audit.)
* **The workhorse lemma** is `Complexity.mem_POracle_of_polyTimeReducible`:
  `L ≤ₚ O → L ∈ Pᴼ` — write the reduction's output on the query tape, query
  once, copy the answer out. Example 3.6(1), `NP ⊆ P^SAT`, and the easy halves
  of [AB09, Theorem 3.7] are all instances or corollaries.

## Main definitions

* `Complexity.DTIMEOracle`, `Complexity.NTIMEOracle` — timed oracle classes with
  constant absorption. [AB09, §3.4]
* `Complexity.POracle`, `Complexity.NPOracle` — `Pᴼ` and `NPᴼ`.
  [AB09, Definition 3.5]

## Main results (five proved; `POracle_eq_P_of_mem_P` remains sorried, deferred)

* `Complexity.P_subset_POracle` — an oracle can only help: `P ⊆ Pᴼ`.
  [AB09, Example 3.6(2), first half]
* `Complexity.POracle_subset_NPOracle` — determinism is a special case of
  nondeterminism, relative to any oracle. [AB09, §3.4]
* `Complexity.mem_POracle_of_polyTimeReducible` — `L ≤ₚ O → L ∈ Pᴼ`.
* `Complexity.oracle_mem_POracle` — `O ∈ Pᴼ`.
* `Complexity.compl_mem_POracle` — `Pᴼ` is closed under complement.
* `Complexity.POracle_eq_P_of_mem_P` — a polynomial-time oracle is redundant:
  `O ∈ P → Pᴼ = P`. [AB09, Example 3.6(2)]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Definition 3.5, Example 3.6.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (The oracle-machine classes,
  pp. 431-433; the all-oracle clock convention noted above.)
-/

namespace Complexity

open Turing

/-- The class of languages decided, with oracle `O`, in time `c · T` for some
constant `c` by a finite well-formed deterministic oracle machine — the oracle
counterpart of `Complexity.DTIME`. [AB09, §3.4] -/
def DTIMEOracle (O : Language Bool) (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinOracleTM Bool), M.DecidesInTime O L fun n => c * T n}

/-- The class of languages decided, with oracle `O`, in nondeterministic time
`c · T` for some constant `c` by a finite well-formed nondeterministic oracle
machine — the oracle counterpart of `Complexity.NTIME`. [AB09, §3.4] -/
def NTIMEOracle (O : Language Bool) (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinOracleNDTM Bool), N.DecidesInTime O L fun n => c * T n}

/-- `Pᴼ`: the languages decidable in deterministic polynomial time with oracle
access to `O`, in the campaign's polynomial normal form `⋃ c, DTIMEOracle O (n^c + 1)`
mirroring `Complexity.P`. [AB09, Definition 3.5] -/
def POracle (O : Language Bool) : Set (Language Bool) :=
  ⋃ c : ℕ, DTIMEOracle O fun n => n ^ c + 1

/-- `NPᴼ`: the languages decidable in nondeterministic polynomial time with
oracle access to `O`. Machine-first, directly following [AB09, Definition 3.5]
(see the module docstring: no certificate form is claimed relative to an
oracle). -/
def NPOracle (O : Language Bool) : Set (Language Bool) :=
  ⋃ c : ℕ, NTIMEOracle O fun n => n ^ c + 1

/-- **An oracle can only help**: every language decidable in polynomial time is
decidable in polynomial time with any oracle, `P ⊆ Pᴼ`.
[AB09, Example 3.6(2), the trivial inclusion]

**Proof sketch.** A `P`-witness `M` embeds as the oracle machine
`Turing.FinTM.toFinOracleTM M`, which never queries;
`Turing.FinTM.toFinOracleTM_computesInTime` transfers `DecidesInTime` verbatim
(same `c`, same exponent) under every oracle `O`. -/
theorem P_subset_POracle (O : Language Bool) : P ⊆ POracle O := by
  intro L hL
  obtain ⟨e, c, M, hM⟩ := Set.mem_iUnion.mp hL
  exact Set.mem_iUnion.mpr ⟨e, c, M.toFinOracleTM,
    fun x => (FinTM.toFinOracleTM_computesInTime M O _ _ _).mpr (hM x)⟩

/-- **Determinism is a special case of nondeterminism, relative to any oracle**:
`Pᴼ ⊆ NPᴼ`. [AB09, §3.4]

**Proof sketch.** A `Pᴼ`-witness `M` embeds as
`Turing.FinOracleTM.toFinOracleNDTM M`, whose two transition functions coincide.
By `Turing.OracleTM.toOracleNDTM_runWith` every choice word of length `t`
reproduces `M.tm.runFrom O · t`, so all-branch halting at the budget follows
from `M`'s halting, and some branch accepts iff `M`'s (unique) run outputs
`[true]`, i.e. iff `x ∈ L` by the indicator equation — mirroring
`Complexity.DTIME_subset_NTIME`'s proof over `Turing.MultiTapeTM.toNDTM_runWith`. -/
theorem POracle_subset_NPOracle (O : Language Bool) : POracle O ⊆ NPOracle O := by
  classical
  intro L hL
  obtain ⟨e, c, M, hM⟩ := Set.mem_iUnion.mp hL
  refine Set.mem_iUnion.mpr ⟨e, c, M.toFinOracleNDTM, ?_⟩
  intro x
  obtain ⟨hhalt, hout⟩ := hM x
  have branch (w : List Bool) (hw : w.length = c * (x.length ^ e + 1)) :
      M.toFinOracleNDTM.tm.runWith O w (M.toFinOracleNDTM.tm.initCfg x) =
        M.tm.runFrom O (M.tm.initCfg x) (c * (x.length ^ e + 1)) := by
    have same := M.tm.toOracleNDTM_runWith O w (M.tm.initCfg x)
    rw [hw] at same
    exact same
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [branch w hw]
    exact hhalt
  · constructor
    · intro hx
      refine ⟨List.replicate (c * (x.length ^ e + 1)) false, List.length_replicate .., ?_, ?_⟩
      · rw [branch _ (List.length_replicate ..)]
        exact hhalt
      · rw [branch _ (List.length_replicate ..), hout]
        simp only [MultiTapeTM.indicator, if_pos hx]
    · rintro ⟨w, hw, _, accepts⟩
      rw [branch w hw, hout] at accepts
      by_contra hx
      simp only [MultiTapeTM.indicator, if_neg hx] at accepts
      cases accepts

/-- The one-query machine for `Complexity.mem_POracle_of_polyTimeReducible`: the
reduction machine `F` under the W1 capture onto the query tape (`Turing.captureAction`,
with its halting transition sent to `qQuery`), followed by the answer tail
(`Turing.OracleTM.answerAction`). The three fresh states `Sum.inr 0/1/2` are `qQuery`,
`qYes`, `qNo`; the `qQuery` row is dead (the query step overrides it). Built from the
library rows of `TCSlib.Complexity.TuringMachine.Build.OracleCall`; no hand-built table. -/
private def queryTM (F : FinTM Bool) : FinOracleTM Bool where
  k := F.k
  State := F.State ⊕ Fin 3
  tm :=
    { q₀ := .inl F.tm.q₀
      qQuery := .inr 0
      qYes := .inr 1
      qNo := .inr 2
      tr := fun q inp w => match q with
        | .inl s => captureAction Sum.inl (Sum.inr 0) (F.tm.tr s inp fun i => w i.castSucc)
        | .inr j => if j = 1 then OracleTM.answerAction true
            else if j = 2 then OracleTM.answerAction false
            else ⟨0, fun _ => (none, 0), none, none⟩ }
  wf := ⟨by simp, by simp, by simp⟩

/-- `queryTM`'s `qYes` row emits `true` and halts. -/
private theorem queryTM_yes (F : FinTM Bool) (inp : Option Bool)
    (w : Fin (F.k + 1) → Option Bool) :
    (queryTM F).tm.tr (queryTM F).tm.qYes inp w = OracleTM.answerAction true := rfl

/-- `queryTM`'s `qNo` row emits `false` and halts. -/
private theorem queryTM_no (F : FinTM Bool) (inp : Option Bool)
    (w : Fin (F.k + 1) → Option Bool) :
    (queryTM F).tm.tr (queryTM F).tm.qNo inp w = OracleTM.answerAction false := rfl

/-- On the embedded source states `queryTM` is the W1-transformed source table. -/
private theorem queryTM_agree (F : FinTM Bool) (s : F.State) (inp : Option Bool)
    (w : Fin (F.k + 1) → Option Bool) :
    (queryTM F).tm.tr (Sum.inl s) inp w =
      captureAction Sum.inl (queryTM F).tm.qQuery (F.tm.tr s inp fun i => w i.castSucc) :=
  rfl

set_option linter.unusedSimpArgs false in
/-- `queryTM` starts at the capture image of the source's initial configuration, with an
empty capture prefix and empty physical output. -/
private theorem queryTM_init (F : FinTM Bool) (x : List Bool) :
    (queryTM F).tm.initCfg x =
      captureCfg Sum.inl (queryTM F).tm.qQuery [] [] (F.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : (i : ℕ) < F.k <;> simp [captureCfg, hi, queryTM]
  · funext i
    by_cases hi : (i : ℕ) < F.k <;> simp [captureCfg, hi, queryTM]

/-- **The workhorse of the light oracle results**: if `L` Karp-reduces to the
oracle in polynomial time, then `L ∈ Pᴼ` — compute the reduction onto the query
tape, query once, and emit the answer.

**Proof sketch.** Let `f` with machine `F` (time `C·(n+1)^c`) witness `L ≤ₚ O`.
Fill obligations, named for the brief: (i) a capture-style retarget of `F` that
writes its emissions to the **query tape** of the host oracle machine instead of
the physical output — `Turing.captureTM`'s core variant (W1) retargeted to a
designated work tape, run inside the oracle architecture via
`Turing.OracleTM.ofMultiTapeTM`-style state adjunction; (ii) a four-state
query-and-answer tail: enter `qQuery` at `F`'s return seam, then from `qYes`
emit `[true]` and halt, from `qNo` emit `[false]` and halt; (iii) the seam
composition of (i) and (ii) with additive budgets (the `machine-library-design.md`
§12 R2 shape; until the routine layer lands, the glue is the dispatch idiom of
`Turing.bufferedCompTM`). Total time `O(C·(n+1)^c)`; correctness is
`x ∈ L ↔ f x ∈ O` against the single query `f x` — the query string read back is
exactly `f x` by the capture contract and `Turing.OracleTM.queryString`'s
extraction.

**B1 appendix.** Fill obligations (i) and (iii) are one table: W1's capture writes on the
last work tape, which is the query tape, and its return state is taken to be `qQuery`
(`Turing.OracleTM.capture_reaches_qQuery`); no seam composition is needed. -/
theorem mem_POracle_of_polyTimeReducible {L O : Language Bool} (h : L ≤ₚ O) :
    L ∈ POracle O := by
  classical
  obtain ⟨f, ⟨F, C, c, hF⟩, hL⟩ := h
  refine Set.mem_iUnion.mpr ⟨c, (C + 2) * 2 ^ c, queryTM F, fun x => ?_⟩
  obtain ⟨hh, ho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp (hF x)
  dsimp only at hh ho
  -- (i) The captured reduction reaches `qQuery` by its own halting time.
  obtain ⟨u, hu, hrun⟩ := OracleTM.capture_reaches_qQuery F.tm (queryTM F).tm O Sum.inl
    (fun s => Sum.inl_ne_inr) (queryTM_agree F) [] [] (F.tm.initCfg x) _ hh
  set cQ := captureCfg Sum.inl (queryTM F).tm.qQuery [] []
    (F.tm.runFrom (F.tm.initCfg x) (C * (x.length + 1) ^ c)) with hcQ
  have hstate : cQ.state = some (queryTM F).tm.qQuery := by
    simp only [cQ, captureCfg, hh, Option.map_none, Option.getD_none]
  -- The submitted query is exactly `f x`, the empty word included.
  have hquery : OracleTM.queryString cQ = f x := by
    apply OracleTM.queryString_bufferTape
    simp only [cQ, captureCfg, OracleTM.queryTapeIdx, Fin.val_last, lt_irrefl, dite_false,
      List.nil_append, ho]
  have hout0 : cQ.output = [] := rfl
  -- (ii) The answer tail: two more steps.
  have htail := OracleTM.runFrom_two_of_qQuery (queryTM F).tm (queryTM F).wf
    (queryTM_yes F) (queryTM_no F) O hstate
  have hfin : (queryTM F).tm.runFrom O ((queryTM F).tm.initCfg x) (u + 2) =
      { cQ with
        state := none
        output := cQ.output ++ [if OracleTM.queryString cQ ∈ O then true else false] } := by
    rw [OracleTM.runFrom_add, queryTM_init, hrun, htail]
  have hdone : (queryTM F).ComputesInTime O x
      [MultiTapeTM.indicator (L : Set (List Bool)) x] (u + 2) := by
    refine ⟨by rw [hfin], ?_⟩
    rw [hfin]
    show cQ.output ++ [if OracleTM.queryString cQ ∈ O then true else false] = _
    rw [hout0, hquery, List.nil_append]
    by_cases hx : x ∈ L
    · simp [MultiTapeTM.indicator, hx, (hL x).mp hx]
    · have : f x ∉ O := fun h' => hx ((hL x).mpr h')
      simp [MultiTapeTM.indicator, hx, this]
  -- (iii) The budget: `u + 2 ≤ (C + 2)(n + 1)^c ≤ (C + 2) 2^c (n^c + 1)`.
  refine hdone.mono ?_
  have hp : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc u + 2 ≤ C * (x.length + 1) ^ c + 2 * (x.length + 1) ^ c := by omega
    _ = (C + 2) * (x.length + 1) ^ c := by ring
    _ ≤ (C + 2) * (2 ^ c * (x.length ^ c + 1)) := Nat.mul_le_mul_left _ (succ_pow_le _ _)
    _ = (C + 2) * 2 ^ c * (x.length ^ c + 1) := by ring

/-- The oracle itself is decidable with one query: `O ∈ Pᴼ`.

**Proof sketch.** `Complexity.mem_POracle_of_polyTimeReducible` at the identity
reduction `Complexity.PolyTimeReducible.refl`. -/
theorem oracle_mem_POracle (O : Language Bool) : O ∈ POracle O := by
  exact mem_POracle_of_polyTimeReducible (PolyTimeReducible.refl O)

/-- The emission-negating transformer for `Complexity.compl_mem_POracle` (the P3.1 audit's
direct construction): every emitted Boolean is negated; states, special states, and all
tape and head actions are unchanged. A table transformer with a single consumer; the
library has no oracle output-relabelling row. -/
private def negOut (M : FinOracleTM Bool) : FinOracleTM Bool where
  k := M.k
  State := M.State
  tm :=
    { q₀ := M.tm.q₀
      qQuery := M.tm.qQuery
      qYes := M.tm.qYes
      qNo := M.tm.qNo
      tr := fun q inp w => { M.tm.tr q inp w with output := (M.tm.tr q inp w).output.map not } }
  wf := ⟨M.wf.qQuery_ne_qYes, M.wf.qQuery_ne_qNo, M.wf.qYes_ne_qNo⟩

/-- A configuration with its output negated. -/
private def negCfg {k : ℕ} {S : Type} {x : List Bool} (c : Cfg (k + 1) Bool S x) :
    Cfg (k + 1) Bool S x := { c with output := c.output.map not }

/-- One step of the negating machine is the negation of one step of the original.

**Proof sketch.** Halted configurations are fixed. At `qQuery` both machines read the same
query (tapes are untouched by the negation) and move to the same answer state. Elsewhere
both apply the same action up to its emission, and negation commutes with appending. -/
private theorem negOut_step (M : FinOracleTM Bool) (O : Language Bool) {x : List Bool}
    (c : Cfg (M.k + 1) Bool M.State x) :
    (negOut M).tm.step O (negCfg c) = negCfg (M.tm.step O c) := by
  classical
  unfold OracleTM.step
  cases hs : c.state with
  | none => simp [negCfg, hs]
  | some q =>
    have hs' : (negCfg c).state = some q := hs
    rw [hs']
    dsimp only
    by_cases hq : q = M.tm.qQuery
    · have hq' : q = (negOut M).tm.qQuery := hq
      rw [if_pos hq', if_pos hq]
      rfl
    · have hq' : q ≠ (negOut M).tm.qQuery := hq
      rw [if_neg hq', if_neg hq]
      have hin : (negCfg c).inputSymbol = c.inputSymbol := rfl
      have hw : (negCfg c).workTapeSymbols = c.workTapeSymbols := rfl
      rw [hin, hw]
      refine Cfg.ext rfl rfl rfl rfl ?_
      show List.map not c.output ++
          ((M.tm.tr q c.inputSymbol c.workTapeSymbols).output.map not).toList =
        List.map not (c.output ++ (M.tm.tr q c.inputSymbol c.workTapeSymbols).output.toList)
      cases (M.tm.tr q c.inputSymbol c.workTapeSymbols).output <;> simp

/-- Runs of the negating machine are the negated runs of the original. -/
private theorem negOut_runFrom (M : FinOracleTM Bool) (O : Language Bool) {x : List Bool}
    (c : Cfg (M.k + 1) Bool M.State x) (t : ℕ) :
    (negOut M).tm.runFrom O (negCfg c) t = negCfg (M.tm.runFrom O c t) :=
  OracleTM.runFrom_comm_of_step negCfg (negOut_step M O) c t

/-- **`Pᴼ` is closed under complement**: flip the final answer.

**Proof sketch.** Given a `Pᴼ`-witness `M` for `L`, compose with the one-bit
negation at the output: a wrapper that runs `M` with output captured (W1) and
emits the flipped indicator bit — the oracle-architecture analogue of the
negation closure in `Complexity.compl_mem_P`'s proof. Same budget shape,
constant overhead.

**B1 appendix.** The fill takes the P3.1 audit's simpler route, recorded in its
resolutions: negate every emission directly, at the same budget, with no capture wrapper. -/
theorem compl_mem_POracle {L O : Language Bool} (h : L ∈ POracle O) :
    Lᶜ ∈ POracle O := by
  classical
  obtain ⟨e, c, M, hM⟩ := Set.mem_iUnion.mp h
  refine Set.mem_iUnion.mpr ⟨e, c, negOut M, fun x => ?_⟩
  obtain ⟨hh, ho⟩ := hM x
  have hinit : (negOut M).tm.initCfg x = negCfg (M.tm.initCfg x) := rfl
  refine ⟨?_, ?_⟩
  · show ((negOut M).tm.runFrom O ((negOut M).tm.initCfg x) _).state = none
    rw [hinit, negOut_runFrom]; exact hh
  · show ((negOut M).tm.runFrom O ((negOut M).tm.initCfg x) _).output = _
    rw [hinit, negOut_runFrom]
    show (M.tm.runFrom O (M.tm.initCfg x) _).output.map not = _
    rw [ho]
    by_cases hx : x ∈ L
    · have : x ∉ (Lᶜ : Language Bool) := fun h' => h' hx
      simp [MultiTapeTM.indicator, hx, this]
    · have : x ∈ (Lᶜ : Language Bool) := hx
      simp [MultiTapeTM.indicator, hx, this]

/-- **A polynomial-time oracle is redundant**: `O ∈ P → Pᴼ = P`.
[AB09, Example 3.6(2)]

**Proof sketch.** `⊇` is `Complexity.P_subset_POracle`. For `⊆`, let `M` decide
`L` with oracle `O` in time `c·(n^k + 1)`, and let `D` decide `O` in time
`d·(n^e + 1)`. Fill obligations, named for the brief: build a plain machine
simulating `M` step by step, where each `qQuery` step is replaced by running `D`
on the current query string. (i) At each query the host copies the query
tape's **extracted prefix only** — cell `0` up to the first blank — onto a
clean virtual-input region, blanks beyond it (garbage past the first blank or
at negative cells must not reach `D`: the round-1 audit's cell-`1` instance),
runs `D` there with output captured (W1) so the host stays silent, clears
`D`'s scratch, restores the suspended heads, and resumes in the answer state;
(ii) **the ledger, explicitly** (round-1 audit, finding 2): with oracle-time
budget `t = c·(n^k + 1)` there are at most `t` queries, each of length at most
`t` (`Turing.OracleTM.queryString_length_le`); positioning, prefix copy and
restoration cost `O(t + 1)` per query and `D`'s run plus cleanup
`O(d·((t+1)^e + 1))`, so the total is
`O(t + t·(t + 1 + d·((t+1)^e + 1))) = O((t+1)^(1+max 1 e)) =
O((n+1)^(k·(1+max 1 e)))` — the exponent depends on `k` and `e` jointly,
not `k·e + O(1)`; (iii) non-query steps are lockstep
(`Turing.OracleTM.step_eq_of_ne_qQuery`), and the preservation/reset
invariants (suspended tapes untouched, scratch cleared, fixed windows) are
named fill obligations. The composite bound sits inside `P`'s `⋃ c` by the
absorption `(n+1)^c ≤ 2^c·(n^c + 1)`. -/
theorem POracle_eq_P_of_mem_P {O : Language Bool} (h : O ∈ P) : POracle O = P := by
  sorry

end Complexity
