/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Build.OracleCall
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.InputCall

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: oracle-call simulation (W2, the B1b extension)

The oracle-call hosting layer of the machine-construction library
(`machine-library-design.md` §12.10): a **plain** machine simulating an oracle machine
[AB09, Definition 3.4] whose oracle is decided by a plain machine, each query answered by
running the decider on the extracted query word. It is the library gap behind
[AB09, Example 3.6(2)] (`Complexity.POracle_eq_P_of_mem_P`: a polynomial-time oracle is
redundant) and behind the last inclusion of [AB09, Example 3.6(3)]
(`Complexity.NPOracle_EXPCOM_subset_EXP`: enumerate the choice words of a polynomial-time
oracle NDTM and answer its `EXPCOM` queries by an exponential-time decider). There is
**one** simulation trace, the deterministic row below; the nondeterministic consumer
reduces to it through choice-word enumeration, never through a second, branchwise
simulation.

## Design

* **One trace, stated at the I/O level from preloaded starts.** The headline
  `Turing.FinOracleTM.exists_plain_simulation` starts the oracle machine from
  `Turing.Cfg.ofWords` with arbitrary words on its ordinary tapes and a blank query tape,
  and the plain host from the same words on its first tapes (`Turing.FinTM.prefixWords`).
  The initial configuration is the all-empty instance
  (`Turing.FinOracleTM.exists_plain_simulation_initCfg`, the draft headline of
  `audits/b1-integration.md`, verbatim). The preloaded generality is what lets the
  choice-word route hand the host a certificate on a work tape.
* **The time bound is exact per query.** The host pays `a·(t + 1)²` for `t` simulated
  steps (one host step per non-query step; at most `t` queries, each of length and head
  displacement at most `t`, each paying `a·(t + 1)` for positioning, extraction and
  restoration) plus `a·τ |z|` for every query `z` actually submitted. No monotonicity of
  `τ` is assumed; the uniform corollary
  `Turing.FinOracleTM.exists_plain_simulation_of_monotone` bounds the sum by `t·τ t`
  under monotone `τ`, and that one form gives both the polynomial instantiation (`τ`
  polynomial: `P^O = P`) and the exponential one (`τ = A·2^(B(m+1))`: `P^EXPCOM ⊆ EXP`, and
  through the choice-word route `NP^EXPCOM ⊆ EXP`).
* **The clean call at a frozen native input is derived, not new.** The decider runs as the
  install-mode clean call `Turing.FinTM.exists_installCallTM` hosted by Z1 at the empty
  virtual input (`Turing.vhostEmitTM` with `y = []`, the F2A `f2_splitCount` pattern), so
  the oracle machine's input head is never rewound.
* **Nondeterminism through choice words.** `Turing.FinOracleNDTM.exists_choiceTM` turns an
  oracle NDTM into a deterministic oracle machine reading its choice word from a work tape
  (a lockstep table transform; queries pass through the host's own query state).
  `Turing.FinTM.exists_certificateShell` (in `TCSlib.Complexity.TuringMachine.Build.CertShell`)
  is the plain certificate shell (split, load,
  Z1-host, verdict), feeding `Complexity.exists_proj_decider`; its loader is the §12.8
  native-input clean call, so its fill follows the §12.8 fill. The summit composes
  choice machine, simulation, shell and enumeration; no oracle-call simulation is repeated.

## Main definitions

* `Turing.FinTM.prefixWords` — words on the first tapes of a wider layout.
* `Turing.FinOracleNDTM.choiceOut` — the observable outcome of an oracle NDTM along a fixed
  choice word: its output if halted, the output followed by `false` otherwise.

## Main results

* `Turing.OracleTM.queryString_runFrom_length_le_of_blank` — from a blank query tape with
  its head at the origin, the query after `s` steps has length at most `s`.
* `Turing.FinOracleTM.exists_plain_simulation` — the headline (statement).
* `Turing.FinOracleTM.exists_plain_simulation_of_monotone`,
  `Turing.FinOracleTM.exists_plain_simulation_initCfg`,
  `Turing.FinOracleTM.exists_plain_decider` — the uniform corollaries.
* `Turing.FinOracleNDTM.choiceOut_eq_true_iff`, `Turing.FinOracleNDTM.mem_iff_exists_choiceOut`
  — acceptance along exact-length choice words.
* `Turing.FinOracleNDTM.exists_choiceTM` — the choice-word machine (statement).

The plain certificate shell `Turing.FinTM.exists_certificateShell` and its projection identity
`Turing.FinTM.certificateShell_proj` live in `TCSlib.Complexity.TuringMachine.Build.CertShell`.

## Status

Statements for the W2 gate. The three corollaries, the query-length lemma, the two
choice-word lemmas and the word-placement facts are proved; the two rows
`exists_plain_simulation` and `exists_choiceTM` are sorried with construction sketches,
pending the W2 fill (the shell's row is in `Build/CertShell`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Definition 3.4, Example 3.6(2)-(3); Claim 2.4
  and Theorem 2.6, the enumeration and choice-word arguments relativized.)
-/

namespace Turing

/-! ### Word placement -/

/-- The words `w` of a `k`-tape layout placed on the first `k` tapes of a `k'`-tape layout,
every further tape empty: the start words of a host whose first tapes carry a hosted
machine's tapes. -/
def FinTM.prefixWords {k : ℕ} (k' : ℕ) (w : Fin k → List Bool) : Fin k' → List Bool :=
  fun j => if h : (j : ℕ) < k then w ⟨j, h⟩ else []

/-- Placing all-empty words gives all-empty words. -/
@[simp]
theorem FinTM.prefixWords_nil {k : ℕ} (k' : ℕ) :
    FinTM.prefixWords k' (fun _ : Fin k => ([] : List Bool)) = fun _ => [] := by
  funext j
  simp only [FinTM.prefixWords]
  split <;> rfl

/-- Placing one word on tape `i` puts it on host tape `i`, every other host tape empty. -/
theorem FinTM.prefixWords_update {k k' : ℕ} (i : Fin k) (u : List Bool) (hk : k ≤ k') :
    FinTM.prefixWords k' (Function.update (fun _ : Fin k => ([] : List Bool)) i u) =
      Function.update (fun _ => []) ⟨i, lt_of_lt_of_le i.isLt hk⟩ u := by
  funext j
  simp only [FinTM.prefixWords]
  by_cases h : (j : ℕ) < k
  · rw [dif_pos h]
    by_cases hj : (j : ℕ) = i
    · have e1 : (⟨j, h⟩ : Fin k) = i := Fin.ext hj
      have e2 : j = ⟨i, lt_of_lt_of_le i.isLt hk⟩ := Fin.ext hj
      rw [e1, e2, Function.update_self, Function.update_self]
    · have e1 : (⟨j, h⟩ : Fin k) ≠ i := fun he => hj (congrArg Fin.val he)
      have e2 : j ≠ ⟨i, lt_of_lt_of_le i.isLt hk⟩ := fun he => hj (congrArg Fin.val he)
      rw [Function.update_of_ne e1, Function.update_of_ne e2]
  · rw [dif_neg h]
    have e2 : j ≠ ⟨i, lt_of_lt_of_le i.isLt hk⟩ := fun he => h (he ▸ i.isLt)
    rw [Function.update_of_ne e2]

/-- An initial configuration is the seam configuration at the start state with every tape
word empty, at any tape count and state type — in particular at an oracle machine's
`k + 1` tapes.

**Proof sketch.** `Turing.initCfg_ofWords` at any machine whose start state is `q`. -/
theorem Cfg.init_eq_ofWords {k : ℕ} {State : Type*} (q : State) (x : List Bool) :
    (Cfg.init q x : Cfg k Bool State x) = Cfg.ofWords q (fun _ => []) :=
  initCfg_ofWords (⟨q, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ :
    MultiTapeTM k Bool State) x

/-! ### The query-length bound from preloaded starts -/

/-- **Queries stay short from a blank query tape**: if the query tape of `c` is blank with
its head at the origin, the query after `s` steps of any oracle run from `c` has length at
most `s`, whatever the other tapes hold. The initialized bound
`Turing.OracleTM.queryString_length_le` is the instance `c = M.initCfg x`. [AB09, §3.4]

**Proof sketch.** Induction on `s` for the query tape alone: its head stays within `s` of
the origin (`Turing.OracleTM.workTapePos_step_le`) and every query cell at distance at least
`s` is still blank, since a step writes only under the old head
(`Turing.OracleTM.workTapes_step_eq_of_ne`). Cell `s` is therefore blank, and
`Turing.OracleTM.queryString_length_le_of_blank` bounds the query. -/
theorem OracleTM.queryString_runFrom_length_le_of_blank {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (M : OracleTM k Symbol State) (O : Language Symbol)
    (c : Cfg (k + 1) Symbol State input)
    (hblank : ∀ z, c.workTapes (OracleTM.queryTapeIdx k) z = none)
    (hpos : c.workTapePos (OracleTM.queryTapeIdx k) = 0) (s : ℕ) :
    (OracleTM.queryString (M.runFrom O c s)).length ≤ s := by
  have inv : ∀ s : ℕ,
      |(M.runFrom O c s).workTapePos (OracleTM.queryTapeIdx k)| ≤ (s : ℤ) ∧
        ∀ z : ℤ, (s : ℤ) ≤ |z| →
          (M.runFrom O c s).workTapes (OracleTM.queryTapeIdx k) z = none := by
    intro s
    induction s with
    | zero =>
      refine ⟨?_, fun z _ => hblank z⟩
      show |c.workTapePos (OracleTM.queryTapeIdx k)| ≤ ((0 : ℕ) : ℤ)
      rw [hpos]
      simp
    | succ s ih =>
      obtain ⟨hp, hb⟩ := ih
      rw [OracleTM.runFrom_succ_eq_step']
      refine ⟨?_, fun z hz => ?_⟩
      · have h1 := M.workTapePos_step_le O (M.runFrom O c s) (OracleTM.queryTapeIdx k)
        rw [abs_le] at h1 hp ⊢
        push_cast
        omega
      · have hz' : ((s : ℤ) + 1) ≤ |z| := by exact_mod_cast hz
        have hne : z ≠ (M.runFrom O c s).workTapePos (OracleTM.queryTapeIdx k) := by
          intro he
          rw [← he] at hp
          have := le_trans hz' hp
          omega
        rw [M.workTapes_step_eq_of_ne O _ hne]
        exact hb z (by omega)
  exact OracleTM.queryString_length_le_of_blank _ s ((inv s).2 _ (le_abs_self _))

/-! ### The oracle-call simulation -/

/-- **The oracle-call simulation** (W2 headline; [AB09, Example 3.6(2)], the simulation
behind `Pᴼ = P` for `O ∈ P`, and the per-branch engine of [AB09, Example 3.6(3)]). Let the
plain machine `D` decide the oracle `O` within `τ`. There are a plain machine `P`, with at
least the oracle machine's `M.k + 1` tapes, and a constant `a` such that: whenever `M`,
started from `Cfg.ofWords` with words `w` on its ordinary tapes and a **blank query
tape**, halts with oracle `O` by time `t`, then `P`, started from the same words on its
first tapes (`Turing.FinTM.prefixWords`, every further tape blank), halts with the **same
output** by time
`a·(t + 1)² + a·Σ_{r < t, M in qQuery at r} τ |queryString at r|`
— one `τ` term for every query actually submitted before `t`, at its own length.

**Proof sketch.** The dispatch host (`machine-library-design.md` §12.10, row W2-S). Tapes:
`M`'s `k + 1` tapes first; a shadow tape whose head mirrors the query head, with an origin
marker written on the first step; the bank of the install-mode clean call
`C := Turing.FinTM.exists_installCallTM D (fun z => [χ_O z]) τ hD`, hosted by Z1 at the
**empty** virtual input (`Turing.vhostEmitTM_runFrom` with `y = []`: the native input
head stays frozen) and relocated by R1; a scratch tape carrying the saved cell `-1` and the
side bit across the seams. Control: `M`'s state with the side of the query
head on simulated steps (the side of the origin it is on, updated whenever the shadow head
reads the marker), dispatch phases otherwise.
(i) Off `qQuery` one host step per source step: the host table agrees, on simulated states,
with the shadowed transport of the plain table `M.tm.plainEmptyOracle`, so the bridge
`Turing.OracleTM.runFrom_eq_plainEmptyOracle` and the agreement transfer
`Turing.MultiTapeTM.runFrom_eq_of_agreeOn` carry `M`'s run.
(ii) At `qQuery`, R2-seamed phases (`Turing.seamCompTM_run_ofCfg`, `Turing.seamReleaseTM`):
bookmark the shadow cell; walk to the origin by the side; save cell `-1` on the scratch
tape and blank it; copy the delimited query (blank at `-1` and at the first blank `|z|`;
`Turing.OracleTM.queryString_eq_of_cells`) to `C`'s argument tape by
`Turing.copyTM_run_ofCfg`; run `C`, which installs `[χ_O z]` within
`c·(τ |z| + |z| + 2)` with its scratch restored; read and clear the verdict cell; restore
cell `-1`; walk back to the bookmark and erase it; enter the embedded `M.qYes` or `M.qNo`,
which is `M`'s next configuration by `Turing.OracleTM.step_of_qQuery`.
(iii) Ledger: from a blank query tape the query at step `r` has length at most `r`
(`Turing.OracleTM.queryString_runFrom_length_le_of_blank`) and the query head is within
`r` of the origin, so each query costs `a·(t + 1) + a·τ |z|`; there are at most `t` of
them. The host halts exactly when `M` does: `M`'s emissions are forwarded, the clean call
emits nothing, the dispatch is silent. First-halt cuts by
`Turing.MultiTapeTM.exists_first_halt`. -/
theorem FinOracleTM.exists_plain_simulation (M : FinOracleTM Bool) (D : FinTM Bool)
    (O : Language Bool) (τ : ℕ → ℕ) (hD : D.DecidesInTime O τ) :
    ∃ (P : FinTM Bool) (a : ℕ), M.k + 1 ≤ P.k ∧
      ∀ (x : List Bool) (w : Fin (M.k + 1) → List Bool), w (Fin.last M.k) = [] →
      ∀ t : ℕ, (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀ w) t).state = none →
        ∃ s ≤ a * (t + 1) ^ 2 + a * ∑ r ∈ Finset.range t,
            (if (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀ w) r).state =
                some M.tm.qQuery then
              τ (OracleTM.queryString
                (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀ w) r)).length
            else 0),
          (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (FinTM.prefixWords P.k w)) s).state =
              none ∧
            (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (FinTM.prefixWords P.k w)) s).output =
              (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀ w) t).output := by
  sorry

/-- **The oracle-call simulation, uniform form**: under a monotone decider budget `τ`, the
per-query sum of `Turing.FinOracleTM.exists_plain_simulation` is at most `t·τ t`, so the
host halts with `M`'s output within `a·(t + 1)·(t + 1 + τ t)`. This is the form both
consumers instantiate: polynomial `τ` for [AB09, Example 3.6(2)], `τ = A·2^(B(m+1))` for
[AB09, Example 3.6(3)].

**Proof sketch.** Every query submitted before `t` has length at most `t`
(`Turing.OracleTM.queryString_runFrom_length_le_of_blank`: the start's query tape is
`bufferTape []`, its head at the origin), so each summand is at most `τ t` by
monotonicity; `t` summands, and `a·(t+1)² + a·t·τ t ≤ a·(t+1)·(t+1+τ t)`. -/
theorem FinOracleTM.exists_plain_simulation_of_monotone (M : FinOracleTM Bool) (D : FinTM Bool)
    (O : Language Bool) (τ : ℕ → ℕ) (hτ : Monotone τ) (hD : D.DecidesInTime O τ) :
    ∃ (P : FinTM Bool) (a : ℕ), M.k + 1 ≤ P.k ∧
      ∀ (x : List Bool) (w : Fin (M.k + 1) → List Bool), w (Fin.last M.k) = [] →
      ∀ t : ℕ, (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀ w) t).state = none →
        ∃ s ≤ a * (t + 1) * (t + 1 + τ t),
          (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (FinTM.prefixWords P.k w)) s).state =
              none ∧
            (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (FinTM.prefixWords P.k w)) s).output =
              (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀ w) t).output := by
  obtain ⟨P, a, hk, hP⟩ := exists_plain_simulation M D O τ hD
  refine ⟨P, a, hk, fun x w hw t ht => ?_⟩
  obtain ⟨s, hs, h1, h2⟩ := hP x w hw t ht
  refine ⟨s, hs.trans ?_, h1, h2⟩
  have hblank : ∀ z, (Cfg.ofWords (input := x) M.tm.q₀ w).workTapes
      (OracleTM.queryTapeIdx M.k) z = none := by
    intro z
    simp [Cfg.ofWords, OracleTM.queryTapeIdx, hw]
  have hterm : ∀ r ∈ Finset.range t,
      (if (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀ w) r).state =
          some M.tm.qQuery then
        τ (OracleTM.queryString
          (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀ w) r)).length
      else 0) ≤ τ t := by
    intro r hr
    split
    · apply hτ
      exact (OracleTM.queryString_runFrom_length_le_of_blank M.tm O _ hblank rfl r).trans
        (Nat.le_of_lt (Finset.mem_range.mp hr))
    · exact Nat.zero_le _
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] at hsum
  have h3 : a * (t * τ t) ≤ a * ((t + 1) * τ t) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_succ t))
  calc a * (t + 1) ^ 2 + a * ∑ r ∈ Finset.range t, _
      ≤ a * (t + 1) ^ 2 + a * (t * τ t) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hsum) _
    _ ≤ a * (t + 1) ^ 2 + a * ((t + 1) * τ t) := Nat.add_le_add_left h3 _
    _ = a * (t + 1) * (t + 1 + τ t) := by ring

/-- **The oracle-call simulation from initial configurations** — the draft headline of
`audits/b1-integration.md` ("Deferred: oracle-call hosting"), verbatim: a computation of
`out` from `x` within `t` steps with oracle `O` becomes a plain computation of `out` from
`x` within `a·(t + 1)·(t + 1 + τ t)`. [AB09, Example 3.6(2)]

**Proof sketch.** The all-empty instance of
`Turing.FinOracleTM.exists_plain_simulation_of_monotone`: both initial configurations are
`Cfg.ofWords` at the start state with empty words (`Turing.Cfg.init_eq_ofWords`,
`Turing.FinTM.prefixWords_nil`), and halting is absorbing up to the budget. -/
theorem FinOracleTM.exists_plain_simulation_initCfg (M : FinOracleTM Bool) (D : FinTM Bool)
    (O : Language Bool) (τ : ℕ → ℕ) (hτ : Monotone τ) (hD : D.DecidesInTime O τ) :
    ∃ (P : FinTM Bool) (a : ℕ), ∀ (x out : List Bool) (t : ℕ),
      M.ComputesInTime O x out t → P.ComputesInTime x out (a * (t + 1) * (t + 1 + τ t)) := by
  obtain ⟨P, a, -, hP⟩ := exists_plain_simulation_of_monotone M D O τ hτ hD
  refine ⟨P, a, fun x out t hM => ?_⟩
  obtain ⟨hh, ho⟩ := hM
  rw [OracleTM.initCfg, Cfg.init_eq_ofWords] at hh ho
  obtain ⟨s, hs, h1, h2⟩ := hP x (fun _ => []) rfl t hh
  rw [FinTM.prefixWords_nil] at h1 h2
  rw [FinTM.computesInTime_iff, MultiTapeTM.initCfg, Cfg.init_eq_ofWords,
    ← Nat.add_sub_of_le hs, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ h1]
  exact ⟨h1, h2.trans ho⟩

/-- **A decidable oracle is simulated by a plain decider** (the class-level corollary):
if `M` decides `L` with oracle `O` within `T`, and `D` decides `O` within a monotone `τ`,
some plain machine decides `L` within `a·(T n + 1)·(T n + 1 + τ (T n))`.
[AB09, Example 3.6(2)-(3)]

**Proof sketch.** `Turing.FinOracleTM.exists_plain_simulation_initCfg` at each input, at
the budget `T |x|`. -/
theorem FinOracleTM.exists_plain_decider {M : FinOracleTM Bool} {D : FinTM Bool}
    {O L : Language Bool} {T τ : ℕ → ℕ} (hτ : Monotone τ)
    (hM : M.DecidesInTime O L T) (hD : D.DecidesInTime O τ) :
    ∃ (P : FinTM Bool) (a : ℕ),
      P.DecidesInTime L fun n => a * (T n + 1) * (T n + 1 + τ (T n)) := by
  obtain ⟨P, a, hP⟩ := exists_plain_simulation_initCfg M D O τ hτ hD
  exact ⟨P, a, fun x => hP x _ _ (hM x)⟩

/-! ### Nondeterminism through choice words -/

/-- The observable outcome of the oracle NDTM `N` with oracle `O` on input `x` along the
choice word `u` (one bit per step, [AB09, §2.1.2] relativized): the output of the branch
if it has halted, and that output followed by `false` otherwise — so the outcome is
`[true]` exactly when the branch has halted accepting
(`Turing.FinOracleNDTM.choiceOut_eq_true_iff`). -/
noncomputable def FinOracleNDTM.choiceOut (N : FinOracleNDTM Bool) (O : Language Bool)
    (x u : List Bool) : List Bool :=
  if (N.tm.runWith O u (N.tm.initCfg x)).state = none then
    (N.tm.runWith O u (N.tm.initCfg x)).output
  else (N.tm.runWith O u (N.tm.initCfg x)).output ++ [false]

/-- The outcome is `[true]` exactly when the branch has halted with output `[true]`.

**Proof sketch.** In the halted case the outcome is the output; otherwise it ends in
`false` and cannot be `[true]`. -/
theorem FinOracleNDTM.choiceOut_eq_true_iff (N : FinOracleNDTM Bool) (O : Language Bool)
    (x u : List Bool) :
    N.choiceOut O x u = [true] ↔
      (N.tm.runWith O u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith O u (N.tm.initCfg x)).output = [true] := by
  unfold choiceOut
  split_ifs with h
  · exact ⟨fun ho => ⟨h, ho⟩, fun ho => ho.2⟩
  · refine ⟨fun ho => ?_, fun ho => absurd ho.1 h⟩
    have := congrArg List.getLast? ho
    simp at this

/-- **Acceptance along exact-length choice words** ([AB09, Theorem 2.6], the certificate
reading of choice words, relativized): if `N` decides `L` with oracle `O` within
`a·(n^c + 1)`, then `x ∈ L` iff some choice word of length exactly `2a·(|x| + 1)^c` has
outcome `[true]`.

**Proof sketch.** `a·(n^c + 1) ≤ 2a·(n + 1)^c`. Forward, pad an accepting branch
(`Turing.FinOracleNDTM.AcceptsWithin.mono`). Backward, the length-`a·(n^c + 1)` prefix of
an accepting word has halted by all-branch halting, so by absorption
(`Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.runWith_of_halt`) it is the whole
run, and it accepts. -/
theorem FinOracleNDTM.mem_iff_exists_choiceOut {N : FinOracleNDTM Bool} {O L : Language Bool}
    {a c : ℕ} (hN : N.DecidesInTime O L fun n => a * (n ^ c + 1)) (x : List Bool) :
    x ∈ L ↔ ∃ u : List Bool, u.length = 2 * a * (x.length + 1) ^ c ∧
      N.choiceOut O x u = [true] := by
  have hle : a * (x.length ^ c + 1) ≤ 2 * a * (x.length + 1) ^ c := by
    have h1 : x.length ^ c ≤ (x.length + 1) ^ c := Nat.pow_le_pow_left (Nat.le_succ _) c
    have h2 : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
    calc a * (x.length ^ c + 1) ≤ a * (2 * (x.length + 1) ^ c) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * a * (x.length + 1) ^ c := by ring
  obtain ⟨hhalt, hacc⟩ := hN x
  constructor
  · intro hx
    obtain ⟨u, hu, h1, h2⟩ := (hacc.mp hx).mono hle
    exact ⟨u, hu, (choiceOut_eq_true_iff N O x u).mpr ⟨h1, h2⟩⟩
  · rintro ⟨u, hu, hout⟩
    obtain ⟨-, h2⟩ := (choiceOut_eq_true_iff N O x u).mp hout
    refine hacc.mpr ⟨u.take (a * (x.length ^ c + 1)), ?_, ?_⟩
    · exact List.length_take_of_le (hu ▸ hle)
    · have hh := hhalt (u.take (a * (x.length ^ c + 1))) (List.length_take_of_le (hu ▸ hle))
      have hrun := OracleNDTM.runWith_append (N := N.tm) O (u.take (a * (x.length ^ c + 1)))
        (u.drop (a * (x.length ^ c + 1))) (N.tm.initCfg x)
      rw [List.take_append_drop, OracleNDTM.runWith_of_halt O _ hh] at hrun
      exact ⟨hh, hrun ▸ h2⟩

/-- **The choice-word machine** (row W2-C; [AB09, Theorem 2.6]'s certificate reading,
relativized): every oracle NDTM `N` has a deterministic oracle machine `M`, with a
designated ordinary *choice tape* `j`, that, started from `Cfg.ofWords` with the choice
word `u` on tape `j` and every other tape empty, halts by `2|u| + 2` with output the
outcome `N.choiceOut O x u` of `N` along `u` — under every oracle `O`. Its queries are
`N`'s, submitted through its own query state.

**Proof sketch.** States `N.State ⊕ Fin 3`; tapes `N`'s ordinary tapes, the choice tape,
then `N`'s query tape last (the query tape is shared verbatim, so the submitted strings
agree). At `inl s`, `s ≠ N.qQuery`: a blank choice cell emits `false` and halts
(the row `Turing.OracleTM.answerAction false`); a bit `b` performs `N.tr b s` with the
choice head moving right. `qQuery := inl N.qQuery`; `qYes`, `qNo` are two pause states
that consume the bit `N`'s query step ignores (`Turing.OracleNDTM.stepWith` reads but
discards it): a blank emits `false` and halts, otherwise the choice head moves right into
`inl N.qYes` or `inl N.qNo`. Lockstep by induction on `u` in the
`Turing.OracleTM.toOracleNDTM_runWith` shape, with `Turing.OracleTM.step_of_qQuery`
against `stepWith` at the query state: one host step per source step, two at a query, at
most `2|u| + 2` in all. -/
theorem FinOracleNDTM.exists_choiceTM (N : FinOracleNDTM Bool) :
    ∃ (M : FinOracleTM Bool) (j : Fin M.k), ∀ (O : Language Bool) (x u : List Bool),
      (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀
          (Function.update (fun _ => []) j.castSucc u)) (2 * u.length + 2)).state = none ∧
        (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀
          (Function.update (fun _ => []) j.castSucc u)) (2 * u.length + 2)).output =
          N.choiceOut O x u := by
  sorry

end Turing
