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
import TCSlib.Complexity.TuringMachine.ChoiceWords

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
* `Turing.FinOracleNDTM.exists_choiceTM` — the choice-word machine (proved).

The plain certificate shell `Turing.FinTM.exists_certificateShell` and its projection identity
`Turing.FinTM.certificateShell_proj` live in `TCSlib.Complexity.TuringMachine.Build.CertShell`.

## Status

The choice-word machine `exists_choiceTM` is proved, including the query-at-exhaustion
case. The deterministic row `exists_plain_simulation` remains sorried: its clean install
call, frozen-input transport, delimited query window and cost summation are proved privately;
the dispatch host and its nine query phases remain to be assembled. The three corollaries,
the query-length lemma, the two choice-word lemmas and the word-placement facts are proved
(the corollaries still depend on the deterministic row). The shell's row is in
`Build/CertShell`. The query-length lemma and choice-word law continue to cite the shared
`Turing.OracleTM.runFrom_radius` and `TCSlib.Complexity.TuringMachine.ChoiceWords`.

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

**Proof sketch.** The radius bound `Turing.OracleTM.runFrom_radius` at radius `0` for the
query tape: its head stays within `s` of the origin and every query cell at distance at
least `s` is still blank. Cell `s` is therefore blank, and
`Turing.OracleTM.queryString_length_le_of_blank` bounds the query. -/
theorem OracleTM.queryString_runFrom_length_le_of_blank {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (M : OracleTM k Symbol State) (O : Language Symbol)
    (c : Cfg (k + 1) Symbol State input)
    (hblank : ∀ z, c.workTapes (OracleTM.queryTapeIdx k) z = none)
    (hpos : c.workTapePos (OracleTM.queryTapeIdx k) = 0) (s : ℕ) :
    (OracleTM.queryString (M.runFrom O c s)).length ≤ s := by
  have h := M.runFrom_radius O c (OracleTM.queryTapeIdx k) 0 (by rw [hpos]; simp)
    (fun z _ => hblank z) s
  exact OracleTM.queryString_length_le_of_blank _ s (h.2 _ (by simp))

/-! ### The oracle-call simulation -/

open Classical in
/-- The install-mode oracle call on empty virtual input, with an entry distinct
from its exit and a first-exit cut including time zero.

**Proof sketch.** Apply `exists_installCallTM` to the singleton oracle verdict.
When entry equals exit, `seamReleaseTM_firstReturn` changes the entry to its fresh
left state and preserves the positive return time. Otherwise the old entry itself
excludes the exit at zero. This is the first-cut normalization required before R2;
the installed call, including its cleanup, is always the public library call. -/
private theorem oracleInstallCall (D : FinTM Bool) (O : Language Bool) (τ : ℕ → ℕ)
    (hD : D.DecidesInTime O τ) :
    ∃ (C : FinTM Bool) (en ex : C.State) (a : ℕ), 0 < C.k ∧ en ≠ ex ∧
      ∀ z : List Bool, ∃ t ≤ a * (τ z.length + z.length + 2), 0 < t ∧
        (∀ s < t,
          (C.tm.runFrom (Cfg.ofWords (input := []) en (stateWord C.k z)) s).state ≠
            some ex) ∧
        C.tm.runFrom (Cfg.ofWords (input := []) en (stateWord C.k z)) t =
          Cfg.ofWords ex (stateWord C.k [decide (z ∈ O)]) := by
  classical
  obtain ⟨A, en, ex, a, hA, hcall⟩ :=
    FinTM.exists_installCallTM D (fun z => [decide (z ∈ O)]) τ
      (by simpa [FinTM.ComputesFunInTime, FinTM.DecidesInTime,
        MultiTapeTM.indicator] using hD)
  by_cases he : en = ex
  · subst ex
    refine ⟨⟨A.k, Unit ⊕ A.State, seamReleaseTM A.tm en⟩, .inl (), .inr en,
      a, hA, Sum.inl_ne_inr, ?_⟩
    intro z
    obtain ⟨t, ht, hpos, hcut, hend⟩ := hcall [] z
    have hr := seamReleaseTM_firstReturn A.tm en rfl hpos hend rfl hcut
    refine ⟨t, ?_, hpos, hr.2, hr.1⟩
    simpa only [List.length_singleton, Nat.add_assoc] using ht
  · refine ⟨A, en, ex, a, hA, he, ?_⟩
    intro z
    obtain ⟨t, ht, hpos, hcut, hend⟩ := hcall [] z
    refine ⟨t, ?_, hpos, ?_, hend⟩
    · simpa only [List.length_singleton, Nat.add_assoc] using ht
    · intro s hs
      cases s with
      | zero => exact fun h => he (Option.some.inj h)
      | succ s => exact hcut (s + 1) (Nat.succ_pos s) hs

/-- An empty-virtual-input clean call keeps the native input head and output
prefix fixed, restores its scratch, and retains the first-exit cut for R2.

**Proof sketch.** Cite `vhostEmitTM_runFrom` at the return and at each earlier
time. The returned virtual input position is `1`; for empty input that is the
right boundary, so its boundary tag must be `true`. Project a putative early
host exit through the first coordinate of the state pair to contradict the
source cut. No virtual-input trace is repeated. -/
private theorem oracleFrozenCall (C : FinTM Bool) (en ex : C.State)
    (arg result : List Bool) (t : ℕ)
    (hend : C.tm.runFrom (Cfg.ofWords (input := []) en (stateWord C.k arg)) t =
      Cfg.ofWords ex (stateWord C.k result))
    (hcut : ∀ s < t,
      (C.tm.runFrom (Cfg.ofWords (input := []) en (stateWord C.k arg)) s).state ≠
        some ex)
    (x : List Bool) (p : Fin (x.length + 2)) (out : List Bool) :
    (vhostEmitTM C.tm).runFrom
        (vhostCfg (Cfg.ofWords (input := []) en (stateWord C.k arg)) true p out) t =
      vhostCfg (Cfg.ofWords (input := []) ex (stateWord C.k result)) true p out ∧
    ∀ s < t, ((vhostEmitTM C.tm).runFrom
      (vhostCfg (Cfg.ofWords (input := []) en (stateWord C.k arg)) true p out) s).state ≠
        some (ex, true) := by
  have htag : FinTM.VirtualTag
      (Cfg.ofWords (input := []) en (stateWord C.k arg)).inputPos true := by
    simp [Cfg.ofWords, FinTM.VirtualTag]
  obtain ⟨b, hb, hr⟩ := vhostEmitTM_runFrom C.tm _ true htag p out t
  rw [hend] at hb hr
  have hbtrue : b = true := hb.2 rfl
  subst b
  refine ⟨hr, ?_⟩
  intro s hs hstate
  obtain ⟨tag, _, hprefix⟩ := vhostEmitTM_runFrom C.tm _ true htag p out s
  rw [hprefix] at hstate
  apply hcut s hs
  simpa [vhostCfg, Option.map_map, Function.comp_def] using
    congrArg (Option.map Prod.fst) hstate

/-- A query tape with a nonnegative blank becomes a delimited copy source when
cell `-1` is temporarily blanked. No cell beyond the first blank is constrained.

**Proof sketch.** Take the least nonnegative blank. The preceding nonblank cells
give a finite word; `queryString_eq_of_cells` identifies it with the submitted
query. On `[-1, |query|]` the temporary update supplies the left delimiter, the
finite word supplies the interior, and the least blank supplies the right delimiter. -/
private theorem oracleQueryWindow {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg (k + 1) Bool S x) (r : ℕ)
    (hblank : c.workTapes (OracleTM.queryTapeIdx k) (r : ℤ) = none) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (OracleTM.queryString c).length →
      Function.update (c.workTapes (OracleTM.queryTapeIdx k)) (-1) none p =
        FinTM.bufferTape (OracleTM.queryString c) p := by
  classical
  have hex : ∃ n : ℕ, c.workTapes (OracleTM.queryTapeIdx k) (n : ℤ) = none := ⟨r, hblank⟩
  let n := Nat.find hex
  let z := List.ofFn fun i : Fin n =>
    (c.workTapes (OracleTM.queryTapeIdx k) (i.val : ℤ)).getD false
  have hzlen : z.length = n := List.length_ofFn
  have hcells : ∀ i (hi : i < z.length),
      c.workTapes (OracleTM.queryTapeIdx k) (i : ℤ) = some z[i] := by
    intro i hi
    have hn : i < n := hzlen ▸ hi
    cases hc : c.workTapes (OracleTM.queryTapeIdx k) (i : ℤ) with
    | none => exact False.elim (Nat.find_min hex hn hc)
    | some b => simp [z, hc]
  have hright : c.workTapes (OracleTM.queryTapeIdx k) (z.length : ℤ) = none := by
    rw [hzlen]
    exact Nat.find_spec hex
  rw [OracleTM.queryString_eq_of_cells c z hcells hright]
  intro p hp hplen
  by_cases hleft : p = -1
  · subst p
    simp
  · rw [Function.update_of_ne hleft]
    have hpnonneg : 0 ≤ p := by omega
    have hpcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hpnonneg
    rw [← hpcast, FinTM.bufferTape_nat]
    by_cases hi : p.toNat < z.length
    · exact (hcells p.toNat hi).trans (List.getElem?_eq_getElem hi).symm
    · have hi' : p.toNat = z.length := by omega
      rw [hi', hright, List.getElem?_eq_none le_rfl]

/-- Summing the dispatcher's per-step charges gives the W2-S quadratic overhead
plus the exact sum of decider charges, without any monotonicity assumption.

**Proof sketch.** Induct on the time horizon. Retain the last query charge
exactly, and absorb its administrative term into the difference of consecutive
squares. The initial charge is the square at horizon zero. -/
private theorem oracleCost_sum (a t : ℕ) (cost charge : ℕ → ℕ)
    (hcost : ∀ r < t, cost r ≤ a * (r + 1) + a * charge r) :
    a + ∑ r ∈ Finset.range t, cost r ≤
      a * (t + 1) ^ 2 + a * ∑ r ∈ Finset.range t, charge r := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hpre := ih (fun r hr => hcost r (by omega))
    have hlast := hcost t (Nat.lt_succ_self t)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    ring_nf at hpre hlast ⊢
    omega

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
`Turing.MultiTapeTM.exists_first_halt`.

**Fill appendix (partial).** `oracleInstallCall` supplies the time-zero cut using R3′
when needed; `oracleFrozenCall` transports that call through Z1 at empty virtual input.
`oracleQueryWindow` proves the left-blanked query meets the copy row's framing premise,
and `oracleCost_sum` gives the final ledger. The source/shadow transport, nine query
phases, their R1/R2 assembly and the global simulation invariant are still unfilled;
the original admission below is retained openly. -/
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

**Proof sketch.** `a·(n^c + 1) ≤ 2a·(n + 1)^c` (`Turing.choiceBudget_le`). Forward, pad an
accepting branch (`Turing.FinOracleNDTM.AcceptsWithin.mono`). Backward, the
length-`a·(n^c + 1)` prefix of an accepting word has halted by all-branch halting, so by
absorption (`Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.runWith_of_halt`) it is
the whole run (`Turing.run_take_of_halted`, shared with the plain Theorem 2.6), and it
accepts. -/
theorem FinOracleNDTM.mem_iff_exists_choiceOut {N : FinOracleNDTM Bool} {O L : Language Bool}
    {a c : ℕ} (hN : N.DecidesInTime O L fun n => a * (n ^ c + 1)) (x : List Bool) :
    x ∈ L ↔ ∃ u : List Bool, u.length = 2 * a * (x.length + 1) ^ c ∧
      N.choiceOut O x u = [true] := by
  have hle : a * (x.length ^ c + 1) ≤ 2 * a * (x.length + 1) ^ c := choiceBudget_le a c _
  obtain ⟨hhalt, hacc⟩ := hN x
  constructor
  · intro hx
    obtain ⟨u, hu, h1, h2⟩ := (hacc.mp hx).mono hle
    exact ⟨u, hu, (choiceOut_eq_true_iff N O x u).mpr ⟨h1, h2⟩⟩
  · rintro ⟨u, hu, hout⟩
    obtain ⟨-, h2⟩ := (choiceOut_eq_true_iff N O x u).mp hout
    obtain ⟨hlen, hh, hrun⟩ := run_take_of_halted
      (fun w => N.tm.runWith O w (N.tm.initCfg x)) (fun c => c.state = none)
      (fun w w' h => by
        simp only [OracleNDTM.runWith_append (N := N.tm) O w w' (N.tm.initCfg x),
          OracleNDTM.runWith_of_halt O _ h])
      hhalt (hu ▸ hle)
    exact hacc.mpr ⟨u.take (a * (x.length ^ c + 1)), hlen, hh, hrun ▸ h2⟩

/-- The choice slot is inserted just before the query tape, leaving that tape last. -/
private abbrev oracleChoiceSlot (k : ℕ) : Fin (k + 1 + 1) := (Fin.last k).castSucc

/-- Forward a source action and consume one choice bit. This is the W2-C table
transform: the plain bank embeddings do not consume a choice on their framed tape. -/
private def oracleChoiceAction {k : ℕ} {S : Type} (a : Action (k + 1) Bool S) :
    Action (k + 1 + 1) Bool (S ⊕ Fin 3) where
  inputTape := a.inputTape
  workTapes := Fin.insertNth (oracleChoiceSlot k) (none, 1) a.workTapes
  output := a.output
  state := a.state.map Sum.inl

/-- The W2-C controller. The two answer pauses consume the ignored query choice;
all blank-choice rows use the public emit-and-halt action. -/
private def oracleChoiceMachine (N : FinOracleNDTM Bool) : FinOracleTM Bool where
  k := N.k + 1
  State := N.State ⊕ Fin 3
  tm := {
    q₀ := .inl N.tm.q₀
    qQuery := .inl N.tm.qQuery
    qYes := .inr 0
    qNo := .inr 1
    tr := fun q inp w => match w (oracleChoiceSlot N.k) with
      | none => OracleTM.answerAction false
      | some b => oracleChoiceAction (match q with
        | .inl s => N.tm.tr b s inp (fun i => w ((oracleChoiceSlot N.k).succAbove i))
        | .inr r => ⟨0, fun _ => (none, 0), none,
            some (if r = 0 then N.tm.qYes else N.tm.qNo)⟩) }
  wf := by constructor <;> simp

/-- A source configuration with one inserted, read-only choice tape and its cursor.
The source query tape and input head are retained verbatim. -/
private def oracleChoiceCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg (k + 1) Bool S x) (tape : ℤ → Option Bool) (p : ℤ) :
    Cfg (k + 1 + 1) Bool (S ⊕ Fin 3) x where
  state := c.state.map Sum.inl
  inputPos := c.inputPos
  workTapes := Fin.insertNth (oracleChoiceSlot k) tape c.workTapes
  workTapePos := Fin.insertNth (oracleChoiceSlot k) p c.workTapePos
  output := c.output

/-- Applying the choice transform forwards all source fields and advances just
the inserted cursor. Proof sketch: split the tape index at the inserted slot. -/
private theorem oracleChoiceAction_apply {k : ℕ} {S : Type} {x : List Bool}
    (a : Action (k + 1) Bool S) (c : Cfg (k + 1) Bool S x)
    (tape : ℤ → Option Bool) (p : ℤ) (s : Option (S ⊕ Fin 3)) :
    (oracleChoiceAction a).apply ({oracleChoiceCfg c tape p with state := s} :
      Cfg (k + 1 + 1) Bool (S ⊕ Fin 3) x) =
      oracleChoiceCfg (a.apply c) tape (p + 1) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    induction i using Fin.succAboveCases (oracleChoiceSlot k) <;>
      simp [oracleChoiceAction, oracleChoiceCfg, Action.apply]
  · funext i
    induction i using Fin.succAboveCases (oracleChoiceSlot k) <;>
      simp [oracleChoiceAction, oracleChoiceCfg, Action.apply]

/-- Inserting the choice tape does not change the word submitted to the oracle.
Proof sketch: the old last tape maps to the new last tape under `succAbove`. -/
private theorem oracleChoiceCfg_query {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg (k + 1) Bool S x) (tape : ℤ → Option Bool) (p : ℤ) :
    OracleTM.queryString (oracleChoiceCfg c tape p) = OracleTM.queryString c := by
  classical
  letI : DecidableEq Bool := fun a b => Classical.propDecidable (a = b)
  have hlast : (oracleChoiceSlot k).succAbove (Fin.last k) = Fin.last (k + 1) :=
    Fin.succAbove_ne_last_last (Fin.castSucc_ne_last _)
  have ht : (oracleChoiceCfg c tape p).workTapes (OracleTM.queryTapeIdx (k + 1)) =
      c.workTapes (OracleTM.queryTapeIdx k) := by
    change Fin.insertNth (α := fun _ => ℤ → Option Bool)
      (oracleChoiceSlot k) tape c.workTapes (Fin.last (k + 1)) = c.workTapes (Fin.last k)
    rw [← hlast, Fin.insertNth_apply_succAbove]
  exact congrArg (fun f : ℤ → Option Bool =>
    if h : ∃ n : ℕ, f (n : ℤ) = none then
      (List.range (Nat.find h)).filterMap fun n => f (n : ℤ)
    else []) ht

/-- A live nonquery step consumes a bit and forwards exactly the selected source
action. Proof sketch: the inserted tape is absent from the source read vector;
apply the action transport after selecting its current bit. -/
private theorem oracleChoice_step (N : FinOracleNDTM Bool) (O : Language Bool)
    {x : List Bool} (c : Cfg (N.k + 1) Bool N.State x)
    (tape : ℤ → Option Bool) (p : ℤ) (b : Bool) (q : N.State)
    (hs : c.state = some q) (hq : q ≠ N.tm.qQuery) (hb : tape p = some b) :
    (oracleChoiceMachine N).tm.step O (oracleChoiceCfg c tape p) =
      oracleChoiceCfg (N.tm.stepWith O b c) tape (p + 1) := by
  have hread : (fun i => (oracleChoiceCfg c tape p).workTapeSymbols
      ((oracleChoiceSlot N.k).succAbove i)) = c.workTapeSymbols := by
    funext i
    simp [oracleChoiceCfg, Cfg.workTapeSymbols]
  have hbit : (oracleChoiceCfg c tape p).workTapeSymbols (oracleChoiceSlot N.k) =
      some b := by simp [oracleChoiceCfg, Cfg.workTapeSymbols, hb]
  simp only [OracleNDTM.stepWith, hs, if_neg hq]
  unfold OracleTM.step
  simp only [oracleChoiceCfg, hs, Option.map_some]
  rw [if_neg (show (Sum.inl q : N.State ⊕ Fin 3) ≠
      (oracleChoiceMachine N).tm.qQuery from fun h => hq (Sum.inl.inj h))]
  change (match (oracleChoiceCfg c tape p).workTapeSymbols (oracleChoiceSlot N.k) with
    | none => OracleTM.answerAction false
    | some b => oracleChoiceAction (N.tm.tr b q c.inputSymbol
        (fun i => (oracleChoiceCfg c tape p).workTapeSymbols
          ((oracleChoiceSlot N.k).succAbove i)))).apply (oracleChoiceCfg c tape p) = _
  rw [hbit, hread]
  exact oracleChoiceAction_apply _ c tape p _

/-- The answer pause consumes a present choice bit without changing any source
tape, head or output. Proof sketch: its source action is stationary and silent. -/
private theorem oracleChoice_pause (N : FinOracleNDTM Bool) (O : Language Bool)
    {x : List Bool} (c : Cfg (N.k + 1) Bool N.State x)
    (tape : ℤ → Option Bool) (p : ℤ) (b : Bool) (r : Fin 3) (hb : tape p = some b) :
    (oracleChoiceMachine N).tm.step O
        ({oracleChoiceCfg c tape p with state := some (.inr r)} :
          Cfg (N.k + 1 + 1) Bool (N.State ⊕ Fin 3) x) =
      oracleChoiceCfg
        ({c with state := some (if r = 0 then N.tm.qYes else N.tm.qNo)} :
          Cfg (N.k + 1) Bool N.State x) tape (p + 1) := by
  unfold OracleTM.step
  simp only [oracleChoiceMachine, Sum.inr_ne_inl, ↓reduceIte]
  simp only [Cfg.workTapeSymbols, oracleChoiceCfg, Fin.insertNth_apply_same, hb]
  simpa only [Action.apply, moveInputPos_zero, SignType.coe_zero, add_zero, Option.toList_none,
    List.append_nil] using oracleChoiceAction_apply
      (⟨0, fun _ => (none, 0), none, some (if r = 0 then N.tm.qYes else N.tm.qNo)⟩ :
        Action (N.k + 1) Bool N.State) c tape p (some (.inr r))

/-- A query step is implemented by the oracle answer and its one-bit pause.
Proof sketch: cite the public query step on the host and on the fixed-choice
source; query-word preservation makes the two oracle tests identical. -/
private theorem oracleChoice_queryStep (N : FinOracleNDTM Bool) (O : Language Bool)
    {x : List Bool} (c : Cfg (N.k + 1) Bool N.State x)
    (tape : ℤ → Option Bool) (p : ℤ) (b : Bool)
    (hs : c.state = some N.tm.qQuery) (hb : tape p = some b) :
    (oracleChoiceMachine N).tm.runFrom O (oracleChoiceCfg c tape p) 2 =
      oracleChoiceCfg (N.tm.stepWith O b c) tape (p + 1) := by
  classical
  rw [show 2 = 1 + 1 from rfl, OracleTM.runFrom_succ_eq_step']
  change (oracleChoiceMachine N).tm.step O
    ((oracleChoiceMachine N).tm.step O (oracleChoiceCfg c tape p)) = _
  rw [OracleTM.step_of_qQuery _ O (cfg := oracleChoiceCfg c tape p)
      (by simp [oracleChoiceCfg, hs, oracleChoiceMachine]),
    oracleChoiceCfg_query, OracleNDTM.stepWith_eq_fixChoice_step,
    (N.tm.fixChoice b).step_of_qQuery O (cfg := c) hs]
  by_cases h : OracleTM.queryString c ∈ O
  · simp only [if_pos h]
    exact oracleChoice_pause N O c tape p b 0 hb
  · simp only [if_neg h]
    simpa only [show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte] using
      oracleChoice_pause N O c tape p b 1 hb

/-- A blank choice cell in any nonquery live state appends `false` and halts.
Proof sketch: select the public `answerAction false` row at the actual read. -/
private theorem oracleChoice_blank (N : FinOracleNDTM Bool) (O : Language Bool)
    {x : List Bool} (d : Cfg (N.k + 1 + 1) Bool (N.State ⊕ Fin 3) x)
    (q : N.State ⊕ Fin 3) (hs : d.state = some q) (hq : q ≠ .inl N.tm.qQuery)
    (hb : d.workTapeSymbols (oracleChoiceSlot N.k) = none) :
    (oracleChoiceMachine N).tm.step O d =
      {d with state := none, output := d.output ++ [false]} := by
  unfold OracleTM.step
  simp only [hs]
  rw [if_neg (show q ≠ (oracleChoiceMachine N).tm.qQuery from hq)]
  change (match d.workTapeSymbols (oracleChoiceSlot N.k) with
    | none => OracleTM.answerAction false
    | some b => oracleChoiceAction (match q with
      | .inl s => N.tm.tr b s d.inputSymbol
          (fun i => d.workTapeSymbols ((oracleChoiceSlot N.k).succAbove i))
      | .inr r => ⟨0, fun _ => (none, 0), none,
          some (if r = 0 then N.tm.qYes else N.tm.qNo)⟩)).apply d = _
  rw [hb]
  exact Cfg.ext rfl (moveInputPos_zero _) rfl (funext fun _ => add_zero _) rfl

/-- Exhaustion takes at most two steps, including exhaustion at a query state.
Proof sketch: a halted source needs no steps; a live ordinary state takes the
blank-choice action; a query state first answers and then takes that same action. -/
private theorem oracleChoice_exhaust (N : FinOracleNDTM Bool) (O : Language Bool)
    {x : List Bool} (c : Cfg (N.k + 1) Bool N.State x)
    (tape : ℤ → Option Bool) (p : ℤ) (hb : tape p = none) :
    ∃ s ≤ 2,
      ((oracleChoiceMachine N).tm.runFrom O (oracleChoiceCfg c tape p) s).state = none ∧
      ((oracleChoiceMachine N).tm.runFrom O (oracleChoiceCfg c tape p) s).output =
        if c.state = none then c.output else c.output ++ [false] := by
  classical
  have hblank : (oracleChoiceCfg c tape p).workTapeSymbols (oracleChoiceSlot N.k) =
      none := by simp [oracleChoiceCfg, Cfg.workTapeSymbols, hb]
  cases hs : c.state with
  | none => exact ⟨0, by omega, by simp [OracleTM.runFrom, oracleChoiceCfg, hs]⟩
  | some q =>
    by_cases hq : q = N.tm.qQuery
    · subst q
      refine ⟨2, le_rfl, ?_⟩
      have hrun : (oracleChoiceMachine N).tm.runFrom O (oracleChoiceCfg c tape p) 2 =
          {oracleChoiceCfg c tape p with state := none, output := c.output ++ [false]} := by
        change (oracleChoiceMachine N).tm.step O
          ((oracleChoiceMachine N).tm.step O (oracleChoiceCfg c tape p)) = _
        rw [OracleTM.step_of_qQuery _ O (cfg := oracleChoiceCfg c tape p)
          (by simp [oracleChoiceCfg, hs, oracleChoiceMachine])]
        split_ifs <;>
          exact oracleChoice_blank N O _ _ rfl (by simp [oracleChoiceMachine])
            (by exact hblank)
      rw [hrun]
      simp
    · refine ⟨1, by omega, ?_⟩
      have hrun : (oracleChoiceMachine N).tm.runFrom O (oracleChoiceCfg c tape p) 1 =
          {oracleChoiceCfg c tape p with state := none, output := c.output ++ [false]} :=
        oracleChoice_blank N O _ (.inl q) (by simp [oracleChoiceCfg, hs])
          (fun h => hq (Sum.inl.inj h)) hblank
      rw [hrun]
      simp

/-- Lockstep along a finite choice suffix, charging one step ordinarily and two
at a query, followed by the exhaustion tail.

**Proof sketch.** Induct on the suffix, generalizing the source configuration and
the choice cursor, as in `OracleTM.toOracleNDTM_runWith`. A halted configuration
absorbs the suffix. Otherwise one of the two local correspondence lemmas supplies
the next source configuration; compose with the induction hypothesis using the
public run algebra. The read invariant shifts by one, without changing the tape. -/
private theorem oracleChoice_run (N : FinOracleNDTM Bool) (O : Language Bool)
    {x : List Bool} (u : List Bool) (c : Cfg (N.k + 1) Bool N.State x)
    (tape : ℤ → Option Bool) (p : ℤ)
    (hread : ∀ i : ℕ, tape (p + i) = u[i]?) :
    ∃ s ≤ 2 * u.length + 2,
      ((oracleChoiceMachine N).tm.runFrom O (oracleChoiceCfg c tape p) s).state = none ∧
      ((oracleChoiceMachine N).tm.runFrom O (oracleChoiceCfg c tape p) s).output =
        if (N.tm.runWith O u c).state = none then (N.tm.runWith O u c).output
        else (N.tm.runWith O u c).output ++ [false] := by
  classical
  induction u generalizing c p with
  | nil => exact oracleChoice_exhaust N O c tape p (by simpa using hread 0)
  | cons b u ih =>
    cases hs : c.state with
    | none =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [OracleNDTM.runWith_of_halt O c hs]
      simp [OracleTM.runFrom, oracleChoiceCfg, hs]
    | some q =>
      have hb : tape p = some b := by simpa using hread 0
      obtain ⟨d, hd, hstep⟩ : ∃ d ≤ 2,
          (oracleChoiceMachine N).tm.runFrom O (oracleChoiceCfg c tape p) d =
            oracleChoiceCfg (N.tm.stepWith O b c) tape (p + 1) := by
        by_cases hq : q = N.tm.qQuery
        · exact ⟨2, le_rfl, oracleChoice_queryStep N O c tape p b (hq ▸ hs) hb⟩
        · exact ⟨1, by omega, oracleChoice_step N O c tape p b q hs hq hb⟩
      have htail : ∀ i : ℕ, tape (p + 1 + i) = u[i]? := by
        intro i
        simpa [Nat.cast_add, add_assoc, add_comm (i : ℤ) 1] using hread (i + 1)
      obtain ⟨s, htime, hhalt, hout⟩ := ih (N.tm.stepWith O b c) (p + 1) htail
      refine ⟨d + s, by simp only [List.length_cons]; omega, ?_⟩
      rw [OracleTM.runFrom_add, hstep]
      exact ⟨hhalt, hout⟩

/-- Loading the one choice word is exactly the transport of the source's initial
configuration. Proof sketch: `insertNth` separates the choice slot from all source
tapes; the source tapes start blank and every head starts at zero. -/
private theorem oracleChoice_initial (N : FinOracleNDTM Bool) (x u : List Bool) :
    Cfg.ofWords (input := x) (oracleChoiceMachine N).tm.q₀
        (Function.update (fun _ => []) (oracleChoiceSlot N.k) u) =
      oracleChoiceCfg (N.tm.initCfg x) (FinTM.bufferTape u) 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    induction i using Fin.succAboveCases (oracleChoiceSlot N.k) <;>
      simp [Cfg.ofWords, oracleChoiceCfg, Fin.succAbove_ne]
  · funext i
    induction i using Fin.succAboveCases (oracleChoiceSlot N.k) <;>
      simp [Cfg.ofWords, oracleChoiceCfg]

/-- **The choice-word machine** (row W2-C; [AB09, Theorem 2.6]'s certificate reading,
relativized): every oracle NDTM `N` has a deterministic oracle machine `M`, with a
designated ordinary *choice tape* `j`, that, started from `Cfg.ofWords` with the choice
word `u` on tape `j` and every other tape empty, halts by `2|u| + 2` with output the
outcome `N.choiceOut O x u` of `N` along `u` — under every oracle `O`. Its queries are
`N`'s, submitted through its own query state, with one exception: when `u` is exhausted at
`N`'s query state, the host may submit that query and discard its answer before emitting
`false`. For example, `u = []` with `N.q₀ = N.qQuery`: `N.runWith O []` makes no query. An
oracle answer changes no tape and no output, so the contract is the I/O statement below,
not the query trace (wave-1 statement gate, round 1, finding 4).

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
most `2|u| + 2` in all.

**Fill appendix.** `oracleChoice_run` generalizes to an arbitrary source configuration
and an arbitrary choice tape whose suffix is the remaining word. The tape layout uses
`Fin.insertNth` immediately before the query tape. Its action transport is shared by
ordinary steps and answer pauses. `oracleChoice_exhaust` handles an exhausted query
by the public oracle-answer step followed by the blank-choice action. Finally, halting
absorption pads the bounded run to the contract's exact observation time. -/
theorem FinOracleNDTM.exists_choiceTM (N : FinOracleNDTM Bool) :
    ∃ (M : FinOracleTM Bool) (j : Fin M.k), ∀ (O : Language Bool) (x u : List Bool),
      (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀
          (Function.update (fun _ => []) j.castSucc u)) (2 * u.length + 2)).state = none ∧
        (M.tm.runFrom O (Cfg.ofWords (input := x) M.tm.q₀
          (Function.update (fun _ => []) j.castSucc u)) (2 * u.length + 2)).output =
          N.choiceOut O x u := by
  classical
  refine ⟨oracleChoiceMachine N, Fin.last N.k, fun O x u => ?_⟩
  change ((oracleChoiceMachine N).tm.runFrom O
      (Cfg.ofWords (input := x) (oracleChoiceMachine N).tm.q₀
        (Function.update (fun _ => []) (oracleChoiceSlot N.k) u))
      (2 * u.length + 2)).state = none ∧ _
  erw [oracleChoice_initial N x u]
  obtain ⟨s, hs, hhalt, hout⟩ := oracleChoice_run N O u (N.tm.initCfg x)
    (FinTM.bufferTape u) 0 (by intro i; simp)
  have hpad : (oracleChoiceMachine N).tm.runFrom O
      (oracleChoiceCfg (N.tm.initCfg x) (FinTM.bufferTape u) 0) (2 * u.length + 2) =
      (oracleChoiceMachine N).tm.runFrom O
        (oracleChoiceCfg (N.tm.initCfg x) (FinTM.bufferTape u) 0) s := by
    conv_lhs => rw [← Nat.add_sub_of_le hs]
    rw [OracleTM.runFrom_add, OracleTM.runFrom_of_halt _ O _ hhalt]
  rw [hpad]
  exact ⟨hhalt, hout⟩

end Turing
