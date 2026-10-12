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
call, frozen-input transport, delimited query window and cost summation are proved privately.
**Continuation status (partial):** the source/shadow transport, query preparation and
restoration, and a finite phase-host definition are now present. The R1/R2 service seams,
global simulation invariant and final time bound remain to be proved. The three corollaries,
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

/-- Relocating the frozen call preserves both its returned configuration and its
first-exit cut. Proof sketch: apply the inherited empty-input Z1 contract, then
R1 at the return and at each earlier time. The ambient tapes are arbitrary. -/
private theorem oracleRelocatedCall {k : ℕ} (C : FinTM Bool) (en ex : C.State)
    (ι : Fin (1 + C.k) ↪ Fin k) (tapes : Fin k → ℤ → Option Bool)
    (heads : Fin k → ℤ) (arg result : List Bool) (t : ℕ)
    (hend : C.tm.runFrom (Cfg.ofWords (input := []) en (stateWord C.k arg)) t =
      Cfg.ofWords ex (stateWord C.k result))
    (hcut : ∀ s < t,
      (C.tm.runFrom (Cfg.ofWords (input := []) en (stateWord C.k arg)) s).state ≠ some ex)
    (x : List Bool) (p : Fin (x.length + 2)) (out : List Bool) :
    (embedEmitTM ι (vhostEmitTM C.tm)).runFrom
        (embedEmitCfg ι tapes heads []
          (vhostCfg (Cfg.ofWords (input := []) en (stateWord C.k arg)) true p out)) t =
      embedEmitCfg ι tapes heads []
        (vhostCfg (Cfg.ofWords (input := []) ex (stateWord C.k result)) true p out) ∧
    ∀ s < t, ((embedEmitTM ι (vhostEmitTM C.tm)).runFrom
      (embedEmitCfg ι tapes heads []
        (vhostCfg (Cfg.ofWords (input := []) en (stateWord C.k arg)) true p out)) s).state ≠
        some (ex, true) := by
  obtain ⟨hreturn, hfirst⟩ := oracleFrozenCall C en ex arg result t hend hcut x p out
  constructor
  · rw [embedEmitTM_runFrom, hreturn]
  · intro s hs
    rw [embedEmitTM_runFrom]
    exact hfirst s hs

/-- The shadow has one permanent origin marker, apart from the temporary query
bookmark. This definition describes its clean state between queries. -/
private def oracleOrigin : ℤ → Option Bool :=
  Function.update (fun _ => none) 0 (some true)

/-- The side bit distinguishes the two open half-lines; either bit is permitted
at zero. Allowing both values there makes one-step shadow tracking possible. -/
private def oracleSide (p : ℤ) (b : Bool) : Prop :=
  if b then 0 ≤ p else p ≤ 0

/-- At the origin the next move determines the side. Away from the origin a
unit move cannot cross to the other open half-line. -/
private theorem oracleSide_move (p : ℤ) (b : Bool) (d : SignType)
    (h : oracleSide p b) :
    oracleSide (p + (d : ℤ))
      (if oracleOrigin p = some true then decide (d ≠ .neg) else b) := by
  by_cases hp : p = 0
  · subst p
    cases d <;> simp [oracleSide, oracleOrigin]
  · cases b <;> cases d <;>
      simp [oracleSide, oracleOrigin, hp] at h ⊢ <;> omega

/-- A source action with a read-only shadow head following its designated tape.
No existing bank embedding synchronizes an extra head or updates a side bit;
this is the source/shadow transform required by W2-S, not a call host. -/
private def oracleShadowAction {n : ℕ} {S : Type} (i : Fin n)
    (a : Action n Bool S) (b : Bool) (marker : Option Bool) :
    Action (n + 1) Bool (S × Bool) where
  inputTape := a.inputTape
  workTapes := Fin.snoc a.workTapes (none, (a.workTapes i).2)
  output := a.output
  state := a.state.map fun q =>
    (q, if marker = some true then decide ((a.workTapes i).2 ≠ .neg) else b)

/-- The shadowed plain table. The shadow origin is installed by the enclosing
dispatcher before this table is entered; this table never writes the shadow. -/
private def oracleShadowTM {n : ℕ} {S : Type} (i : Fin n)
    (A : MultiTapeTM n Bool S) : MultiTapeTM (n + 1) Bool (S × Bool) where
  q₀ := (A.q₀, true)
  tr := fun qb inp w => oracleShadowAction i
    (A.tr qb.1 inp (fun j => w j.castSucc)) qb.2 (w (Fin.last n))

/-- Source fields followed by the origin shadow, whose head is exactly the
designated source head. The side bit is separate from all source data. -/
private def oracleShadowCfg {n : ℕ} {S : Type} {x : List Bool} (i : Fin n)
    (c : Cfg n Bool S x) (b : Bool) : Cfg (n + 1) Bool (S × Bool) x where
  state := c.state.map fun q => (q, b)
  inputPos := c.inputPos
  workTapes := Fin.snoc c.workTapes oracleOrigin
  workTapePos := Fin.snoc c.workTapePos (c.workTapePos i)
  output := c.output

/-- The shadow transform executes all source effects and only mirrors the
designated head on its extra tape. Proof sketch: split at the last tape. -/
private theorem oracleShadowAction_apply {n : ℕ} {S : Type} {x : List Bool}
    (i : Fin n) (a : Action n Bool S) (c : Cfg n Bool S x) (b : Bool) :
    (oracleShadowAction i a b (oracleOrigin (c.workTapePos i))).apply
        (oracleShadowCfg i c b) =
      oracleShadowCfg i (a.apply c)
        (if oracleOrigin (c.workTapePos i) = some true then
          decide ((a.workTapes i).2 ≠ .neg) else b) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    induction j using Fin.lastCases <;>
      simp [oracleShadowAction, oracleShadowCfg, Action.apply]
  · funext j
    induction j using Fin.lastCases <;>
      simp [oracleShadowAction, oracleShadowCfg, Action.apply]

/-- One shadow step preserves the side invariant, including a source halt.
Proof sketch: the action correspondence supplies the configuration; the unit
move lemma supplies the side. All ordinary tapes and emissions are forwarded. -/
private theorem oracleShadow_step {n : ℕ} {S : Type} {x : List Bool}
    (i : Fin n) (A : MultiTapeTM n Bool S) (c : Cfg n Bool S x) (b : Bool)
    (hb : oracleSide (c.workTapePos i) b) :
    ∃ b', oracleSide ((A.step c).workTapePos i) b' ∧
      (oracleShadowTM i A).step (oracleShadowCfg i c b) =
        oracleShadowCfg i (A.step c) b' := by
  cases hs : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa [MultiTapeTM.step, hs] using hb
    · simp [MultiTapeTM.step, oracleShadowCfg, hs]
  | some q =>
    let a := A.tr q c.inputSymbol c.workTapeSymbols
    let b' := if oracleOrigin (c.workTapePos i) = some true then
      decide ((a.workTapes i).2 ≠ .neg) else b
    refine ⟨b', ?_, ?_⟩
    · simpa only [MultiTapeTM.step, hs] using
        oracleSide_move (c.workTapePos i) b (a.workTapes i).2 hb
    · have hread : (fun j : Fin n => (oracleShadowCfg i c b).workTapeSymbols j.castSucc) =
          c.workTapeSymbols := by
        funext j
        simp [oracleShadowCfg, Cfg.workTapeSymbols]
      have hshadow : (oracleShadowCfg i c b).workTapeSymbols (Fin.last n) =
          oracleOrigin (c.workTapePos i) := by
        simp [oracleShadowCfg, Cfg.workTapeSymbols]
      simp only [MultiTapeTM.step, oracleShadowCfg, hs, Option.map_some]
      change (oracleShadowAction i
        (A.tr q c.inputSymbol
          (fun j => (oracleShadowCfg i c b).workTapeSymbols j.castSucc)) b
        ((oracleShadowCfg i c b).workTapeSymbols (Fin.last n))).apply
          (oracleShadowCfg i c b) = oracleShadowCfg i (a.apply c) b'
      rw [hread, hshadow]
      exact oracleShadowAction_apply i a c b

/-- The source/shadow invariant for a whole plain run.

**Proof sketch.** Apply the library iterate recursor to the paired source and
shadow configurations, retaining the side witness. The two projection
semiconjugacies identify the components with their public `runFrom`s. No new
run induction is written; subsequent relocation and guarded transfer use R1 and Z5. -/
private theorem oracleShadow_run {n : ℕ} {S : Type} {x : List Bool}
    (i : Fin n) (A : MultiTapeTM n Bool S) (c : Cfg n Bool S x) (b : Bool)
    (hb : oracleSide (c.workTapePos i) b) (t : ℕ) :
    ∃ b', oracleSide ((A.runFrom c t).workTapePos i) b' ∧
      (oracleShadowTM i A).runFrom (oracleShadowCfg i c b) t =
        oracleShadowCfg i (A.runFrom c t) b' := by
  let advance := fun d : Cfg n Bool S x × Cfg (n + 1) Bool (S × Bool) x =>
    (A.step d.1, (oracleShadowTM i A).step d.2)
  let invariant := fun d : Cfg n Bool S x × Cfg (n + 1) Bool (S × Bool) x =>
    ∃ side, oracleSide (d.1.workTapePos i) side ∧ d.2 = oracleShadowCfg i d.1 side
  have paired : invariant (advance^[t] (c, oracleShadowCfg i c b)) :=
    Function.Iterate.rec invariant ⟨b, hb, rfl⟩ (fun d h => by
      obtain ⟨side, hside, hcfg⟩ := h
      obtain ⟨next, hnext, hstep⟩ := oracleShadow_step i A d.1 side hside
      exact ⟨next, hnext, by simpa only [advance, hcfg] using hstep⟩) t
  have source : Function.Semiconj
      (Prod.fst : Cfg n Bool S x × Cfg (n + 1) Bool (S × Bool) x → _) advance A.step :=
    fun _ => rfl
  have shadow : Function.Semiconj
      (Prod.snd : Cfg n Bool S x × Cfg (n + 1) Bool (S × Bool) x → _)
        advance (oracleShadowTM i A).step := fun _ => rfl
  dsimp only [invariant] at paired
  rw [source.iterate_right t, shadow.iterate_right t] at paired
  exact paired

/-- A relocated source/shadow segment transfers to any dispatcher agreeing on
nonquery states. The source may halt at the end of the segment.

**Proof sketch.** R1 transports the shadow run. Projecting its state pair gives
the plain source state, so the nonquery guard supplies Z5's agreement premise.
The public empty-oracle bridge then identifies the plain source segment with
the run under the actual oracle. No oracle or bank lockstep is repeated. -/
private theorem oracleOffQuery {k : ℕ} {H : Type} {x : List Bool}
    (M : FinOracleTM Bool) (O : Language Bool) (P : MultiTapeTM k Bool H)
    (ι : Fin (M.k + 1 + 1) ↪ Fin k) (emb : (M.State × Bool) ↪ H)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (hagree : ∀ qb : M.State × Bool, qb.1 ≠ M.tm.qQuery → ∀ inp work,
      P.tr (emb qb) inp work =
        ((embedEmitTM ι (oracleShadowTM (OracleTM.queryTapeIdx M.k)
          M.tm.plainEmptyOracle)).tr qb inp work).mapState emb)
    (c : Cfg (M.k + 1) Bool M.State x) (b : Bool)
    (hb : oracleSide (c.workTapePos (OracleTM.queryTapeIdx M.k)) b) (t : ℕ)
    (hvisit : ∀ s < t,
      (M.tm.plainEmptyOracle.runFrom c s).state ≠ some M.tm.qQuery) :
    ∃ b', oracleSide ((M.tm.runFrom O c t).workTapePos (OracleTM.queryTapeIdx M.k)) b' ∧
      P.runFrom
          ((embedEmitCfg ι tapes heads []
            (oracleShadowCfg (OracleTM.queryTapeIdx M.k) c b)).mapState emb) t =
        (embedEmitCfg ι tapes heads []
          (oracleShadowCfg (OracleTM.queryTapeIdx M.k) (M.tm.runFrom O c t) b')).mapState emb := by
  have hguard : ∀ s < t, ∀ qb,
      ((embedEmitTM ι (oracleShadowTM (OracleTM.queryTapeIdx M.k)
        M.tm.plainEmptyOracle)).runFrom
          (embedEmitCfg ι tapes heads [] (oracleShadowCfg (OracleTM.queryTapeIdx M.k) c b)) s).state =
        some qb → qb.1 ≠ M.tm.qQuery := by
    intro s hs qb hstate heq
    obtain ⟨bs, _, hshadow⟩ := oracleShadow_run (OracleTM.queryTapeIdx M.k)
      M.tm.plainEmptyOracle c b hb s
    rw [embedEmitTM_runFrom, hshadow] at hstate
    have hsource : (M.tm.plainEmptyOracle.runFrom c s).state = some qb.1 := by
      simpa [embedEmitCfg, oracleShadowCfg, Option.map_map, Function.comp_def] using
        congrArg (Option.map Prod.fst) hstate
    exact hvisit s hs (heq ▸ hsource)
  have htransfer := MultiTapeTM.runFrom_mapState_of_agreeOn
    (embedEmitTM ι (oracleShadowTM (OracleTM.queryTapeIdx M.k) M.tm.plainEmptyOracle))
    P emb (fun qb => qb.1 ≠ M.tm.qQuery) hagree
    (embedEmitCfg ι tapes heads [] (oracleShadowCfg (OracleTM.queryTapeIdx M.k) c b)) t hguard
  obtain ⟨b', hside, hshadow⟩ := oracleShadow_run (OracleTM.queryTapeIdx M.k)
    M.tm.plainEmptyOracle c b hb t
  rw [M.tm.runFrom_eq_plainEmptyOracle O c t hvisit]
  refine ⟨b', hside, ?_⟩
  rw [htransfer, embedEmitTM_runFrom, hshadow]

/-- An R1 configuration is determined by its selected bank and its ambient
frame. Proof sketch: use the public selected-tape projections on the bank and
the public frame contract at time zero elsewhere. This seam glue does not
unfold or repeat R1's partial-inverse construction. -/
private theorem oracleBankCfg_eq {m k : ℕ} {S : Type} {x : List Bool}
    (A : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k)
    (c : Cfg m Bool S x) (d : Cfg k Bool S x)
    (hs : c.state = d.state) (hin : c.inputPos = d.inputPos) (hout : c.output = d.output)
    (htape : ∀ i, c.workTapes i = d.workTapes (ι i))
    (hhead : ∀ i, c.workTapePos i = d.workTapePos (ι i)) :
    embedEmitCfg ι d.workTapes d.workTapePos [] c = d := by
  refine Cfg.ext hs hin ?_ ?_ (by simpa [embedEmitCfg] using hout)
  · funext j
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_tape]
      exact htape i
    · exact ((embedEmitTM_frame ι A d.workTapes d.workTapePos [] c 0).1 j hj).1
  · funext j
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos]
      exact hhead i
    · exact ((embedEmitTM_frame ι A d.workTapes d.workTapePos [] c 0).1 j hj).2

/-- Copying to an entirely blank tape at zero installs precisely the buffered
query word. The source needs only the public copy's local window premise.

**Proof sketch.** Apply `copyTM_run_ofCfg`. Inside the destination interval its
overwrite is the buffer; outside, both the old blank tape and the buffer are
blank. The public first-exit cut is reused verbatim. -/
private theorem oracleCopy_intoBlank {k : ℕ} {x : List Bool} (src dst : Fin k)
    (hne : src ≠ dst) (z : List Bool) (d : Cfg k Bool SweepPhase x)
    (hs : d.state = some .sweep) (hpos : d.workTapePos dst = 0)
    (hblank : d.workTapes dst = fun _ => none)
    (hwindow : ∀ p : ℤ, -1 ≤ p → p ≤ (z.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape z p) :
    (copyTM k src dst).runFrom d (2 * z.length + 2) =
      { d with
        state := some .done
        workTapes := Function.update d.workTapes dst (FinTM.bufferTape z) } ∧
    ∀ s < 2 * z.length + 2, ((copyTM k src dst).runFrom d s).state ≠ some .done := by
  obtain ⟨hrun, hcut, _⟩ := copyTM_run_ofCfg src dst hne z d hs hwindow
  refine ⟨hrun.trans ?_, hcut⟩
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext j p
  by_cases hj : j = dst
  · subst j
    simp only [hpos, zero_add, sub_zero, Function.update_self, hblank, true_and]
    split_ifs with hp
    · rfl
    · symm
      unfold FinTM.bufferTape
      split_ifs with hnonneg
      · apply List.getElem?_eq_none
        omega
      · rfl
  · simp [hj]

/-- The source plus its shadow occupies the first bank; the virtual-input call
occupies the second bank; the final tape is the dispatch scratch. -/
private abbrev oracleHostTapes (m c : ℕ) : ℕ := (m + 1 + 1) + (1 + c) + 1

/-- R1 selection for the source and its one shadow tape. -/
private def oracleSourceBank (m c : ℕ) : Fin (m + 1 + 1) ↪ Fin (oracleHostTapes m c) where
  toFun j := (Fin.castAdd (1 + c) j).castSucc
  inj' := by
    intro i j h
    have hv := congrArg Fin.val h
    exact Fin.ext hv

/-- R1 selection for the empty virtual-input buffer and the clean-call bank. -/
private def oracleCallBank (m c : ℕ) : Fin (1 + c) ↪ Fin (oracleHostTapes m c) where
  toFun j := (Fin.natAdd (m + 1 + 1) j).castSucc
  inj' := by
    intro i j h
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val h)

/-- The four physical slots touched by query dispatch: source query, shadow,
scratch, and the call's argument tape. Their names describe the fixed W2 layout. -/
private def oracleSlots (m c : ℕ) (hc : 0 < c) : Fin 4 → Fin (oracleHostTapes m c) :=
  (Fin.cons (oracleSourceBank m c (Fin.last m).castSucc) (Fin.cons (oracleSourceBank m c (Fin.last (m + 1))) (Fin.cons (Fin.last ((m + 1 + 1) + (1 + c))) (Fin.cons (oracleCallBank m c (vhostBank ⟨0, hc⟩)) Fin.elim0))))

/-- The query-dispatch slots are distinct, including when the source has no
ordinary tapes. Proof sketch: their numerical offsets are respectively
`m`, `m+1`, `m+c+3`, and `m+3`, and the call has positive tape count. -/
private theorem oracleSlots_injective (m c : ℕ) (hc : 0 < c) :
    Function.Injective (oracleSlots m c hc) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;>
    simp [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, oracleSlots, oracleSourceBank, oracleCallBank, vhostBank] at hv ⊢ <;> omega

/-- Finite control for the nine query phases. The side is stored on scratch
cell zero during the call, and the original query cell `-1` on scratch cell one.
`none` in the saved side cell records an original query head at zero. -/
private inductive OracleDispatch where
  | boot
  | ready
  | bookmark (side : Bool)
  | origin (side : Bool)
  | save
  | copy
  | read
  | restore (verdict : Bool) (side : Option Bool)
  | depart (verdict : Bool) (side : Option Bool)
  | back (verdict side : Bool)
  | answer (verdict side : Bool)
  deriving DecidableEq, Fintype

/-- A local four-tape dispatch action, silent with the native input frozen.
Whole-bank placement is delegated to R1 in `oraclePhases`. -/
private def oracleDispatchAction
    (acts : Fin 4 → Option (Option Bool) × SignType) (q : OracleDispatch) :
    Action 4 Bool OracleDispatch := ⟨0, acts, none, some q⟩

/-- The dispatch table around the public copy and clean-call routines. There
is no library routine for a bookmarked two-head walk with a saved negative
query cell, so these finite-control rows are local to the W2 construction.

The bookmark is `false`; the origin is `true`. At zero the bookmark temporarily
replaces the origin, and the blank saved-side cell selects its direct restoration.
For a nonzero displacement, origin and bookmark are distinct. Both walks move the
query and shadow heads together. The native input and physical output are fixed. -/
private def oracleDispatchTM : MultiTapeTM 4 Bool OracleDispatch where
  q₀ := .boot
  tr := fun q _ w =>
    let act := oracleDispatchAction
    let stay : Option (Option Bool) × SignType := (none, 0)
    let shadow := w 1
    let scratch := w 2
    match q with
    | .boot => act (Fin.cons (stay) (Fin.cons ((some (some true), 0)) (Fin.cons (stay) (Fin.cons (stay) Fin.elim0)))) .ready
    | .bookmark side =>
        if shadow = some true then
          act (Fin.cons ((none, -1)) (Fin.cons ((some (some false), 0)) (Fin.cons ((none, 1)) (Fin.cons (stay) Fin.elim0)))) .save
        else
          act (Fin.cons (stay) (Fin.cons ((some (some false), 0)) (Fin.cons ((some (some side), 1)) (Fin.cons (stay) Fin.elim0)))) (.origin side)
    | .origin side =>
        if shadow = some true then act (Fin.cons ((none, -1)) (Fin.cons (stay) (Fin.cons (stay) (Fin.cons (stay) Fin.elim0)))) .save
        else
          let d : SignType := if side then -1 else 1
          act (Fin.cons ((none, d)) (Fin.cons ((none, d)) (Fin.cons (stay) (Fin.cons (stay) Fin.elim0)))) (.origin side)
    | .save => act (Fin.cons ((some none, 1)) (Fin.cons (stay) (Fin.cons ((some (w 0), -1)) (Fin.cons (stay) Fin.elim0)))) .copy
    | .read => act (Fin.cons ((none, -1)) (Fin.cons (stay) (Fin.cons ((some none, 1)) (Fin.cons ((some none, 0)) Fin.elim0))))
        (.restore ((w 3).getD false) scratch)
    | .restore verdict side =>
        act (Fin.cons ((some scratch, 1)) (Fin.cons (stay) (Fin.cons ((some none, -1)) (Fin.cons (stay) Fin.elim0)))) (.depart verdict side)
    | .depart verdict side =>
        match side with
        | none => act (Fin.cons (stay) (Fin.cons ((some (some true), 0)) (Fin.cons (stay) (Fin.cons (stay) Fin.elim0)))) (.answer verdict true)
        | some b =>
            let d : SignType := if b then 1 else -1
            act (Fin.cons ((none, d)) (Fin.cons ((none, d)) (Fin.cons (stay) (Fin.cons (stay) Fin.elim0)))) (.back verdict b)
    | .back verdict side =>
        if shadow = some false then act (Fin.cons (stay) (Fin.cons ((some none, 0)) (Fin.cons (stay) (Fin.cons (stay) Fin.elim0)))) (.answer verdict side)
        else
          let d : SignType := if side then 1 else -1
          act (Fin.cons ((none, d)) (Fin.cons ((none, d)) (Fin.cons (stay) (Fin.cons (stay) Fin.elim0)))) (.back verdict side)
    | _ => act (Fin.cons (stay) (Fin.cons (stay) (Fin.cons (stay) (Fin.cons (stay) Fin.elim0)))) q

/-- A dispatch walking configuration: the query and shadow heads have the
same coordinate, with the scratch and argument heads and every tape fixed. -/
private def oracleWalkCfg {x : List Bool} (d : Cfg 4 Bool OracleDispatch x)
    (q : OracleDispatch) (p : ℤ) : Cfg 4 Bool OracleDispatch x :=
  { d with
    state := some q
    workTapePos := Function.update (Function.update d.workTapePos 0 p) 1 p }

/-- The one shared walk for both origin search and bookmark search.

**Proof sketch.** Induct over the specified number of unit moves. Each row
moves exactly the first two local heads and writes nothing. The row hypothesis
is supplied by the relevant marker test, so the two searches share this trace;
R1, rather than another induction, later transports the walk to the host. -/
private theorem oracleWalk_run {x : List Bool} (d : Cfg 4 Bool OracleDispatch x)
    (q : OracleDispatch) (p : ℤ) (mv : SignType) (t : ℕ)
    (hrow : ∀ u < t, oracleDispatchTM.tr q d.inputSymbol
      (oracleWalkCfg d q (p + (mv : ℤ) * u)).workTapeSymbols =
        oracleDispatchAction
          (Fin.cons (none, mv) (Fin.cons (none, mv)
            (Fin.cons (none, 0) (Fin.cons (none, 0) Fin.elim0)))) q) :
    ∀ u ≤ t, oracleDispatchTM.runFrom (oracleWalkCfg d q p) u =
      oracleWalkCfg d q (p + (mv : ℤ) * u) := by
  intro u hu
  induction u with
  | zero => simp [oracleWalkCfg]
  | succ u ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    change (oracleDispatchTM.tr q d.inputSymbol
      (oracleWalkCfg d q (p + (mv : ℤ) * u)).workTapeSymbols).apply _ = _
    rw [hrow u (by omega)]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext j
      fin_cases j <;> simp [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, oracleDispatchAction, oracleWalkCfg]
    · funext j
      fin_cases j <;> simp [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, oracleDispatchAction, oracleWalkCfg, Nat.cast_add] <;> ring
    · exact List.append_nil _

/-- A bookmarked shadow retains `true` exactly at the origin, except when the
bookmark is itself at zero. In particular no nonzero cell reads `true`. -/
private theorem oracleBookmark_ne_origin (p z : ℤ) (hz : z ≠ 0) :
    Function.update oracleOrigin p (some false) z ≠ some true := by
  by_cases h : z = p
  · subst z
    simp
  · rw [Function.update_of_ne h]
    simp [oracleOrigin, hz]

/-- The clean four-tape dispatch frame at a source configuration. The native
input position and output prefix are arbitrary and are not inspected here. -/
private def oracleLocalCfg {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (q : OracleDispatch) (ip : Fin (x.length + 2)) (out : List Bool) :
    Cfg 4 Bool OracleDispatch x where
  state := some q
  inputPos := ip
  workTapes := Fin.cons f (Fin.cons oracleOrigin
    (Fin.cons (fun _ => none) (Fin.cons (fun _ => none) Fin.elim0)))
  workTapePos := Fin.cons p (Fin.cons p (Fin.cons 0 (Fin.cons 0 Fin.elim0)))
  output := out

/-- The local seam surrounding the copy/call service. The query's negative
delimiter is blanked, its old symbol and side are on scratch, the shadow is
bookmarked, and every local head is zero. `arg` is empty before copying and
is the singleton verdict after the clean call. -/
private def oracleReadyCfg {x : List Bool} (f : ℤ → Option Bool) (p : ℤ) (side : Bool)
    (arg : List Bool) (q : OracleDispatch) (ip : Fin (x.length + 2)) (out : List Bool) :
    Cfg 4 Bool OracleDispatch x where
  state := some q
  inputPos := ip
  workTapes := Fin.cons (Function.update f (-1) none)
    (Fin.cons (Function.update oracleOrigin p (some false))
      (Fin.cons (Function.update (Function.update (fun _ => none) 0
        (if p = 0 then none else some side)) 1 (f (-1)))
        (Fin.cons (FinTM.bufferTape arg) Fin.elim0)))
  workTapePos := fun _ => 0
  output := out

/-- After restoring the saved query cell and clearing the verdict and scratch,
only the shadow bookmark remains. The two moving heads are at `at`. -/
private def oracleBackCfg {x : List Bool} (f : ℤ → Option Bool) (bookmark pos : ℤ)
    (q : OracleDispatch) (ip : Fin (x.length + 2)) (out : List Bool) :
    Cfg 4 Bool OracleDispatch x :=
  { oracleLocalCfg f pos q ip out with
    workTapes := Fin.cons f (Fin.cons (Function.update oracleOrigin bookmark (some false))
      (Fin.cons (fun _ => none) (Fin.cons (fun _ => none) Fin.elim0))) }

/-- The nonzero-head bookmark seam: the scratch head is on cell one, ready to
save the query's negative delimiter after the walk to the origin. -/
private def oracleMarkedCfg {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side : Bool) (ip : Fin (x.length + 2)) (out : List Bool) :
    Cfg 4 Bool OracleDispatch x where
  state := some (.origin side)
  inputPos := ip
  workTapes := Fin.cons f (Fin.cons (Function.update oracleOrigin p (some false))
    (Fin.cons (Function.update (fun _ => none) 0 (some side))
      (Fin.cons (fun _ => none) Fin.elim0)))
  workTapePos := Fin.cons p (Fin.cons p (Fin.cons 1 (Fin.cons 0 Fin.elim0)))
  output := out

section oracleDispatchCells

-- Shared finite-cell normalization for the local dispatch equations. The
-- public extensionality and finite-quantifier rules handle all four slots.
attribute [local simp] MultiTapeTM.step oracleDispatchTM oracleDispatchAction
  oracleWalkCfg oracleLocalCfg oracleReadyCfg oracleBackCfg oracleMarkedCfg
  Cfg.workTapeSymbols oracleOrigin Fin.cons Fin.cases Fin.induction Fin.induction.go

/-- A query whose head is at the origin reaches the prepared seam in two
steps, even if its cell `-1` is nonblank. Proof sketch: bookmark the origin,
move to `-1`, then save and erase that cell while returning both active heads. -/
private theorem oraclePrepare_zero {x : List Bool} (f : ℤ → Option Bool) (side : Bool)
    (ip : Fin (x.length + 2)) (out : List Bool) :
    oracleDispatchTM.runFrom (oracleLocalCfg f 0 (.bookmark side) ip out) 2 =
      oracleReadyCfg f 0 side [] .copy ip out := by
  change oracleDispatchTM.step (oracleDispatchTM.step (oracleLocalCfg f 0 (.bookmark side) ip out)) = _
  simp [Cfg.ext_iff, funext_iff, Fin.forall_fin_succ]

/-- Reading the verdict and restoring cell `-1` takes exactly two steps, from
every bookmarked displacement. Both scratch cells and the verdict tape become
blank, and the old negative query cell is restored without any assumption on it.

**Proof sketch.** The read row saves the verdict and side in finite control and
clears their cells. The restore row reads the saved negative cell, writes it
back, and clears its scratch cell. The singleton buffer is the public
`bufferTape_append` at the empty word. -/
private theorem oracleRestore_cell {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side verdict : Bool) (ip : Fin (x.length + 2)) (out : List Bool) :
    oracleDispatchTM.runFrom (oracleReadyCfg f p side [verdict] .read ip out) 2 =
      oracleBackCfg f p 0 (.depart verdict (if p = 0 then none else some side)) ip out := by
  have hbuf : FinTM.bufferTape [verdict] =
      Function.update (fun _ : ℤ => none) 0 (some verdict) := by
    simpa using FinTM.bufferTape_append ([] : List Bool) verdict
  change oracleDispatchTM.step (oracleDispatchTM.step (oracleReadyCfg f p side [verdict] .read ip out)) = _
  simp [Cfg.ext_iff, funext_iff, Fin.forall_fin_succ, hbuf, Function.update_apply]
  constructor
  · intro z
    split_ifs <;> simp_all
  · intro z hz₁ hz₀
    simp [hz₁, hz₀]

/-- Writing back the shadow's original cell removes its bookmark. The same
field argument covers the origin branch and the nonzero return branch.

**Proof sketch.** Use the public one-tape writing step. The written cell is
the original shadow value at its current head, so two same-cell updates reduce
to the original tape; a zero move preserves the head. -/
private theorem oracleMarker_step {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (q q' : OracleDispatch) (ip : Fin (x.length + 2)) (out : List Bool)
    (hrow : oracleDispatchTM.tr q (oracleBackCfg f p p q ip out).inputSymbol
      (oracleBackCfg f p p q ip out).workTapeSymbols =
        tapeAction 1 0 (some (oracleOrigin p)) 0 q') :
    oracleDispatchTM.step (oracleBackCfg f p p q ip out) =
      oracleLocalCfg f p q' ip out := by
  rw [step_of_tapeAction_write oracleDispatchTM _ 1 0 (oracleOrigin p) 0 rfl hrow,
    moveInputPos_zero]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j z
    fin_cases j <;>
      simp [oracleBackCfg, oracleLocalCfg, Fin.cons, Fin.cases, Fin.induction,
        Fin.induction.go, Function.update_apply] <;> split_ifs <;> simp_all [eq_comm]
  · funext j
    fin_cases j <;>
      simp [oracleBackCfg, oracleLocalCfg, Fin.cons, Fin.cases, Fin.induction,
        Fin.induction.go]

/-- A bookmark at the origin is removed directly after the two restoration
steps. Proof sketch: the blank side cell selects the direct branch, which
restores the origin marker and enters the live answer anchor. -/
private theorem oracleRestore_zero {x : List Bool} (f : ℤ → Option Bool)
    (side verdict : Bool) (ip : Fin (x.length + 2)) (out : List Bool) :
    oracleDispatchTM.runFrom (oracleReadyCfg f 0 side [verdict] .read ip out) 3 =
      oracleLocalCfg f 0 (.answer verdict true) ip out := by
  rw [show 3 = 2 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step', oracleRestore_cell]
  simp only [ite_true]
  apply oracleMarker_step
  dsimp [oracleDispatchTM, oracleDispatchAction, tapeAction, oracleOrigin]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- Bookmarking a nonzero query position preserves the source data and saves
the side on scratch. Proof sketch: the clean shadow is blank at that position,
so the non-origin branch writes the bookmark and the side and moves only scratch. -/
private theorem oracleMark_step {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side : Bool) (hp : p ≠ 0) (ip : Fin (x.length + 2)) (out : List Bool) :
    oracleDispatchTM.step (oracleLocalCfg f p (.bookmark side) ip out) =
      oracleMarkedCfg f p side ip out := by
  simp [Cfg.ext_iff, funext_iff, Fin.forall_fin_succ, hp]

/-- Once the marked heads reach zero, the origin test and the save row prepare
the query in two more steps. Proof sketch: the bookmark is away from zero;
the first row moves the query head to `-1`, and the next stores and blanks it. -/
private theorem oraclePrepare_tail {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side : Bool) (hp : p ≠ 0) (ip : Fin (x.length + 2)) (out : List Bool) :
    oracleDispatchTM.runFrom
        (oracleWalkCfg (oracleMarkedCfg f p side ip out) (.origin side) 0) 2 =
      oracleReadyCfg f p side [] .copy ip out := by
  change oracleDispatchTM.step (oracleDispatchTM.step _) = _
  simp [Cfg.ext_iff, funext_iff, Fin.forall_fin_succ, hp, Ne.symm hp, Function.update_apply]

/-- A saved nonzero side starts the return walk with one outward move. -/
private theorem oracleDepart_step {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side verdict : Bool) (ip : Fin (x.length + 2)) (out : List Bool) :
    oracleDispatchTM.step (oracleBackCfg f p 0 (.depart verdict (some side)) ip out) =
      oracleBackCfg f p ((if side then 1 else -1 : SignType) : ℤ)
        (.back verdict side) ip out := by
  simp [Cfg.ext_iff, funext_iff, Fin.forall_fin_succ]

end oracleDispatchCells

/-- A nonzero marked query head walks to the origin in exactly its absolute
displacement, and every prefix retains the origin-walk control.

**Proof sketch.** The side invariant fixes the direction. Before the absolute
displacement has been traversed, the shadow coordinate is nonzero and therefore
cannot read the origin marker. Apply the one shared two-head walk. -/
private theorem oracleOrigin_run {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side : Bool) (hb : oracleSide p side)
    (ip : Fin (x.length + 2)) (out : List Bool) :
    ∀ u ≤ p.natAbs,
      oracleDispatchTM.runFrom (oracleMarkedCfg f p side ip out) u =
        oracleWalkCfg (oracleMarkedCfg f p side ip out) (.origin side)
          (p + ((if side then -1 else 1 : SignType) : ℤ) * u) := by
  let d := oracleMarkedCfg f p side ip out
  have hnz (u : ℕ) (hu : u < p.natAbs) :
      p + ((if side then -1 else 1 : SignType) : ℤ) * u ≠ 0 := by
    have habs : (p.natAbs : ℤ) = |p| := Int.natCast_natAbs p
    cases side <;> simp [oracleSide] at hb ⊢
    · rw [abs_of_nonpos hb] at habs
      omega
    · rw [abs_of_nonneg hb] at habs
      omega
  have hstart : oracleWalkCfg d (.origin side) p = d := by
    apply Cfg.ext <;> try rfl
    funext j
    fin_cases j <;> simp [oracleWalkCfg, d, oracleMarkedCfg,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  have walk := oracleWalk_run d (.origin side) p
    (if side then -1 else 1) p.natAbs (fun u hu => by
      have hmarker : (oracleWalkCfg d (.origin side)
          (p + ((if side then -1 else 1 : SignType) : ℤ) * u)).workTapeSymbols 1 ≠ some true := by
        simpa [oracleWalkCfg, d, oracleMarkedCfg, Cfg.workTapeSymbols,
          Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] using
            oracleBookmark_ne_origin p _ (hnz u hu)
      simp [oracleDispatchTM, hmarker])
  simpa only [hstart] using walk

/-- The side bit reconstructs a displacement from its absolute value; either
bit gives zero when the head is at zero. -/
private theorem oracleSide_distance (p : ℤ) (side : Bool) (hb : oracleSide p side) :
    p = ((if side then 1 else -1 : SignType) : ℤ) * p.natAbs := by
  cases side with
  | false =>
    have hp : p ≤ 0 := hb
    simp [abs_of_nonpos hp]
  | true =>
    have hp : 0 ≤ p := hb
    simp [abs_of_nonneg hp]

/-- The complete local query prelude, with a control cut suitable for the
phase host. It costs at most the head displacement plus three, independently
of the query contents and of every ordinary source tape.

**Proof sketch.** At zero use the two-step seam. Otherwise bookmark once,
walk the absolute displacement, and perform the two-step origin/save tail.
Earlier controls are exactly bookmark, origin-walk, or save, so no service
redirect is taken early. -/
private theorem oraclePrepare {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side : Bool) (hb : oracleSide p side) (ip : Fin (x.length + 2)) (out : List Bool) :
    ∃ t ≤ p.natAbs + 3,
      oracleDispatchTM.runFrom (oracleLocalCfg f p (.bookmark side) ip out) t =
        oracleReadyCfg f p side [] .copy ip out ∧
      ∀ u < t,
        (oracleDispatchTM.runFrom (oracleLocalCfg f p (.bookmark side) ip out) u).state =
            some (.bookmark side) ∨
        (oracleDispatchTM.runFrom (oracleLocalCfg f p (.bookmark side) ip out) u).state =
            some (.origin side) ∨
        (oracleDispatchTM.runFrom (oracleLocalCfg f p (.bookmark side) ip out) u).state =
            some .save := by
  by_cases hp : p = 0
  · subst p
    refine ⟨2, by simp, oraclePrepare_zero f side ip out, ?_⟩
    intro u hu
    have cases_u : u = 0 ∨ u = 1 := by omega
    rcases cases_u with rfl | rfl
    · exact Or.inl rfl
    · right; right
      change (oracleDispatchTM.step (oracleLocalCfg f 0 (.bookmark side) ip out)).state = _
      simp [MultiTapeTM.step, oracleDispatchTM,
        oracleDispatchAction, oracleLocalCfg, Cfg.workTapeSymbols, oracleOrigin,
        Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  · have hzero : p + ((if side then -1 else 1 : SignType) : ℤ) * p.natAbs = 0 := by
      have he := oracleSide_distance p side hb
      cases side <;> simp at he ⊢ <;> omega
    have reach := oracleOrigin_run f p side hb ip out p.natAbs le_rfl
    rw [hzero] at reach
    refine ⟨p.natAbs + 3, le_rfl, ?_, ?_⟩
    · rw [show p.natAbs + 3 = 1 + (p.natAbs + 2) from by omega,
        MultiTapeTM.runFrom_add]
      change oracleDispatchTM.runFrom
        (oracleDispatchTM.step (oracleLocalCfg f p (.bookmark side) ip out)) (p.natAbs + 2) = _
      rw [oracleMark_step f p side hp, MultiTapeTM.runFrom_add, reach,
        oraclePrepare_tail f p side hp]
    · intro u hu
      by_cases hu0 : u = 0
      · subst u
        exact Or.inl rfl
      · by_cases hwalk : u ≤ p.natAbs + 1
        · right; left
          rw [show u = 1 + (u - 1) from by omega, MultiTapeTM.runFrom_add]
          change (oracleDispatchTM.runFrom
            (oracleDispatchTM.step (oracleLocalCfg f p (.bookmark side) ip out)) (u - 1)).state = _
          rw [oracleMark_step f p side hp, oracleOrigin_run f p side hb ip out
            (u - 1) (by omega)]
          rfl
        · right; right
          rw [show u = 1 + (p.natAbs + 1) from by omega, MultiTapeTM.runFrom_add]
          change (oracleDispatchTM.runFrom
            (oracleDispatchTM.step (oracleLocalCfg f p (.bookmark side) ip out)) (p.natAbs + 1)).state = _
          rw [oracleMark_step f p side hp, MultiTapeTM.runFrom_succ_eq_step', reach]
          simp [MultiTapeTM.step, oracleDispatchTM, oracleDispatchAction, oracleWalkCfg,
            oracleMarkedCfg, Cfg.workTapeSymbols, oracleOrigin, Ne.symm hp,
            Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

/-- All prefixes of the nonzero return walk, ending on the bookmark before
its erasing step. Proof sketch: an earlier coordinate differs from the original
head position by the side-distance equality; its shadow cell cannot be `false`.
Invoke the same walk used for origin search. -/
private theorem oracleBack_run {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side verdict : Bool) (hb : oracleSide p side)
    (ip : Fin (x.length + 2)) (out : List Bool) :
    ∀ u ≤ p.natAbs - 1,
      oracleDispatchTM.runFrom
          (oracleBackCfg f p ((if side then 1 else -1 : SignType) : ℤ)
            (.back verdict side) ip out) u =
        oracleBackCfg f p
          (((if side then 1 else -1 : SignType) : ℤ) +
            ((if side then 1 else -1 : SignType) : ℤ) * u) (.back verdict side) ip out := by
  let mv : SignType := if side then 1 else -1
  let d := oracleBackCfg f p (mv : ℤ) (.back verdict side) ip out
  have hnq (u : ℕ) (hu : u < p.natAbs - 1) : (mv : ℤ) + (mv : ℤ) * u ≠ p := by
    have hd := oracleSide_distance p side hb
    cases side <;> simp [mv] at hd ⊢ <;> omega
  have walk := oracleWalk_run d (.back verdict side) (mv : ℤ) mv (p.natAbs - 1)
    (fun u hu => by
      have hmarker : (oracleWalkCfg d (.back verdict side)
          ((mv : ℤ) + (mv : ℤ) * u)).workTapeSymbols 1 ≠ some false := by
        simp [oracleWalkCfg, d, oracleBackCfg, oracleLocalCfg, Cfg.workTapeSymbols,
          Fin.cons, Fin.cases, Fin.induction, Fin.induction.go,
          Function.update_of_ne (hnq u hu), oracleOrigin, Function.update_apply]
      simp [oracleDispatchTM, hmarker, mv])
  have hcfg (r : ℤ) : oracleWalkCfg d (.back verdict side) r =
      oracleBackCfg f p r (.back verdict side) ip out := by
    refine Cfg.ext rfl rfl rfl ?_ rfl
    funext j
    fin_cases j <;> simp [oracleWalkCfg, d, oracleBackCfg, oracleLocalCfg,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  simpa only [hcfg] using walk

/-- The nonzero bookmark is erased by the public one-tape writing row.
Proof sketch: the bookmarked cell reads `false`, and its original value is
blank, so `oracleMarker_step` applies. -/
private theorem oracleErase_step {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side verdict : Bool) (hp : p ≠ 0) (ip : Fin (x.length + 2)) (out : List Bool) :
    oracleDispatchTM.step (oracleBackCfg f p p (.back verdict side) ip out) =
      oracleLocalCfg f p (.answer verdict side) ip out := by
  apply oracleMarker_step
  simp [oracleDispatchTM, oracleDispatchAction, oracleBackCfg, oracleLocalCfg,
    Cfg.workTapeSymbols, oracleOrigin, hp, tapeAction,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  funext j
  fin_cases j <;> rfl

/-- Three postlude steps start the nonzero return walk. This seam is shared
by the returned-configuration proof and its first-exit guard. -/
private theorem oracleRestore_three {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side verdict : Bool) (hp : p ≠ 0) (ip : Fin (x.length + 2)) (out : List Bool) :
    oracleDispatchTM.runFrom (oracleReadyCfg f p side [verdict] .read ip out) 3 =
      oracleBackCfg f p ((if side then 1 else -1 : SignType) : ℤ)
        (.back verdict side) ip out := by
  rw [show 3 = 2 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step', oracleRestore_cell,
    if_neg hp, oracleDepart_step]

/-- The local query postlude restores every tape and head, preserving arbitrary
native input position and prior output. Its cost is absolute displacement plus
three. At zero the returned side may be normalized to `true`.

**Proof sketch.** First use the two-step negative-cell restoration. At zero
restore the origin marker directly. Otherwise depart one cell, walk to the
bookmark, and erase it. Both walking directions use `oracleBack_run`; the final
write uses the public one-tape row. -/
private theorem oracleRestore {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side verdict : Bool) (hb : oracleSide p side)
    (ip : Fin (x.length + 2)) (out : List Bool) :
    ∃ side', oracleSide p side' ∧
      oracleDispatchTM.runFrom (oracleReadyCfg f p side [verdict] .read ip out) (p.natAbs + 3) =
        oracleLocalCfg f p (.answer verdict side') ip out := by
  by_cases hp : p = 0
  · subst p
    exact ⟨true, by simp [oracleSide], oracleRestore_zero f side verdict ip out⟩
  · have hpos : 0 < p.natAbs := Int.natAbs_pos.mpr hp
    have hend : ((if side then 1 else -1 : SignType) : ℤ) +
        ((if side then 1 else -1 : SignType) : ℤ) * (p.natAbs - 1 : ℕ) = p := by
      have hd := oracleSide_distance p side hb
      have hcast : ((p.natAbs - 1 : ℕ) : ℤ) = (p.natAbs : ℤ) - 1 := by omega
      rw [hcast]
      cases side <;>
        simp only [Bool.false_eq_true, ↓reduceIte,
          SignType.coe_neg_one, SignType.coe_one, one_mul, neg_one_mul] at hd ⊢ <;> omega
    have reach := oracleBack_run f p side verdict hb ip out (p.natAbs - 1) le_rfl
    rw [hend] at reach
    refine ⟨side, hb, ?_⟩
    rw [show p.natAbs + 3 = (3 + (p.natAbs - 1)) + 1 from by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
      oracleRestore_three f p side verdict hp, reach,
      oracleErase_step f p side verdict hp]

/-- Dispatch controls with no phase-host redirect. The three live handover
families are readiness after initialization, entry to service, and the answer. -/
private def oracleDispatchInternal : OracleDispatch → Prop
  | .ready | .copy | .answer _ _ => False
  | _ => True

/-- The restoration phase never reaches a redirect before its return time.

**Proof sketch.** The first three controls are read, restore, and depart.
Any remaining proper prefix is on the nonzero return walk, whose shared
prefix theorem gives a back-walk control. Thus the answer anchor is first. -/
private theorem oracleRestore_cut {x : List Bool} (f : ℤ → Option Bool) (p : ℤ)
    (side verdict : Bool) (hb : oracleSide p side)
    (ip : Fin (x.length + 2)) (out : List Bool) :
    ∀ u < p.natAbs + 3, ∀ q,
      (oracleDispatchTM.runFrom (oracleReadyCfg f p side [verdict] .read ip out) u).state =
        some q → oracleDispatchInternal q := by
  intro u hu q hq
  by_cases hsmall : u < 3
  · have cases_u : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases cases_u with rfl | rfl | rfl
    · have he : q = .read := (Option.some.inj hq).symm
      subst q
      trivial
    · have he : q = .restore verdict (if p = 0 then none else some side) := by
        simpa [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step, oracleDispatchTM,
          oracleDispatchAction, oracleReadyCfg, Cfg.workTapeSymbols,
          Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] using (Option.some.inj hq).symm
      subst q
      trivial
    · rw [oracleRestore_cell] at hq
      have he : q = .depart verdict (if p = 0 then none else some side) :=
        (Option.some.inj hq).symm
      subst q
      trivial
  · have hp : p ≠ 0 := by intro he; subst p; simp at hu; omega
    rw [show u = 3 + (u - 3) from by omega, MultiTapeTM.runFrom_add,
      oracleRestore_three f p side verdict hp,
      oracleBack_run f p side verdict hb ip out (u - 3) (by omega)] at hq
    have he : q = .back verdict side := (Option.some.inj hq).symm
    subst q
    trivial

/-- The three phase families of the public finite phase host. The service
phase itself is exactly the R2 seam from the public copy to the relocated call. -/
private inductive OraclePhase where
  | source
  | dispatch
  | service
  deriving DecidableEq, Fintype

/-- State alphabets of the W2 source, dispatch, and R2 service phases. -/
private def oraclePhaseState (M : FinOracleTM Bool) (C : FinTM Bool) : OraclePhase → Type
  | .source => M.State × Bool
  | .dispatch => OracleDispatch
  | .service => SweepPhase ⊕ (C.State × Bool)

private instance oraclePhaseFintype (M : FinOracleTM Bool) (C : FinTM Bool) (i : OraclePhase) :
    Fintype (oraclePhaseState M C i) := by cases i <;> unfold oraclePhaseState <;> infer_instance

/-- Each phase uses its existing public host. The source's new shadow is the
only additional transport; copy and call are joined by `seamCompTM`. -/
private noncomputable def oraclePhases (M : FinOracleTM Bool) (C : FinTM Bool)
    (hc : 0 < C.k) (en : C.State) (i : OraclePhase) :
    MultiTapeTM (oracleHostTapes M.k C.k) Bool (oraclePhaseState M C i) :=
  match i with
  | .source => embedEmitTM (oracleSourceBank M.k C.k)
      (oracleShadowTM (OracleTM.queryTapeIdx M.k) M.tm.plainEmptyOracle)
  | .dispatch => embedEmitTM
      ⟨oracleSlots M.k C.k hc, oracleSlots_injective M.k C.k hc⟩ oracleDispatchTM
  | .service => seamCompTM
      (copyTM _ (oracleSlots M.k C.k hc 0) (oracleSlots M.k C.k hc 3)) .done
      (embedEmitTM (oracleCallBank M.k C.k) (vhostEmitTM C.tm)) (en, true)

/-- Finite redirects of the W2 phase host. Only a completed query service
returns to the source's yes/no state; source halts remain genuine host halts. -/
private noncomputable def oracleRedirect (M : FinOracleTM Bool) (C : FinTM Bool)
    (ex : C.State) (i : OraclePhase) (q : oraclePhaseState M C i) :
    Option (Σ j, oraclePhaseState M C j) := by
  classical
  cases i with
  | source => exact if q.1 = M.tm.qQuery then some ⟨.dispatch, .bookmark q.2⟩ else none
  | dispatch => exact match q with
    | .ready => some ⟨.source, (M.tm.q₀, true)⟩
    | .copy => some ⟨.service, .inl .sweep⟩
    | .answer verdict side => some ⟨.source, (if verdict then M.tm.qYes else M.tm.qNo, side)⟩
    | _ => none
  | service => exact if q = .inr (ex, true) then some ⟨.dispatch, .read⟩ else none

open Classical in
/-- The finite plain witness, using one existing phase host around the R2
copy/call seam. Its full query restoration and global simulation remain proof
obligations until the W2-S target is discharged. -/
private noncomputable def oracleHost (M : FinOracleTM Bool) (C : FinTM Bool)
    (hc : 0 < C.k) (en ex : C.State) : FinTM Bool where
  k := oracleHostTapes M.k C.k
  State := Σ i, oraclePhaseState M C i
  tm := phaseHostTM (oraclePhases M C hc en) ⟨.dispatch, .boot⟩ (oracleRedirect M C ex)

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
the original admission below is retained openly.

**Fill appendix (continuation, partial).** `oracleRelocatedCall` adds R1 transport to
`oracleFrozenCall`. `oracleShadow_run` maintains the head side and origin shadow;
`oracleOffQuery` cites the plain-empty-oracle bridge and Z5 to transfer an off-query
segment. `oraclePrepare` bookmarks, reaches zero, and saves and blanks cell `-1`;
`oracleRestore` and `oracleRestore_cut` restore all four local tapes and heads with
no early answer. The origin and bookmark searches share `oracleWalk_run`. The
finite `oracleHost` uses the public phase host, with an R2 seam between public copy
and the relocated Z1 call. Its complete service seam, initial configuration,
global simulation and time ledger are still unproved. No new private admission is
introduced; the original W2-S admission below remains the continuation frontier. -/
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
