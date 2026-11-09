/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.Padding
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.TuringMachine.SelfUniversal
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.SpaceComplexity.WindowClock
import TCSlib.Complexity.ClassNP.PClosure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space hierarchy theorem

[AB09, §4.1.3, Theorem 4.8] with the space-bounded universal machine of
[AB09, Exercise 4.1] (its forward clause, as the book states it), the
strictness corollary `L ⊊ PSPACE` on the p. 92 chain, and `SPACE(n+1) ≠ NP`
([AB09, Exercise 3.2], stated with the positive normalization). The universal
machine statement has a forward clause with the addend-free bound `C · s`;
the hierarchy uses a fixed self-application universal machine inside a
space-bounded configuration window.

## Design

* **Constant-factor overhead is the point** ([AB09]: "one can have a
  universal TM using only a constant factor of space overhead, and hence we
  don't need the logarithmic term of Theorem 3.1"): the hierarchy hypothesis
  below is eventual domination of every constant multiple — no square, no
  log — in contrast to the received `f²` time hierarchy.
* **The space-universal machine** reuses the fixed code scheme
  `Complexity.TimeHierarchy.code` (one-work-tape binary codes) and the layout
  `⟨bits s, ⟨α, x⟩⟩`, and keeps only Exercise 4.1's forward clause: a run of
  the coded machine within `s` work cells is reproduced, output included,
  within constant-factor space. Overruns and divergence are unconstrained, so
  the machine tests no budget, runs no clock and replays nothing. Its space
  bound is Exercise 4.1's `C_α · t`, with no addend: the simulated input, a
  suffix of its input, is read through the bounded-prefix ruler device
  (`Turing.exists_rulerHostTM`), a unary ruler of the header's length, which
  the bound absorbs because every qualifying run visits a cell.
* **The hierarchy takes the window route**: the
  diagonalizer runs one fixed self-application universal machine `U₀` in a
  window of radius `a · g(n)` on the configuration-record rows
  (`Build/CfgRecord.lean`, `Build/RecordTable.lean`), stopped by a
  configuration-count clock, and flips its verdict. The window, not `U₀`'s
  code-dependent constant, bounds the diagonalizer's space. The chapter-1
  interpreter (`Turing.universalInterpreter`) serves neither machine: it
  tracks the simulated input head in unary on its fourth tape, which uses one
  plus the largest simulated input position reached, `Θ(n + 1)` cells on a
  full scan, so it cannot guarantee `O(S(n))` space uniformly for sublinear
  `S`.
* **Both bounds space-constructible**, as in the book; `g`'s witness drives
  the window radius, and of `f` the proof uses only the
  bundled floor `1 ≤ logSpace n ≤ f n`.
* The `SpaceComplexity.lean` facade imports this module.

## Main results

* `Complexity.space_universal` — [AB09, Exercise 4.1], forward clause, with the
  addend-free bound `C · s`; proved by the ruler-hosted suffix assembly.
* `Complexity.space_hierarchy` — [AB09, Theorem 4.8].
* `Complexity.LOGSPACE_ssubset_PSPACE` — `L ⊊ PSPACE` on the p. 92 chain.
* `Complexity.SPACE_linear_ne_NP` — [AB09, Exercise 3.2], normalized.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.3, Theorem 4.8, Exercise 4.1;
  Exercise 3.2; [SHL65] through [AB09].)
-/

namespace Complexity

open Turing

/-! ### The space-universal machine: private assembly glue

The fixed prefix (budget header and ruler, the hosted startup with its return, the ruler-end
seek and correction, the code header scan and the rewind) and its pieces, the hosted forwarding
loop with its per-tape ledger, and the startup–loop seam at the last-ruler endpoint, consumed only
by `Complexity.space_universal`. -/

/-- Embedding a configuration into the same number of tapes along `Fin.castLEEmb`, with a
blank frame and no prior output, gives it back (`Turing.embedEmitCfg_eq`). -/
private theorem f6_full_embed {m : ℕ} {Q : Type} {z : List Bool} (c : Cfg m Bool Q z) :
    embedEmitCfg (Fin.castLEEmb (le_refl m)) (fun _ _ => none) (fun _ => 0) [] c = c := by
  apply embedEmitCfg_eq
  · rfl
  · rfl
  · exact List.nil_append _
  · intro i
    exact ⟨rfl, rfl⟩
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)

/-- One seam of the prefix: the public `Turing.seamCompTM_step` supplies the run, endpoint
control and first-return cut. -/
private theorem f6_seam {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] {x : List Bool}
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry q₂ : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₃ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) (hq : c₃.state = some q₂)
    (hcut₂ : ∀ t < T₂, (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) (T₁ + 1 + T₂) =
        c₃.mapState Sum.inr ∧
      (c₃.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).state = some (Sum.inr q₂) ∧
      ∀ t < T₁ + 1 + T₂,
        ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
          some (Sum.inr q₂) := by
  exact seamCompTM_step M₁ exit M₂ entry q₂ h₁ hexit hcut h₂ hq hcut₂

/-- The startup of `Turing.exists_selfStartupTM`, seamed at its exit to a one-step stationary
silent halt leaf, first halts at `T + 2` on `⟨α, w⟩` for every suffix `w`, with the startup's
installed bank, input head `1`, every head at `0` and empty output ([AB09, Exercise 4.1]: the
universal machine's preparation of its work tapes). The leaf is the one-state machine whose
transition halts in place; no catalog row is a single halting step.

**Proof sketch.** The public seam run composes the startup's endpoint and exit cut with the
leaf's one step (`Turing.FinTM.controlAction_apply`). At `T + 1` the dispatch step has entered
the leaf's live control (`Turing.seamCompTM_runFrom_right`), so the composite is live at every
time up to `T + 1` (`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`). -/
private theorem f6_native_halt (c : EffectiveMachineCode) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (A : MultiTapeTM (K + 3) Bool (P ⊕ Unit)),
      ∀ α : List Bool, ∃ T : ℕ, ∀ w : List Bool,
        A.runFrom (A.initCfg (pairEncode α w)) (T + 2) =
          ⟨none, 1,
            fun j => if j = 1 then FinTM.bufferTape (tableBitsK (c.decode α).tm.tr)
              else if j = 2 then fun p => FinTM.bufferTape (unaryFin (c.decode α).tm.q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T + 2, (A.runFrom (A.initCfg (pairEncode α w)) u).state ≠ none) := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTM c
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  let leaf : MultiTapeTM (K + 3) Bool Unit :=
    ⟨(), fun _ _ _ => FinTM.controlAction 0 none⟩
  let A : MultiTapeTM (K + 3) Bool (P ⊕ Unit) :=
    {seamCompTM R exit leaf () with q₀ := Sum.inl R.q₀}
  have hinit (y : List Bool) : A.initCfg y = (R.initCfg y).mapState Sum.inl :=
    MultiTapeTM.initCfg_eq_mapState R A Sum.inl rfl y
  have hrun {y : List Bool} (d : Cfg (K + 3) Bool (P ⊕ Unit) y) (t : ℕ) :
      A.runFrom d t = (seamCompTM R exit leaf ()).runFrom d t :=
    MultiTapeTM.runFrom_with_q₀ _ _ _ _
  have hleaf {y : List Bool} (d : Cfg (K + 3) Bool Unit y) (hs : d.state = some ()) :
      leaf.runFrom d 1 = {d with state := none} := by
    rw [MultiTapeTM.runFrom_one,
      MultiTapeTM.step_of_some hs]
    change (FinTM.controlAction 0 none).apply d = _
    rw [FinTM.controlAction_apply, moveInputPos_zero]
  refine ⟨K, P, fP, dP, A, fun α => ?_⟩
  obtain ⟨T, _B, hα⟩ := hR α
  refine ⟨T, fun w => ?_⟩
  obtain ⟨hr, hcut, _hout, _hspace⟩ := hα w
  let d : Cfg (K + 3) Bool P (pairEncode α w) :=
    ⟨some exit, 1,
      fun j => if j = 1 then FinTM.bufferTape (tableBitsK (c.decode α).tm.tr)
        else if j = 2 then fun p => FinTM.bufferTape (unaryFin (c.decode α).tm.q₀) (p - 2)
        else fun _ => none,
      fun _ => 0, []⟩
  have hd : d.state = some exit := rfl
  have hs : (d.mapState (fun _ => ())).state = some () := by
    rw [Cfg.mapState_state, hd, Option.map_some]
  have hr' : R.runFrom (R.initCfg (pairEncode α w)) T = d := hr
  have hfinal : A.runFrom (A.initCfg (pairEncode α w)) (T + 2) =
      ({d.mapState (fun _ => ()) with state := none}).mapState Sum.inr := by
    rw [hinit, hrun]
    exact seamCompTM_run_ofCfg R exit leaf () hr' hd hcut (hleaf _ hs)
  refine ⟨?_, fun u hu => ?_⟩
  · rw [hfinal]
    refine Cfg.mapState_eq_of_fields _ _ _ rfl (Cfg.mapState_inputPos (fun _ : P => ()) d) ?_ ?_
      (Cfg.mapState_output (fun _ : P => ()) d)
    · funext i p
      exact Cfg.mapState_workTapes (fun _ : P => ()) d i p
    · funext i
      exact Cfg.mapState_workTapePos (fun _ : P => ()) d i
  · have hdispatch := seamCompTM_runFrom_right R exit leaf () hr' hd hcut 0
    have hdispatch' : (seamCompTM R exit leaf ()).runFrom
        ((R.initCfg (pairEncode α w)).mapState Sum.inl) (T + 1) =
        (d.mapState (fun _ => ())).mapState Sum.inr := by
      simpa only [Nat.add_zero, MultiTapeTM.runFrom_zero] using hdispatch
    have hlive : (A.runFrom (A.initCfg (pairEncode α w)) (T + 1)).state ≠ none := by
      rw [hinit, hrun, hdispatch', Cfg.mapState_state, hs, Option.map_some]
      exact Option.some_ne_none _
    exact MultiTapeTM.runFrom_state_ne_none_of_le A _ (T + 1) hlive u (by omega)

/-- The first prefix phase: from the physical start, `Turing.headerRulerTM` on the last tape
reads the budget header `pairEncode u v`, leaves the ruler `true^ℓ` (`ℓ = 2|u| + 2`) rewound to
its first cell and the input head just past the header, every other tape blank, at a first
return to its exit ([AB09, Exercise 4.1]).

**Proof sketch.** Instantiate `Turing.headerRulerTM_run` at offset `0` from the initial
configuration of the scan's control, whose tapes are blank and heads at `0`, and normalize its
endpoint through the initialization field equations. -/
private theorem f6_header (K : ℕ) (u v : List Bool) :
    let z := pairEncode u v
    let ℓ := 2 * u.length + 2
    let r : Fin (K + 4) := Fin.last (K + 3)
    let e : Cfg (K + 4) Bool (Fin 4 ⊕ RewindPhase) z :=
      ⟨some (Sum.inr .done), ⟨ℓ + 1, by
        show 2 * u.length + 2 + 1 < (pairEncode u v).length + 2
        have := length_pairEncode u v; omega⟩,
        Function.update (fun _ _ => none) r (FinTM.bufferTape (List.replicate ℓ true)),
        fun _ => 0, []⟩
    (headerRulerTM r).runFrom ((Cfg.init (0 : Fin 4) z).mapState Sum.inl) (2 * ℓ + 3) = e ∧
      ∀ t < 2 * ℓ + 3, ((headerRulerTM r).runFrom
        ((Cfg.init (0 : Fin 4) z).mapState Sum.inl) t).state ≠ some (Sum.inr .done) := by
  intro z ℓ r e
  let d : Cfg (K + 4) Bool (Fin 4) z := Cfg.init 0 z
  have hpos : d.inputPos.val = 1 + 0 := by
    change (Cfg.init (0 : Fin 4) z : Cfg (K + 4) Bool (Fin 4) z).inputPos.val = 1 + 0
    rw [Cfg.init_inputPos]; rfl
  have hstate : d.state = some 0 := Cfg.init_state _ _
  have hblank (a : ℤ) : d.workTapes r a = none := by
    change (Cfg.init (0 : Fin 4) z : Cfg (K + 4) Bool (Fin 4) z).workTapes r a = none
    rw [Cfg.init_workTapes]
  obtain ⟨hrow, hcut⟩ := headerRulerTM_run r d 0 hpos hstate u v
    (by rw [List.drop_zero]) hblank
  have hw : d.workTapes = fun _ _ => none := by
    funext j a
    change (Cfg.init (0 : Fin 4) z : Cfg (K + 4) Bool (Fin 4) z).workTapes j a = none
    rw [Cfg.init_workTapes]
  have hh : d.workTapePos = fun _ => 0 := by
    funext j
    change (Cfg.init (0 : Fin 4) z : Cfg (K + 4) Bool (Fin 4) z).workTapePos j = 0
    rw [Cfg.init_workTapePos]
  have ho : d.output = [] := Cfg.init_output _ _
  have hip : d.inputPos.val = 1 := by simpa only [Nat.add_zero] using hpos
  refine ⟨?_, hcut⟩
  simpa only [e, ℓ, hw, hh, ho, hip, Nat.cast_zero, sub_zero, Nat.one_add] using hrow

/-- Relabelling a literal configuration relabels only its control
(`Turing.Cfg.mapState_eq_of_fields`). -/
private theorem f6_mapState_mk {k : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (q : Option S) (i : Fin (x.length + 2)) (w : Fin k → ℤ → Option Bool) (h : Fin k → ℤ)
    (o : List Bool) :
    (⟨q, i, w, h, o⟩ : Cfg k Bool S x).mapState f = ⟨q.map f, i, w, h, o⟩ :=
  Cfg.mapState_eq_of_fields _ f _ rfl rfl rfl rfl rfl

/-- The second prefix phase: a machine `M` on `K + 3` tapes, hosted on the suffix by the
ruler device `Turing.exists_rulerHostTM` and returned by the identity returning embedding
`Turing.embedEmitRetTM`. If `M` first halts at `T` from its initial configuration on `y` with
data `bank`, heads `0` and empty output, then from the first header's endpoint on
`pairEncode u y` (control relabelled to the host's entry) the returned host reaches the live
return anchor at some `t' ≤ C (ℓ + 1) T`, not earlier, with `bank`, the ruler `true^ℓ` last,
every head at `0`, input head `ℓ + 1` and empty output ([AB09, Exercise 4.1]: the simulated input
is a suffix of the input).

**Proof sketch.** The header endpoint relabelled at the host's entry is the ruler host's
presentation of `M`'s initial configuration (pairing geometry, field equations). The host's
endpoint at `T` is halted and its none-liveness clause gives liveness before `t'`; the returning
embedding turns that first halt into the live anchor at the same time, with its strict cut, and
its endpoint fields are the host presentation's of `M`'s halted configuration. -/
private theorem f6_hosted {K : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (M : MultiTapeTM (K + 3) Bool S) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : MultiTapeTM (K + 4) Bool Q)
      (inj : S → Bool → Q) (C : ℕ),
      ∀ (u y : List Bool) (bank : Fin (K + 3) → ℤ → Option Bool) (T : ℕ) {R : Type} (q : R),
        M.runFrom (M.initCfg y) T = ⟨none, 1, bank, fun _ => 0, []⟩ →
        (∀ v < T, (M.runFrom (M.initCfg y) v).state ≠ none) →
        let ℓ := 2 * u.length + 2
        let hp : ℓ + 1 < (pairEncode u y).length + 2 := by
          have := length_pairEncode u y; omega
        let e₁ : Cfg (K + 4) Bool R (pairEncode u y) := ⟨some q, ⟨ℓ + 1, hp⟩,
          Function.update (fun _ _ => none) (Fin.last (K + 3))
            (FinTM.bufferTape (List.replicate ℓ true)), fun _ => 0, []⟩
        let e₂ : Cfg (K + 4) Bool (Q ⊕ Unit) (pairEncode u y) :=
          ⟨some (Sum.inr ()), ⟨ℓ + 1, hp⟩,
            Fin.lastCases (FinTM.bufferTape (List.replicate ℓ true)) bank, fun _ => 0, []⟩
        ∃ t', t' ≤ C * (ℓ + 1) * T ∧
          (embedEmitRetTM (Fin.castLEEmb (le_refl (K + 4))) H).runFrom
            (e₁.mapState fun _ => Sum.inl (inj M.q₀ false)) t' = e₂ ∧
          ∀ v < t', ((embedEmitRetTM (Fin.castLEEmb (le_refl (K + 4))) H).runFrom
            (e₁.mapState fun _ => Sum.inl (inj M.q₀ false)) v).state ≠ some (Sum.inr ()) := by
  classical
  obtain ⟨Q, fQ, dQ, H, inj, C, _, hH⟩ := exists_rulerHostTM M
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  refine ⟨Q, fQ, dQ, H, inj, C, ?_⟩
  intro u y bank T R q hrun hlive ℓ hp e₁ e₂
  have hz : (pairEncode u y).length = ℓ + y.length := length_pairEncode u y
  have hℓ : 0 < ℓ := Nat.succ_pos _
  have hdrop : (pairEncode u y).drop ℓ = y := pairEncode_drop u y
  have hc : (M.initCfg y).state = some M.q₀ := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
  have hci : (M.initCfg y).inputPos.val = 1 := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_inputPos]; rfl
  obtain ⟨t', _, hhi, ⟨b', _, hend⟩, hinner, _, _, _⟩ :=
    hH ℓ hz hℓ hdrop (FinTM.bufferTape (List.replicate ℓ true)) 0
      (fun p _ _ => by rw [zero_add]) (M.initCfg y) false
      (by rw [hci]; exact ⟨fun h => Bool.noConfusion h, fun h => absurd h Nat.one_ne_zero⟩) T
  let d := rulerHostCfg ℓ hz ((M.initCfg y).state.map fun q => inj q false) (M.initCfg y)
    (FinTM.bufferTape (List.replicate ℓ true)) 0
  have hdlive : d.state ≠ none := by
    rw [rulerHostCfg_state, hc, Option.map_some]; exact Option.some_ne_none _
  have hHlive : ∀ v < t', (H.runFrom d v).state ≠ none := hinner hlive
  have hHhalt : (H.runFrom d t').state = none := by
    rw [hend, rulerHostCfg_state, hrun]; rfl
  obtain ⟨_, hret, hcut⟩ := embedEmitRetTM_run (Fin.castLEEmb (le_refl (K + 4))) H
    (fun _ _ => none) (fun _ => 0) [] d t' hdlive hHlive hHhalt
  have hhand : e₁.mapState (fun _ => inj M.q₀ false) = d := by
    refine Cfg.mapState_eq_of_fields e₁ _ d ?_ ?_ ?_ ?_ ?_
    · rw [rulerHostCfg_state, hc]; rfl
    · apply Fin.ext
      rw [(rulerHostCfg_fields ℓ hz _ (M.initCfg y) _ 0).1, hci]
    · funext j p
      rw [rulerHostCfg_workTapes]
      change Function.update (fun _ _ => none) (Fin.last (K + 3))
          (FinTM.bufferTape (List.replicate ℓ true)) j p =
        Fin.lastCases (motive := fun _ => ℤ → Option Bool)
          (FinTM.bufferTape (List.replicate ℓ true)) (M.initCfg y).workTapes j p
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Function.update_self, Fin.lastCases_last]
      · rw [Function.update_of_ne (Fin.castSucc_ne_last i), Fin.lastCases_castSucc,
          MultiTapeTM.initCfg_eq, Cfg.init_workTapes]
    · funext j
      rw [rulerHostCfg_workTapePos]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
    · rw [rulerHostCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output]
  have hstart : e₁.mapState (fun _ => Sum.inl (inj M.q₀ false)) =
      (embedEmitCfg (Fin.castLEEmb (le_refl (K + 4))) (fun _ _ => none) (fun _ => 0) []
        d).mapState (Sum.inl : Q → Q ⊕ Unit) := by
    rw [f6_full_embed, ← hhand, Cfg.mapState_mapState]
    rfl
  refine ⟨t', hhi, ?_, ?_⟩
  · rw [hstart, hret, f6_full_embed, hend, hrun]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (rulerHostCfg ℓ hz _ _ (FinTM.bufferTape (List.replicate ℓ true)) 0).inputPos.val =
        ℓ + 1
      rw [(rulerHostCfg_fields ℓ hz _ _ _ 0).1]
      rfl
    · funext j p
      change (rulerHostCfg ℓ hz _ _ (FinTM.bufferTape (List.replicate ℓ true)) 0).workTapes j p =
        _
      rw [rulerHostCfg_workTapes]
    · funext j
      change (rulerHostCfg ℓ hz _ _ (FinTM.bufferTape (List.replicate ℓ true)) 0).workTapePos j =
        0
      rw [rulerHostCfg_workTapePos]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc]
    · change (rulerHostCfg ℓ hz _ _ (FinTM.bufferTape (List.replicate ℓ true)) 0).output = []
      rw [rulerHostCfg_output]
  · rw [hstart]
    exact hcut

/-- The ruler-head phases of the prefix, by catalog rows on the last (ruler) tape, each from a
literal configuration with the ruler `true^n` and the bank `bank` ([AB09, Exercise 4.1]):
the skip `Turing.skipTM` from the ruler's first cell stops one cell past the ruler (third
phase); the walk `Turing.walkTM` over the empty word, leftwards, moves the head back by one cell,
so that the next scan starts at the ruler's end (fourth phase); the rewind `Turing.rewindTM`
returns the head from the end of the whole ruler `true^N` to its first cell (sixth phase). Each
reaches its exit control first at the stated time and changes only the control and the ruler
head.

**Proof sketch.** Rewrite each relabelled start as a literal (`f6_mapState_mk`) and apply the
row's public contract (`Turing.skipTM_run_ofCfg`, `Turing.walkTM_run_ofCfg`,
`Turing.rewindTM_run_ofCfg`) with the ruler window read through `Turing.FinTM.bufferTape_eq`; the
walk's single read is the blank after the ruler. The endpoints differ from the targets only in
the ruler head, `ℓ + 1`, `ℓ + 1 - 1` and `N - N`. -/
private theorem f6_ruler_moves {K : ℕ} {z : List Bool} {S₃ S₄ S₆ : Type}
    (bank : Fin (K + 3) → ℤ → Option Bool) (ℓ N : ℕ) (hp : ℓ + 1 < z.length + 2)
    (hN : N + 1 < z.length + 2) (q₃ : S₃) (q₄ : S₄) (q₆ : S₆) :
    let r : Fin (K + 4) := Fin.last (K + 3)
    let W := Fin.lastCases (FinTM.bufferTape (List.replicate ℓ true)) bank
    let WN := Fin.lastCases (FinTM.bufferTape (List.replicate N true)) bank
    let e₃ : Cfg (K + 4) Bool S₃ z := ⟨some q₃, ⟨ℓ + 1, hp⟩, W, fun _ => 0, []⟩
    let f₃ : Cfg (K + 4) Bool SeekPhase z := ⟨some .done, ⟨ℓ + 1, hp⟩, W,
      Function.update (fun _ => (0 : ℤ)) r ((ℓ : ℤ) + 1), []⟩
    let e₄ : Cfg (K + 4) Bool S₄ z := ⟨some q₄, ⟨ℓ + 1, hp⟩, W,
      Function.update (fun _ => (0 : ℤ)) r ((ℓ : ℤ) + 1), []⟩
    let f₄ : Cfg (K + 4) Bool SeekPhase z := ⟨some .done, ⟨ℓ + 1, hp⟩, W,
      Function.update (fun _ => (0 : ℤ)) r (ℓ : ℤ), []⟩
    let e₆ : Cfg (K + 4) Bool S₆ z := ⟨some q₆, ⟨N + 1, hN⟩, WN,
      Function.update (fun _ => (0 : ℤ)) r (N : ℤ), []⟩
    let f₆ : Cfg (K + 4) Bool RewindPhase z := ⟨some .done, ⟨N + 1, hN⟩, WN, fun _ => 0, []⟩
    ((skipTM (K + 4) r).runFrom (e₃.mapState fun _ => .run) (ℓ + 1) = f₃ ∧
      ∀ t < ℓ + 1, ((skipTM (K + 4) r).runFrom (e₃.mapState fun _ => .run) t).state ≠
        some .done) ∧
    ((walkTM (Symbol := Bool) (K + 4) r (· = r) .neg).runFrom (e₄.mapState fun _ => .run) 1 =
        f₄ ∧
      ∀ t < 1, ((walkTM (Symbol := Bool) (K + 4) r (· = r) .neg).runFrom
        (e₄.mapState fun _ => .run) t).state ≠ some .done) ∧
    ((rewindTM (K + 4) r).runFrom (e₆.mapState fun _ => .start) (N + 2) = f₆ ∧
      ∀ t < N + 2, ((rewindTM (K + 4) r).runFrom (e₆.mapState fun _ => .start) t).state ≠
        some .done) := by
  intro r W WN e₃ f₃ e₄ f₄ e₆ f₆
  have hW (a : ℤ) : W (Fin.last (K + 3)) a = FinTM.bufferTape (List.replicate ℓ true) a := by
    simp only [W, Fin.lastCases_last]
  have hWN (a : ℤ) : WN (Fin.last (K + 3)) a = FinTM.bufferTape (List.replicate N true) a := by
    simp only [WN, Fin.lastCases_last]
  refine ⟨?_, ?_, ?_⟩
  · -- the skip
    let d : Cfg (K + 4) Bool SeekPhase z := ⟨some .run, ⟨ℓ + 1, hp⟩, W, fun _ => 0, []⟩
    rw [show e₃.mapState (fun _ => SeekPhase.run) = d from f6_mapState_mk _ _ _ _ _ _]
    obtain ⟨run, cut, _⟩ := skipTM_run_ofCfg r (List.replicate ℓ true) d rfl
      (fun p _ _ => (congrArg (W (Fin.last (K + 3))) (zero_add p)).trans (hW p))
    rw [List.length_replicate] at run cut
    exact ⟨run.trans (by simp only [d, f₃, zero_add]), cut⟩
  · -- the walk back over the blank after the ruler
    let d : Cfg (K + 4) Bool SeekPhase z := ⟨some .run, ⟨ℓ + 1, hp⟩, W,
      Function.update (fun _ => (0 : ℤ)) r ((ℓ : ℤ) + 1), []⟩
    rw [show e₄.mapState (fun _ => SeekPhase.run) = d from f6_mapState_mk _ _ _ _ _ _]
    obtain ⟨run, cut, _⟩ := walkTM_run_ofCfg r (· = r) rfl SignType.neg ([] : List Bool) d rfl
      (fun p hp => by
        rw [Nat.le_zero.mp hp]
        change W (Fin.last (K + 3)) (Function.update (fun _ => (0 : ℤ)) r ((ℓ : ℤ) + 1) r +
          ((SignType.neg : SignType) : ℤ) * ((0 : ℕ) : ℤ)) = _
        rw [hW, Function.update_self, Nat.cast_zero, mul_zero, add_zero, FinTM.bufferTape_eq,
          FinTM.bufferTape_eq, if_pos (by omega), if_pos le_rfl, List.getElem?_replicate,
          if_neg (by omega), List.getElem?_nil])
    have hhead : (fun j => d.workTapePos j + if j = r then
        ((SignType.neg : SignType) : ℤ) * ((([] : List Bool).length + 1 : ℕ) : ℤ) else 0) =
        Function.update (fun _ => (0 : ℤ)) r (ℓ : ℤ) := by
      funext j
      by_cases hj : j = r
      · subst hj
        simp only [d, Function.update_self, if_true, List.length_nil, Nat.zero_add,
          Nat.cast_one, mul_one, SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one]
        omega
      · simp only [d, Function.update_of_ne hj, if_neg hj, add_zero]
    exact ⟨run.trans (by rw [hhead]), cut⟩
  · -- the final rewind of the whole ruler
    let d : Cfg (K + 4) Bool RewindPhase z := ⟨some .start, ⟨N + 1, hN⟩, WN,
      Function.update (fun _ => (0 : ℤ)) r (N : ℤ), []⟩
    rw [show e₆.mapState (fun _ => RewindPhase.start) = d from f6_mapState_mk _ _ _ _ _ _]
    have hhead : d.workTapePos r = (N : ℤ) := Function.update_self r (N : ℤ) (fun _ => (0 : ℤ))
    obtain ⟨run, cut, _⟩ := rewindTM_run_ofCfg r (List.replicate N true) N
      (by rw [List.length_replicate]) d rfl
      (fun p _ _ => by rw [hhead, sub_self, zero_add]; exact hWN p)
    have hheads : Function.update d.workTapePos r (d.workTapePos r - N) = fun _ => (0 : ℤ) := by
      rw [hhead, sub_self]
      exact Function.update_idem _ _ _ |>.trans (Function.update_eq_self _ _)
    exact ⟨run.trans (by rw [hheads]), cut⟩

/-- The fifth prefix phase: from the ruler's end, `Turing.headerScanTM` reads the code header
`pairEncode u v` and extends the ruler `true^ℓ` to `true^(ℓ + ℓ₂)`, `ℓ₂ = 2|u| + 2`, at a first
return, with the input head `ℓ₂` cells further ([AB09, Exercise 4.1]).

**Proof sketch.** `Turing.headerScanTM_run` from input offset `ℓ`; the extended ruler is
`Turing.headerScanCfg_ruler` at the existing prefix length `ℓ`, read from the ruler's first
cell `0`; every other tape and the output are unchanged. -/
private theorem f6_scan {K : ℕ} {z : List Bool} {S : Type}
    (bank : Fin (K + 3) → ℤ → Option Bool) (ℓ : ℕ) (hp : ℓ + 1 < z.length + 2) (q : S)
    (u v : List Bool) (hz : z.drop ℓ = pairEncode u v) :
    let ℓ₂ := 2 * u.length + 2
    let r : Fin (K + 4) := Fin.last (K + 3)
    let hp' : ℓ + ℓ₂ + 1 < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    let e : Cfg (K + 4) Bool S z := ⟨some q, ⟨ℓ + 1, hp⟩,
      Fin.lastCases (FinTM.bufferTape (List.replicate ℓ true)) bank,
      Function.update (fun _ => (0 : ℤ)) r (ℓ : ℤ), []⟩
    let f : Cfg (K + 4) Bool (Fin 4) z := ⟨some 3, ⟨ℓ + ℓ₂ + 1, hp'⟩,
      Fin.lastCases (FinTM.bufferTape (List.replicate (ℓ + ℓ₂) true)) bank,
      Function.update (fun _ => (0 : ℤ)) r ((ℓ + ℓ₂ : ℕ) : ℤ), []⟩
    (headerScanTM r).runFrom (e.mapState fun _ => 0) ℓ₂ = f ∧
      ∀ t < ℓ₂, ((headerScanTM r).runFrom (e.mapState fun _ => 0) t).state ≠ some 3 := by
  intro ℓ₂ r hp' e f
  have hpd : (e.mapState fun _ => (0 : Fin 4)).inputPos.val = 1 + ℓ := by
    rw [Cfg.mapState_inputPos]
    change ℓ + 1 = 1 + ℓ
    omega
  have hqd : (e.mapState fun _ => (0 : Fin 4)).state = some 0 := by
    rw [Cfg.mapState_state]; rfl
  obtain ⟨run, cut, _⟩ := headerScanTM_run r (e.mapState fun _ => (0 : Fin 4)) ℓ hpd hqd u v hz
  refine ⟨run.trans ?_, cut⟩
  have hhead : (e.mapState fun _ => (0 : Fin 4)).workTapePos r = (ℓ : ℤ) := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self r (ℓ : ℤ) (fun _ => (0 : ℤ))
  apply Cfg.ext
  · rw [headerScanCfg_state]
  · apply Fin.ext
    rw [headerScanCfg_inputPos]
    change (e.mapState fun _ => (0 : Fin 4)).inputPos.val + ℓ₂ = ℓ + ℓ₂ + 1
    rw [hpd]
    omega
  · funext j a
    by_cases hj : j = r
    · rw [hj]
      have hpre (b : ℤ) : (e.mapState fun _ => (0 : Fin 4)).workTapes r
          ((e.mapState fun _ => (0 : Fin 4)).workTapePos r - (ℓ : ℤ) + b) =
          FinTM.bufferTape (List.replicate ℓ true) b := by
        rw [hhead, sub_self, zero_add, Cfg.mapState_workTapes]
        change Fin.lastCases (motive := fun _ => ℤ → Option Bool)
          (FinTM.bufferTape (List.replicate ℓ true)) bank (Fin.last (K + 3)) b = _
        rw [Fin.lastCases_last]
      have h := headerScanCfg_ruler r (e.mapState fun _ => (0 : Fin 4)) 3
        (2 * u.length + 2) (by
          have h : ℓ + (2 * u.length + 2) + 1 < z.length + 2 := hp'
          rw [hpd]; omega) ℓ hpre a
      rw [hhead, sub_self, zero_add] at h
      rw [h]
      change _ = Fin.lastCases (motive := fun _ => ℤ → Option Bool)
        (FinTM.bufferTape (List.replicate (ℓ + ℓ₂) true)) bank (Fin.last (K + 3)) a
      rw [Fin.lastCases_last]
    · rw [headerScanCfg_workTapes, Function.update_of_ne hj, Cfg.mapState_workTapes]
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      change Fin.lastCases (motive := fun _ => ℤ → Option Bool) _ bank i.castSucc a =
        Fin.lastCases (motive := fun _ => ℤ → Option Bool) _ bank i.castSucc a
      rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
  · funext j
    rw [headerScanCfg_workTapePos]
    by_cases hj : j = r
    · rw [hj, Function.update_self, hhead]
      change _ = Function.update (fun _ => (0 : ℤ)) r ((ℓ + ℓ₂ : ℕ) : ℤ) r
      rw [Function.update_self]
      push_cast
      rfl
    · rw [Function.update_of_ne hj, Cfg.mapState_workTapePos]
      change Function.update (fun _ => (0 : ℤ)) r (ℓ : ℤ) j =
        Function.update (fun _ => (0 : ℤ)) r ((ℓ + ℓ₂ : ℕ) : ℤ) j
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · rw [headerScanCfg_output, Cfg.mapState_output]

/-- **The physical prefix.** One finite control on `K + 4` tapes, chosen before
the code: scan the budget header writing the ruler and rewind it; run the native startup (seamed
to its halt leaf) on the suffix through the ruler host and return; skip to the ruler end and
correct one cell; scan the code header extending the ruler; rewind the whole ruler. For every
code `α` its run on `⟨u, ⟨α, x⟩⟩` reaches the installed bank with the ruler `true^ℓ` at a first
return to `finish`, within a time linear in `ℓ` with a per-code coefficient
([AB09, Exercise 4.1]).

**Proof sketch.** Six phase contracts give exact runs and first-return cuts between literal
configurations; five public seams compose them, each adding its dispatch step. The startup's
first halt is hosted and returned (`f6_hosted`); the initial configuration is the scan's,
relabelled. The time is the sum of the phase times. -/
private theorem f6_prefix (c : EffectiveMachineCode) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (A : MultiTapeTM (K + 4) Bool P) (finish : P) (C : ℕ),
      ∀ α : List Bool, ∃ T₀ : ℕ, ∀ u x : List Bool,
        let ℓ := (2 * u.length + 2) + (2 * α.length + 2)
        let z := pairEncode u (pairEncode α x)
        let hp : ℓ + 1 < z.length + 2 := by
          show (2 * u.length + 2) + (2 * α.length + 2) + 1 <
            (pairEncode u (pairEncode α x)).length + 2
          have h1 := length_pairEncode u (pairEncode α x)
          have h2 := length_pairEncode α x
          omega
        ∃ T : ℕ, T ≤ C * (ℓ + 1) * (T₀ + 2) + 4 * ℓ + 11 ∧
          A.runFrom (A.initCfg z) T =
            ⟨some finish, ⟨ℓ + 1, hp⟩,
              Fin.lastCases (FinTM.bufferTape (List.replicate ℓ true))
                (fun j => if j = 1 then FinTM.bufferTape (tableBitsK (c.decode α).tm.tr)
                  else if j = 2 then
                    fun p => FinTM.bufferTape (unaryFin (c.decode α).tm.q₀) (p - 2)
                  else fun _ => none),
              fun _ => 0, []⟩ ∧
          ∀ v < T, (A.runFrom (A.initCfg z) v).state ≠ some finish := by
  classical
  obtain ⟨K, P₀, fP₀, dP₀, A₁, hA₁⟩ := f6_native_halt c
  letI : Fintype P₀ := fP₀
  letI : DecidableEq P₀ := dP₀
  obtain ⟨Q₁, fQ₁, dQ₁, H₁, inj₁, C₁, hH₁⟩ := f6_hosted A₁
  letI : Fintype Q₁ := fQ₁
  letI : DecidableEq Q₁ := dQ₁
  let r : Fin (K + 4) := Fin.last (K + 3)
  let P2 := embedEmitRetTM (Fin.castLEEmb (le_refl (K + 4))) H₁
  let S2 := seamCompTM (headerRulerTM r) (Sum.inr RewindPhase.done) P2
    (Sum.inl (inj₁ A₁.q₀ false))
  let S3 := seamCompTM S2 (Sum.inr (Sum.inr ())) (skipTM (Symbol := Bool) (K + 4) r)
    SeekPhase.run
  let S4 := seamCompTM S3 (Sum.inr SeekPhase.done)
    (walkTM (Symbol := Bool) (K + 4) r (· = r) .neg) SeekPhase.run
  let S5 := seamCompTM S4 (Sum.inr SeekPhase.done) (headerScanTM r) (0 : Fin 4)
  let S6 := seamCompTM S5 (Sum.inr (3 : Fin 4)) (rewindTM (Symbol := Bool) (K + 4) r)
    RewindPhase.start
  let A : MultiTapeTM (K + 4) Bool _ :=
    { S6 with q₀ := Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 4)))))) }
  refine ⟨K, _, inferInstance, inferInstance, A, Sum.inr RewindPhase.done, C₁, fun α => ?_⟩
  obtain ⟨T₀, hT₀⟩ := hA₁ α
  refine ⟨T₀, fun u x => ?_⟩
  intro ℓ z hp
  obtain ⟨hrun₁, hlive₁⟩ := hT₀ x
  let bank : Fin (K + 3) → ℤ → Option Bool :=
    fun j => if j = 1 then FinTM.bufferTape (tableBitsK (c.decode α).tm.tr)
      else if j = 2 then fun p => FinTM.bufferTape (unaryFin (c.decode α).tm.q₀) (p - 2)
      else fun _ => none
  have hp₁ : 2 * u.length + 2 + 1 < z.length + 2 := by
    have h1 := length_pairEncode u (pairEncode α x)
    omega
  obtain ⟨h1, k1⟩ := f6_header K u (pairEncode α x)
  obtain ⟨t₂, ht₂, h2, k2⟩ := hH₁ u (pairEncode α x) bank (T₀ + 2)
    (Sum.inr RewindPhase.done : Fin 4 ⊕ RewindPhase) hrun₁ hlive₁
  obtain ⟨s2, _, c2⟩ := f6_seam (headerRulerTM r) _ P2 _ (Sum.inr ()) h1 rfl k1 h2 rfl k2
  replace s2 := s2.trans (f6_mapState_mk _ _ _ _ _ _)
  obtain ⟨⟨h3, k3⟩, ⟨h4, k4⟩, ⟨h6, k6⟩⟩ := f6_ruler_moves (z := z) bank (2 * u.length + 2) ℓ hp₁ hp
    (Sum.inr (Sum.inr ()) : (Fin 4 ⊕ RewindPhase) ⊕ (Q₁ ⊕ Unit))
    (Sum.inr SeekPhase.done : ((Fin 4 ⊕ RewindPhase) ⊕ (Q₁ ⊕ Unit)) ⊕ SeekPhase)
    (Sum.inr (3 : Fin 4) :
      ((((Fin 4 ⊕ RewindPhase) ⊕ (Q₁ ⊕ Unit)) ⊕ SeekPhase) ⊕ SeekPhase) ⊕ Fin 4)
  obtain ⟨s3, _, c3⟩ := f6_seam S2 _ (skipTM (Symbol := Bool) (K + 4) r) _ SeekPhase.done
    s2 rfl c2 h3 rfl k3
  replace s3 := s3.trans (f6_mapState_mk _ _ _ _ _ _)
  obtain ⟨s4, _, c4⟩ := f6_seam S3 _ (walkTM (Symbol := Bool) (K + 4) r (· = r) .neg) _
    SeekPhase.done s3 rfl c3 h4 rfl k4
  replace s4 := s4.trans (f6_mapState_mk _ _ _ _ _ _)
  obtain ⟨h5, k5⟩ := f6_scan (z := z) bank (2 * u.length + 2) hp₁
    (Sum.inr SeekPhase.done : (((Fin 4 ⊕ RewindPhase) ⊕ (Q₁ ⊕ Unit)) ⊕ SeekPhase) ⊕ SeekPhase)
    α x
    (pairEncode_drop u (pairEncode α x))
  obtain ⟨s5, _, c5⟩ := f6_seam S4 _ (headerScanTM r) _ (3 : Fin 4) s4 rfl c4 h5 rfl k5
  replace s5 := s5.trans (f6_mapState_mk _ _ _ _ _ _)
  obtain ⟨s6, _, c6⟩ := f6_seam S5 _ (rewindTM (Symbol := Bool) (K + 4) r) _ RewindPhase.done
    s5 rfl c5 h6 rfl k6
  replace s6 := s6.trans (f6_mapState_mk _ _ _ _ _ _)
  have hinit : A.initCfg z = ((((((Cfg.init (0 : Fin 4) z).mapState Sum.inl).mapState
      Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState Sum.inl := by
    rw [MultiTapeTM.initCfg_eq_mapState { headerScanTM r with q₀ := (0 : Fin 4) } A
      (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) rfl z,
      MultiTapeTM.initCfg_with_q₀]
    simp only [Cfg.mapState_mapState]
  have hrunA (t : ℕ) : A.runFrom (A.initCfg z) t = S6.runFrom (((((((Cfg.init (0 : Fin 4)
      z).mapState Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState
      Sum.inl).mapState Sum.inl) t :=
    (congrArg (fun d => A.runFrom d t) hinit).trans (MultiTapeTM.runFrom_with_q₀ _ _ _ _)
  refine ⟨_, ?_, (hrunA _).trans s6, fun v hv => by rw [hrunA]; exact c6 v hv⟩
  have hmono : C₁ * (2 * u.length + 2 + 1) * (T₀ + 2) ≤ C₁ * (ℓ + 1) * (T₀ + 2) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  omega


/-- **The hosted forwarding loop and its per-tape ledger.** The forwarding round loop of
`Turing.StepBlock.exists_forwardLoopTM` on the first three of `K + 3` bank tapes, hosted by the
ruler device: for every one-tape coded machine `M`
halting on `x` by `t`, started at the suffix presentation of the loop's initial encoding, the host
halts with `M`'s output, and every tape visits at most `s + (2D + 1) + ℓ + 3` cells, `s` the
source space and `D` a constant of `M`'s table ([AB09, Exercise 4.1]).

**Proof sketch.** Take the first source halt `t₀ ≤ t` (`StepBlock.forwardLoop_forward`); the loop
reaches the encoding of the halted source after `r` steps. The ruler host transports that run:
halt and output by the host endpoint, the bank's visited sets exactly, the ruler's within
`[-1, ℓ]`. Through the emitting embedding a selected tape has the loop's visited set: the
mirrored tape's lies in the source's (at most `s` cells), the two auxiliaries' in `[-D, D]`; an
unselected tape visits its initial cell only. -/
private theorem f6_loop (K : ℕ) :
    ∃ (Q V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : MultiTapeTM (K + 4) Bool V)
      (entry : Q) (inj : Q → Bool → V),
      ∀ {n : ℕ} (M : MultiTapeTM 1 Bool (Fin (n + 1))), ∃ D : ℕ,
        ∀ (x z : List Bool) (ℓ : ℕ) (hz : z.length = ℓ + x.length), 0 < ℓ → z.drop ℓ = x →
        ∀ t : ℕ, (M.runFrom (M.initCfg x) t).state = none →
          let ec := embedEmitCfg (Fin.castLEEmb (by omega : 3 ≤ K + 3)) (fun _ _ => none)
            (fun _ => 0) [] (StepBlock.forwardLoopCfg entry M (M.initCfg x))
          let c := rulerHostCfg ℓ hz (ec.state.map fun q => inj q false) ec
            (FinTM.bufferTape (List.replicate ℓ true)) 0
          ∃ t' : ℕ, (H.runFrom c t').state = none ∧
            (H.runFrom c t').output = (M.runFrom (M.initCfg x) t).output ∧
            ∀ i, H.spaceUsedByTape c t' i ≤
              M.spaceUsed (M.initCfg x) t + (2 * D + 1) + ℓ + 3 := by
  classical
  obtain ⟨QL, fQL, dQL, L, entry, CL, hL⟩ := StepBlock.exists_forwardLoopTM 1
  letI : Fintype QL := fQL
  letI : DecidableEq QL := dQL
  obtain ⟨V, fV, dV, H, inj, C, _, hH⟩ :=
    exists_rulerHostTM (embedEmitTM (Fin.castLEEmb (by omega : 3 ≤ K + 3)) L)
  refine ⟨QL, V, fV, dV, H, entry, inj, fun {n} M => ?_⟩
  refine ⟨50 * ((tableBitsK M.tr).length + 1) + CL, ?_⟩
  intro x z ℓ hz hℓ hdrop t hhalt ec c
  obtain ⟨cost, hlock, hcost, hledger⟩ := hL (x := x) M
  obtain ⟨t₀, ht₀, hfirst, _, hloop⟩ := StepBlock.forwardLoop_forward M L entry cost _ hlock
    (fun c hc => (hcost c hc).2) t hhalt
  obtain ⟨hmirror, haux⟩ := hledger (M.initCfg x) t₀ hfirst
  have hec := embedEmitCfg_forwardLoop_init (k := 1) (K := K) () entry M x
  have hecpos : ec.inputPos.val = 1 := by
    change (embedEmitCfg (Fin.castLEEmb (by omega : 1 + 2 ≤ K + (1 + 2))) (fun _ _ => none)
      (fun _ => 0) [] (StepBlock.forwardLoopCfg entry M (M.initCfg x))).inputPos.val = 1
    rw [hec, Cfg.mapState_inputPos]
    rfl
  obtain ⟨t', _, _, ⟨b', _, hend⟩, _, _, hbank, hruler⟩ := hH ℓ hz hℓ hdrop
    (FinTM.bufferTape (List.replicate ℓ true)) 0 (fun p _ _ => by rw [zero_add]) ec false
    (by rw [hecpos]; exact ⟨fun h => Bool.noConfusion h, fun h => absurd h Nat.one_ne_zero⟩)
    (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u))
  have hL' : (embedEmitTM (Fin.castLEEmb (by omega : 3 ≤ K + 3)) L).runFrom ec
      (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) =
      embedEmitCfg (Fin.castLEEmb (by omega : 3 ≤ K + 3)) (fun _ _ => none) (fun _ => 0) []
        (StepBlock.forwardLoopCfg entry M (M.runFrom (M.initCfg x) t)) := by
    rw [embedEmitTM_runFrom, hloop]
  have hfl := StepBlock.forwardLoopCfg_halt_iff entry M (M.runFrom (M.initCfg x) t)
  refine ⟨t', ?_, ?_, fun i => ?_⟩
  · rw [hend, rulerHostCfg_state, hL', embedEmitCfg_state, hfl.1.mpr hhalt, Option.map_none]
  · rw [hend, rulerHostCfg_output, hL', embedEmitCfg_output, List.nil_append, hfl.2]
  · rw [MultiTapeTM.spaceUsedByTape_eq_card]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h : (H.visitedByTapeHead c t' (Fin.last (K + 3))).card ≤
          ((0 : ℤ) + ℓ + 1 - (0 - 1)).toNat := by
        have h' := Finset.card_le_card hruler
        rwa [Int.card_Icc] at h'
      have he : ((0 : ℤ) + ℓ + 1 - (0 - 1)).toNat = ℓ + 2 := by omega
      omega
    · rw [hbank j]
      by_cases hj : j ∈ Set.range (Fin.castLEEmb (by omega : 3 ≤ K + 3))
      · obtain ⟨i', rfl⟩ := hj
        rw [(embedEmitTM_visitedByTapeHead _ L _ _ [] _ _ i').1]
        by_cases h0 : i'.val = 0
        · have hi' : i' = Fin.castAdd 2 (0 : Fin 1) := Fin.ext h0
          rw [hi']
          have hmono : M.visitedByTapeHead (M.initCfg x) t₀ 0 ⊆
              M.visitedByTapeHead (M.initCfg x) t 0 :=
            MultiTapeTM.visitedByTapeHead_mono M (M.initCfg x) ht₀ 0
          have hb := M.spaceUsedByTape_le_spaceUsed (M.initCfg x) t 0
          rw [MultiTapeTM.spaceUsedByTape_eq_card] at hb
          have := (Finset.card_le_card ((hmirror 0).trans hmono)).trans hb
          omega
        · have h := Finset.card_le_card (haux i' (by omega))
          rw [Int.card_Icc] at h
          omega
      · rw [(embedEmitTM_visitedByTapeHead_frame _ L _ _ [] _ _ j hj).1, Finset.card_singleton]
        omega

/-- The final loop configuration is the prefix endpoint relabelled at the host's entry: the
loop's three tapes are the first three of the `K + 3` bank tapes and the common ruler is last
([AB09, Exercise 4.1]).

**Proof sketch.** The embedded initial loop encoding is the startup's installed bank relabelled
(`Turing.embedEmitCfg_forwardLoop_init`); compare the ruler host's presentation of it field by
field (`Turing.rulerHostCfg_fields`), splitting the tape index into the bank and the last tape. -/
private theorem f6_last_ruler_layout (K n ℓ : ℕ) {P Q V : Type}
    (finish : P) (entry : Q) (inj : Q → Bool → V)
    (M : MultiTapeTM 1 Bool (Fin (n + 1))) (x z : List Bool)
    (hz : z.length = ℓ + x.length) :
    let σ : Fin 3 ↪ Fin (K + 3) := Fin.castLEEmb (by omega)
    let ec := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) []
      (StepBlock.forwardLoopCfg entry M (M.initCfg x))
    let bank : Cfg (K + 3) Bool P x :=
      ⟨some finish, 1,
        fun j => if j = 1 then FinTM.bufferTape (tableBitsK M.tr)
          else if j = 2 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
          else fun _ => none,
        fun _ => 0, []⟩
    let physical : Cfg ((K + 3) + 1) Bool P z :=
      ⟨some finish, ⟨ℓ + 1, by omega⟩,
        Fin.lastCases (FinTM.bufferTape (List.replicate ℓ true)) bank.workTapes,
        fun _ => 0, []⟩
    physical.mapState (fun _ => inj entry false) =
      rulerHostCfg ℓ hz (ec.state.map fun q => inj q false) ec
        (FinTM.bufferTape (List.replicate ℓ true)) 0 := by
  intro σ ec bank physical
  dsimp only [physical]
  have h1 (j : Fin (K + 3)) : (j = 1) ↔ j.val = 1 := by
    rw [Fin.ext_iff]
    change j.val = 1 % (K + 3) ↔ j.val = 1
    rw [Nat.mod_eq_of_lt (by omega : 1 < K + 3)]
  have h2 (j : Fin (K + 3)) : (j = 2) ↔ j.val = 2 := by
    rw [Fin.ext_iff]
    change j.val = 2 % (K + 3) ↔ j.val = 2
    rw [Nat.mod_eq_of_lt (by omega : 2 < K + 3)]
  have hbank : ec = bank.mapState (fun _ => entry) := by
    have h := embedEmitCfg_forwardLoop_init (k := 1) (K := K) finish entry M x
    simpa only [ec, bank, σ, h1, h2] using h
  refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
  · rw [rulerHostCfg_state, hbank, Cfg.mapState_state]
    all_goals rfl
  · apply Fin.ext
    rw [(rulerHostCfg_fields ℓ hz _ ec _ 0).1, hbank, Cfg.mapState_inputPos]
    simp only [bank, Fin.val_one]
  · funext i p
    rw [rulerHostCfg_workTapes, hbank]
    change Fin.lastCases (motive := fun _ => ℤ → Option Bool)
        (FinTM.bufferTape (List.replicate ℓ true)) bank.workTapes i p =
      Fin.lastCases (motive := fun _ => ℤ → Option Bool)
        (FinTM.bufferTape (List.replicate ℓ true)) (bank.mapState (fun _ => entry)).workTapes i p
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc, Cfg.mapState_workTapes]
  · funext i
    rw [rulerHostCfg_workTapePos, hbank]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]
    · rw [Fin.lastCases_castSucc, Cfg.mapState_workTapePos]
  · rw [rulerHostCfg_output, hbank, Cfg.mapState_output]

/-- Equality induction transports an initialized run along a tape-count equation. -/
private theorem f6_cast_init_run {P : Type} {m n : ℕ} (h : m = n)
    (A : MultiTapeTM m Bool P) (z : List Bool) (t : ℕ) :
    (h ▸ A : MultiTapeTM n Bool P).runFrom
      ((h ▸ A : MultiTapeTM n Bool P).initCfg z) t =
        (h ▸ A.runFrom (A.initCfg z) t : Cfg n Bool P z) := by
  cases h
  rfl

/-- Equality induction transports initialized space along a tape-count equation. -/
private theorem f6_cast_init_space {P : Type} {m n : ℕ} (h : m = n)
    (A : MultiTapeTM m Bool P) (z : List Bool) (t : ℕ) :
    (h ▸ A : MultiTapeTM n Bool P).spaceUsed
      ((h ▸ A : MultiTapeTM n Bool P).initCfg z) t =
        A.spaceUsed (A.initCfg z) t := by
  cases h
  rfl

/-- Equality induction preserves a configuration's control. -/
private theorem f6_cast_cfg_state {P : Type} {m n : ℕ} (h : m = n) {z : List Bool}
    (c : Cfg m Bool P z) : (h ▸ c : Cfg n Bool P z).state = c.state := by
  cases h
  rfl

/-- Equality induction commutes with relabelling. -/
private theorem f6_cast_cfg_mapState {P Q : Type} {m n : ℕ} (h : m = n) {z : List Bool}
    (c : Cfg m Bool P z) (f : P → Q) :
    (h ▸ c : Cfg n Bool P z).mapState f = (h ▸ c.mapState f : Cfg n Bool Q z) := by
  cases h
  rfl

/-- A transported configuration is the full-bank embedding along `Fin.castLEEmb`. -/
private theorem f6_cast_cfg_embedding {Q : Type} {m n : ℕ} (h : m = n) {z : List Bool}
    (c : Cfg m Bool Q z) :
    (h ▸ c : Cfg n Bool Q z) =
      embedEmitCfg (Fin.castLEEmb (Nat.le_of_eq h)) (fun _ _ => none) (fun _ => 0) [] c := by
  cases h
  exact (f6_full_embed c).symm

/-- Transporting back the full-bank embedding gives the original configuration. -/
private theorem f6_cast_back_embedding {Q : Type} {m n : ℕ} (h : m = n) {z : List Bool}
    (c : Cfg m Bool Q z) :
    (h.symm ▸ embedEmitCfg (Fin.castLEEmb (Nat.le_of_eq h))
      (fun _ _ => none) (fun _ => 0) [] c : Cfg m Bool Q z) = c := by
  cases h
  exact f6_full_embed c

/-- **The startup–loop seam at the last-ruler endpoint.** For a prefix `A` reaching the
installed last-ruler endpoint at a first return, the zero-outer startup–loop seam with the hosted
loop `H` runs `H` from the loop's presentation after `T + 1` steps, and uses at most
`B + (K + 4) · S` cells when the prefix uses at most `B` and each hosted tape at most `S`.

**Proof sketch.** Reconstruct the endpoint's relabelling as the host presentation
(`f6_last_ruler_layout`) and as its full-bank embedding; transport the prefix and endpoint along
`K + 4 = 0 + ((K + 2) + 2)` by equality induction; apply `startupLoopTM_runFrom` and
`startupLoopTM_spaceUsed_le`; transport back ([AB09, Exercise 4.1]). -/
private theorem f6_final_seam (K n ℓ : ℕ) {P Q V : Type} [DecidableEq P]
    (A : MultiTapeTM (K + 4) Bool P) (finish : P)
    (H : MultiTapeTM (K + 4) Bool V) (entry : Q) (inj : Q → Bool → V)
    (M : MultiTapeTM 1 Bool (Fin (n + 1))) (x z : List Bool)
    (hz : z.length = ℓ + x.length) :
    let σ : Fin 3 ↪ Fin (K + 3) := Fin.castLEEmb (by omega)
    let ec := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) []
      (StepBlock.forwardLoopCfg entry M (M.initCfg x))
    let bank : Cfg (K + 3) Bool P x :=
      ⟨some finish, 1,
        fun j => if j = 1 then FinTM.bufferTape (tableBitsK M.tr)
          else if j = 2 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
          else fun _ => none,
        fun _ => 0, []⟩
    let d : Cfg (K + 4) Bool P z :=
      ⟨some finish, ⟨ℓ + 1, by omega⟩,
        Fin.lastCases (FinTM.bufferTape (List.replicate ℓ true)) bank.workTapes,
        fun _ => 0, []⟩
    let c := rulerHostCfg ℓ hz (ec.state.map fun q => inj q false) ec
      (FinTM.bufferTape (List.replicate ℓ true)) 0
    ∀ (T t B S : ℕ),
      (A.runFrom (A.initCfg z) T = d) →
      (∀ u < T, (A.runFrom (A.initCfg z) u).state ≠ some finish) →
      (A.spaceUsed (A.initCfg z) T ≤ B) →
      (1 ≤ S) →
      (∀ i, H.spaceUsedByTape c t i ≤ S) →
      let A0 : MultiTapeTM (0 + ((K + 2) + 2)) Bool P :=
        (Nat.zero_add ((K + 2) + 2)).symm ▸ A
      let U0 := startupLoopTM (k := K + 2) (K := 0) A0 finish H (inj entry false)
      let U : MultiTapeTM (K + 4) Bool (P ⊕ V) :=
        (Nat.zero_add ((K + 2) + 2)) ▸ U0
      U.runFrom (U.initCfg z) (T + 1 + t) = (H.runFrom c t).mapState Sum.inr ∧
        U.spaceUsed (U.initCfg z) (T + 1 + t) ≤ B + (K + 4) * S := by
  intro σ ec bank d c T t B S aRun aCut hB hS hloop A0 U0 U
  have hexit : d.state = some finish := rfl
  have hphysical : d.mapState (fun _ => inj entry false) = c :=
    f6_last_ruler_layout K n ℓ finish entry inj M x z hz
  let e : (K + 4) = 0 + ((K + 2) + 2) := (Nat.zero_add ((K + 2) + 2)).symm
  let d0 : Cfg (0 + ((K + 2) + 2)) Bool P z := e ▸ d
  have aRun0 : A0.runFrom (A0.initCfg z) T = d0 := by
    calc
      _ = (e ▸ A.runFrom (A.initCfg z) T : Cfg (0 + ((K + 2) + 2)) Bool P z) :=
        f6_cast_init_run e A z T
      _ = d0 := congrArg (fun v : Cfg (K + 4) Bool P z =>
        (e ▸ v : Cfg (0 + ((K + 2) + 2)) Bool P z)) aRun
  have hexit0 : d0.state = some finish := (f6_cast_cfg_state e d).trans hexit
  have aCut0 : ∀ u < T, (A0.runFrom (A0.initCfg z) u).state ≠ some finish := by
    intro u hu
    rw [show A0.runFrom (A0.initCfg z) u =
      (e ▸ A.runFrom (A.initCfg z) u : Cfg (0 + ((K + 2) + 2)) Bool P z) from
        f6_cast_init_run e A z u, f6_cast_cfg_state]
    exact aCut u hu
  have hcfg0 : d0.mapState (fun _ => inj entry false) =
      embedEmitCfg (Fin.castLEEmb (by omega : (K + 2) + 2 ≤ 0 + ((K + 2) + 2)))
        (fun _ _ => none) (fun _ => 0) [] c := by
    calc
      _ = (e ▸ d.mapState (fun _ => inj entry false) :
          Cfg (0 + ((K + 2) + 2)) Bool V z) := f6_cast_cfg_mapState e d _
      _ = (e ▸ c : Cfg (0 + ((K + 2) + 2)) Bool V z) :=
        congrArg (fun v : Cfg (K + 4) Bool V z =>
          (e ▸ v : Cfg (0 + ((K + 2) + 2)) Bool V z)) hphysical
      _ = _ := f6_cast_cfg_embedding e c
  have hB0 : A0.spaceUsed (A0.initCfg z) T ≤ B :=
    (f6_cast_init_space e A z T).trans_le hB
  have hr := startupLoopTM_runFrom (k := K + 2) (K := 0)
    A0 finish H (inj entry false) c d0 T aRun0 hexit0 aCut0 hcfg0 t
  have hs := startupLoopTM_spaceUsed_le (k := K + 2) (K := 0)
    A0 finish H (inj entry false) c d0 T aRun0 hexit0 aCut0 hcfg0 t B S hB0 hS hloop
  constructor
  · calc
      _ = (e.symm ▸ U0.runFrom (U0.initCfg z) (T + 1 + t) : Cfg (K + 4) Bool (P ⊕ V) z) :=
        f6_cast_init_run e.symm U0 z (T + 1 + t)
      _ = (e.symm ▸ (embedEmitCfg (Fin.castLEEmb (Nat.le_of_eq e))
          (fun _ _ => none) (fun _ => 0) [] (H.runFrom c t)).mapState Sum.inr :
            Cfg (K + 4) Bool (P ⊕ V) z) :=
        congrArg (fun v : Cfg (0 + ((K + 2) + 2)) Bool (P ⊕ V) z =>
          (e.symm ▸ v : Cfg (K + 4) Bool (P ⊕ V) z)) hr
      _ = _ := by
        rw [← f6_cast_cfg_mapState, f6_cast_back_embedding]
        exact e
  · calc
      _ = U0.spaceUsed (U0.initCfg z) (T + 1 + t) :=
        f6_cast_init_space e.symm U0 z (T + 1 + t)
      _ ≤ B + (0 + ((K + 2) + 2)) * S := hs
      _ = B + (K + 4) * S := by rw [Nat.zero_add]


/-- **The space-bounded universal machine** ([AB09, Exercise 4.1], p. 93,
forward clause, with the addend-free bound `C · s`):
for the fixed scheme there is a machine `SU` such that for every code `α`
there is a constant `C > 0` with: whenever the coded machine halts on `x`
with `output`, having visited at most `s` work cells by then, `SU` on input
`⟨bits s, ⟨α, x⟩⟩` halts with the same `output`, having visited at most
`C · s` work cells: the book's `C · t`. Nothing is claimed when the coded
machine overruns `s` or does not halt. The time is existential, as
`Turing.FinTM.ComputesInTime`'s halting demands, with no stated bound. Every
qualifying run has `s ≥ 1` (`Turing.CodeTM.one_le_spaceUsed`), so the bound
is never `0`.

Deviations from the book's `SU(α, t, x) = M_α(x)` within `C · t` cells:
* **`C` depends on the representation `α`**, not only on `M_α`, as in
  `Turing.universal`, whose module docstring records why an arbitrary
  effective scheme forces this.
* "Halts before using `t` cells" is read as "at most `s` visited cells"; the
  budget is an argument of `SU`, as in the book. Its encoding is scanned to locate
  the suffix; its numerical value is not interpreted as a limit or clock.
* The output is the simulated output itself: with no failure clause there is
  no verdict to tag. The former `[false]` clause, and with it the
  visited-interval counters, the core-count clock and the probe/replay of the
  previous statement, went with design §16b item 3.

There is no input-device addend: the gated `+ logSpace |x| + 1` (a binary
position for the simulated input head) is replaced by a unary ruler of the
header's length, whose cells the bound absorbs (the RD-3 gate's minor 1).

**Proof sketch.** The ruler-hosted suffix assembly. Write `z = ⟨bits s, ⟨α, x⟩⟩`,
`ℓ₁ = 2|bits s| + 2` and `ℓ = ℓ₁ + 2|α| + 2`, the two header lengths
(`Turing.length_pairEncode`). `SU` has the `K + 3` bank tapes of the startup of
`Turing.exists_selfStartupTM` and a ruler tape last; it runs a fixed prefix, then the hosted
forwarding loop, glued by `Turing.startupLoopTM`. (i) **Prefix.** Six phases glued by
`Turing.seamCompTM`, each seam with its dispatch step and its first-return cut: the header ruler
`Turing.headerRulerTM` reads `bits s` and leaves the ruler `true^ℓ₁` rewound; the startup, seamed
to a one-step halt leaf, runs on the suffix `⟨α, x⟩` through the ruler device
`Turing.exists_rulerHostTM`, and the returning embedding `Turing.embedEmitRetTM` turns its first
halt into a live return; the skip `Turing.skipTM` and the walk `Turing.walkTM` over the empty word
(one cell back) bring the ruler head to `ℓ₁`; the header scan `Turing.headerScanTM` reads `α` and
extends the ruler to `true^ℓ` (`Turing.headerScanCfg_ruler`); `Turing.rewindTM` rewinds it. The
prefix first returns at the startup's installed bank (the decoded machine's table and initial
state; the target's bundled machine is that raw machine by `Turing.CodeTM.toFinTM_eq`), with the
ruler `true^ℓ` and the input head at `ℓ + 1`, the virtual position `1` on `x`. The numerical
budget is not interpreted as a limit or clock. Its time `T` is at most
`C_H (ℓ + 1)(T_α + 2) + 4ℓ + 11` for the startup time `T_α` of `α`, so it uses at most
`(K + 4) * (T + 1)` cells
(`Turing.MultiTapeTM.spaceUsed_le_mul_succ`). (ii) **Loop.** The forwarding round loop of
`Turing.StepBlock.exists_forwardLoopTM` on the first three bank tapes, hosted on the suffix `x` by
the ruler device; the prefix endpoint is the host's presentation of the loop's initial encoding
(`Turing.embedEmitCfg_forwardLoop_init`, `Turing.rulerHostCfg_fields`). From the coded machine's
first halt (`Turing.StepBlock.forwardLoop_forward`, via `Turing.FinTM.computesInTime_iff`) the
host halts with the same output, and `Turing.startupLoopTM_runFrom` gives `SU`'s halt with it.
(iii) **Space.** `Turing.startupLoopTM_spaceUsed_le`, tape by tape: the mirrored tape visits only
cells the coded machine visits, at most `s`; the table and summary tapes stay in `[-D_α, D_α]`,
`D_α` depending on the table only; every idle bank tape visits its start cell; the ruler stays in
`[-1, ℓ]`. Every qualifying run has `s ≥ 1` (`Turing.CodeTM.one_le_spaceUsed`) and
`|bits s| ≤ s` (`Turing.length_bits_le_self`), so `ℓ ≤ (2|α| + 6) · s` and the whole bound is at
most `C_α · s` for a positive `C_α` depending on `α` only. -/
theorem space_universal :
    ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (s : ℕ) (x output : List Bool) (t : ℕ),
        ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t →
        ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
            (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s →
          ∃ t' : ℕ,
            SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x)) output t' ∧
            SU.tm.spaceUsed
                (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
              ≤ C * s := by
  -- The fixed machine: the prefix, then the hosted forwarding loop, by the startup–loop seam.
  obtain ⟨K, P, fP, dP, A, finish, CH, hA⟩ := f6_prefix TimeHierarchy.code
  obtain ⟨Q, V, fV, dV, H, entry, inj, hH⟩ := f6_loop K
  let A0 : MultiTapeTM (0 + ((K + 2) + 2)) Bool P := (Nat.zero_add ((K + 2) + 2)).symm ▸ A
  let U : MultiTapeTM (K + 4) Bool (P ⊕ V) := (Nat.zero_add ((K + 2) + 2)) ▸
    startupLoopTM (k := K + 2) (K := 0) A0 finish H (inj entry false)
  refine ⟨{ k := K + 4, State := P ⊕ V, tm := U }, fun α => ?_⟩
  -- The per-code constant, chosen before the budget, input, output and time.
  obtain ⟨T₀, hT⟩ := hA α
  obtain ⟨D, hD⟩ := hH ((TimeHierarchy.code).decode α).tm
  let a := 2 * α.length + 6
  let p := (K + 4) * (CH * (T₀ + 2) + 12)
  let q := (K + 4) * (CH * (T₀ + 2) + 4)
  refine ⟨p + q * a + (K + 4) * (1 + (2 * D + 4) + a) + 1, by omega, ?_⟩
  intro s x output t hcomp hspace
  -- The source run, through the bundle equation; every qualifying budget is positive.
  have hs1 : 1 ≤ s := (CodeTM.one_le_spaceUsed _ x t).trans hspace
  rw [CodeTM.toFinTM_eq] at hcomp hspace
  obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff _ x output t).mp hcomp
  -- The prefix run on the two headers, and the hosted loop on the suffix `x`.
  obtain ⟨T, hTle, hrun, hcut⟩ := hT (Nat.bits s) x
  have hzl : (pairEncode (Nat.bits s) (pairEncode α x)).length =
      ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) + x.length := by
    rw [pairEncode_pairEncode_length]; omega
  have hdrop : (pairEncode (Nat.bits s) (pairEncode α x)).drop
      ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) = x := by
    rw [show (2 * (Nat.bits s).length + 2) + (2 * α.length + 2) =
      2 * (Nat.bits s).length + 2 * α.length + 4 by ring]
    exact pairEncode_pairEncode_drop (Nat.bits s) α x
  obtain ⟨t'', hHhalt, hHout, hHsp⟩ := hD x _ _ hzl (by omega) hdrop t hhalt
  -- The seam: run and per-tape space, with the prefix space bounded by its time.
  have hB := A.spaceUsed_le_mul_succ (A.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) T
  obtain ⟨hU, hUsp⟩ := f6_final_seam K _ _ A finish H entry inj
    ((TimeHierarchy.code).decode α).tm x _ hzl T t'' _
    (s + (2 * D + 1) + ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) + 3)
    hrun hcut hB (by omega) (fun i => (hHsp i).trans (by omega))
  refine ⟨T + 1 + t'', (FinTM.computesInTime_iff _ _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · change (U.runFrom (U.initCfg _) (T + 1 + t'')).state = none
    rw [hU, Cfg.mapState_state, hHhalt, Option.map_none]
  · change (U.runFrom (U.initCfg _) (T + 1 + t'')).output = output
    rw [hU, Cfg.mapState_output, hHout]
    exact hout
  · change U.spaceUsed (U.initCfg _) (T + 1 + t'') ≤ _
    refine hUsp.trans ?_
    -- Absorb the prefix bound and the per-tape budget into `C_α · s`.
    have hbits := length_bits_le_self s
    have hLa : (2 * (Nat.bits s).length + 2) + (2 * α.length + 2) ≤ a * s := by
      have h4 : 2 * α.length + 4 ≤ (2 * α.length + 4) * s := Nat.le_mul_of_pos_right _ hs1
      have he : a * s = 2 * s + (2 * α.length + 4) * s := by
        simp only [a]; ring
      omega
    have hT1 : T + 1 ≤ (CH * (T₀ + 2) + 12) + (CH * (T₀ + 2) + 4) *
        ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) := by
      have he : CH * ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2) + 1) * (T₀ + 2) +
          4 * ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) + 12 =
          (CH * (T₀ + 2) + 12) + (CH * (T₀ + 2) + 4) *
            ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) := by ring
      omega
    have hB' : (K + 4) * (T + 1) ≤ p * s + q * a * s := by
      calc (K + 4) * (T + 1)
          ≤ (K + 4) * ((CH * (T₀ + 2) + 12) + (CH * (T₀ + 2) + 4) *
            ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2))) :=
            Nat.mul_le_mul_left _ hT1
        _ = p + q * ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) := by
            simp only [p, q]; ring
        _ ≤ p * s + q * (a * s) :=
            Nat.add_le_add (Nat.le_mul_of_pos_right _ hs1) (Nat.mul_le_mul_left _ hLa)
        _ = p * s + q * a * s := by ring
    have hS' : (K + 4) * (s + (2 * D + 1) +
        ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) + 3) ≤
        (K + 4) * (1 + (2 * D + 4) + a) * s := by
      have h1 : 2 * D + 4 ≤ (2 * D + 4) * s := Nat.le_mul_of_pos_right _ hs1
      have he : (1 + (2 * D + 4) + a) * s = s + (2 * D + 4) * s + a * s := by ring
      calc (K + 4) * (s + (2 * D + 1) +
            ((2 * (Nat.bits s).length + 2) + (2 * α.length + 2)) + 3)
          ≤ (K + 4) * ((1 + (2 * D + 4) + a) * s) := Nat.mul_le_mul_left _ (by omega)
        _ = (K + 4) * (1 + (2 * D + 4) + a) * s := by ring
    have he : (p + q * a + (K + 4) * (1 + (2 * D + 4) + a) + 1) * s =
        p * s + q * a * s + (K + 4) * (1 + (2 * D + 4) + a) * s + s := by ring
    omega

/-- The inclusion half: `hfg` at `A = 1` from some `N` on, and `g`'s floor below `N`.
[AB09, Theorem 4.8, inclusion]

**Proof sketch.** Bound the finitely many exceptional values by their supremum. The positive
floor of `g` absorbs that supremum into one constant, and `SPACE.mono_const` applies. -/
private lemma sph_inclusion {f g : ℕ → ℕ} (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) : SPACE f ⊆ SPACE g := by
  obtain ⟨N, hN⟩ := hfg 1
  have hfloor : ∀ n, 1 ≤ g n := fun n =>
    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff g).mp hg).1 n)
  set F := (Finset.range N).sup f with hF
  refine SPACE.mono_const (a := F + 1) fun n => ?_
  by_cases hn : N ≤ n
  · have := hN n hn
    calc f n ≤ g n := by simpa using this
      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  · have hle : f n ≤ F := Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
    calc f n ≤ F + 1 := by omega
      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_right _ (hfloor n)

/-- A decider in the smaller space class has a padded code on which the fixed universal
machine halts inside the larger window, before its configuration-count clock expires.
[AB09, Theorem 4.8, diagonal contradiction]

**Proof sketch.** Normalize the decider to one binary work tape and then to a coded machine,
using the published space clauses. Choose the domination constant after the code's universal
simulation constant is fixed, and pad the payload to the resulting threshold. The configuration
bound supplies a halting time; the window-summary theorem identifies the run at the next round. -/
private lemma sph_code_window (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) (U₀ : FinTM Bool)
    (hU : ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (w output : List Bool) (t s : ℕ),
        (TimeHierarchy.code.decode α).toFinTM.ComputesInTime (pairEncode α w) output t →
        (TimeHierarchy.code.decode α).toFinTM.tm.spaceUsed
          ((TimeHierarchy.code.decode α).toFinTM.tm.initCfg (pairEncode α w)) t ≤ s →
        ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
          U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1))
    (L : Language Bool) (c₀ : ℕ) (M : FinTM Bool)
    (hM : M.DecidesInSpace L (fun n => c₀ * f n)) :
    ∃ (x : List Bool) (t : ℕ),
      U₀.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t ∧
      U₀.tm.spaceUsed (U₀.tm.initCfg x) t ≤ g x.length ∧
      t = U₀.configBound x.length (g x.length) ∧
      windowRun U₀.tm (g x.length) summaryTag (t + 1) (U₀.tm.initCfg x) 0 =
        (.halted, U₀.tm.runFrom (U₀.tm.initCfg x) t,
          outSummaryCode (outSummary [MultiTapeTM.indicator (L : Set (List Bool)) x])) := by
  have hm := (FinTM.decidesInSpace_iff M L (fun n => c₀ * f n)).mp hM
  have hbounds := hm.computesFunInTime_and_forall_spaceUsed_le
  obtain ⟨M₁, c₁, hk, htime, hspace⟩ := FinTM.one_work_tape_binary_spaceUsed M
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
    (fun n => M.configBound n (c₀ * f n)) (fun n => c₀ * f n) hbounds.1 hbounds.2
  obtain ⟨N, hrun, hsp⟩ := exists_codeTM_spaceUsed M₁ hk
  let α := TimeHierarchy.code.encode N
  have hα : TimeHierarchy.code.decode α = N := MachineCode.decode_encode _ _
  obtain ⟨C, _hC, hsim⟩ := hU α
  let A := C * (c₁ * c₀ + c₁ + 1)
  obtain ⟨N₀, hN₀⟩ := hfg A
  let x := pairEncode α (List.replicate N₀ true)
  have hx : N₀ ≤ x.length := by
    simp only [x, length_pairEncode, List.length_replicate]
    omega
  let t₀ := c₁ * (M.configBound x.length (c₀ * f x.length) + 1) ^ 2
  have hn : (TimeHierarchy.code.decode α).toFinTM.ComputesInTime x
      [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ := by
    rw [hα]
    exact (hrun x _ t₀).mpr ((FinTM.computesFunInTime_iff _ _ _).mp htime x)
  have hs : (TimeHierarchy.code.decode α).toFinTM.tm.spaceUsed
      ((TimeHierarchy.code.decode α).toFinTM.tm.initCfg x) t₀ ≤
      c₁ * (c₀ * f x.length + 1) := by
    rw [hα, hsp]
    exact hspace x t₀
  obtain ⟨u, hu, hsu⟩ := hsim (List.replicate N₀ true)
    [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ (c₁ * (c₀ * f x.length + 1)) hn hs
  have hfloor : 1 ≤ f x.length :=
    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff f).mp hf).1 x.length)
  have hsmall : C * (c₁ * (c₀ * f x.length + 1) + 1) ≤ A * f x.length := by
    calc
      _ ≤ C * (c₁ * (c₀ * f x.length + f x.length) + f x.length) :=
        Nat.mul_le_mul_left C (Nat.add_le_add
          (Nat.mul_le_mul_left c₁ (Nat.add_le_add_left hfloor _)) hfloor)
      _ = A * f x.length := by dsimp only [A]; ring
  have hwindow : U₀.tm.spaceUsed (U₀.tm.initCfg x) u ≤ g x.length :=
    hsu.trans (hsmall.trans (hN₀ x.length hx))
  let t := U₀.configBound x.length (g x.length)
  have hhalt : U₀.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t :=
    hu.of_spaceUsed_le hwindow
  have hspace' : U₀.tm.spaceUsed (U₀.tm.initCfg x) t ≤ g x.length :=
    hu.spaceUsed_le_of_halt hwindow t
  exact ⟨x, t, hhalt, hspace', rfl,
    windowRun_summary_of_halts U₀ x hhalt hspace' (Nat.lt_succ_self t)⟩

/-- A square below a power of two, from `4` on.

**Proof sketch.** Induct from `4`; doubling the previous power absorbs the next square. -/
private lemma sph_sq_le_two_pow : ∀ L, 4 ≤ L → L * L ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    nlinarith

/-- The logarithm is dominated by the identity at every constant factor, eventually.

**Proof sketch.** Beyond `2 ^ max 4 (2 * A)`, the integer logarithm is at least both `4` and
`2 * A`. Its square fits below `n`, and dominates `A * (log₂ n + 1)`. -/
private lemma sph_logSpace_dom : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * logSpace n ≤ n + 1 := by
  intro A
  refine ⟨2 ^ (max 4 (2 * A)), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have := Nat.one_le_two_pow (n := max 4 (2 * A)); omega
  set L := Nat.log 2 n with hL
  have hLge : max 4 (2 * A) ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hsq := sph_sq_le_two_pow L (le_trans (le_max_left _ _) hLge)
  have h2A : 2 * A ≤ L := le_trans (le_max_right _ _) hLge
  rw [logSpace_eq, ← hL]
  nlinarith

/-- **`LOGSPACE ⊂ PSPACE`**, from the space hierarchy's statement. [AB09, §4.3.2]

**Proof sketch.** Apply the hierarchy to logarithmic and linear space, then transport strictness
along the published inclusion of linear space into polynomial space. -/
private lemma sph_logspace_ssubset
    (hH : ∀ f g : ℕ → ℕ, SpaceConstructible f → SpaceConstructible g →
      (∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) → SPACE f ⊂ SPACE g) :
    LOGSPACE ⊂ PSPACE := by
  have hlin : SPACE (fun n => n + 1) ⊆ PSPACE := by
    have := space_poly_subset_PSPACE 1
    simpa only [pow_one] using this
  obtain ⟨-, hnot⟩ := hH logSpace (fun n => n + 1) spaceConstructible_logSpace
    spaceConstructible_linear sph_logSpace_dom
  refine ⟨LOGSPACE_subset_PSPACE, fun hP => hnot ?_⟩
  rw [← LOGSPACE_eq]
  exact hlin.trans hP

/-- One input-head move before the lifted rewind. The rewind's published contract requires a
positive input position; this leaf supplies it even when the radius witness stops at `0`.
The action changes no work tape or output. [AB09, §1.2]

**Proof sketch.** The transition always moves the input head right and reaches its live anchor.
At the right boundary it stays put; everywhere else its position increases by one. -/
private def sphRightTM (k : ℕ) (Γ : Type) : MultiTapeTM k Γ Bool where
  q₀ := false
  tr := fun _ _ _ => ⟨.pos, fun _ => (none, 0), none, some true⟩

/-- The right-move leaf's framed run and positive endpoint.

**Proof sketch.** Read the one transition field by field, separate the input's right boundary,
and use the zero-step and one-step configurations for the cut and head claim. -/
private lemma sph_right_run {k : ℕ} {Γ : Type} {x : List Γ}
    (d : Cfg k Γ Bool x) (hd : d.state = some false) :
    (sphRightTM k Γ).runFrom d 1 =
        {d with state := some true, inputPos := moveInputPos d.inputPos .pos} ∧
      1 ≤ (moveInputPos d.inputPos .pos).val ∧
      (∀ u < 1, ((sphRightTM k Γ).runFrom d u).state ≠ some true) ∧
      ∀ u ≤ 1, ((sphRightTM k Γ).runFrom d u).workTapePos = d.workTapePos := by
  have hstep : (sphRightTM k Γ).runFrom d 1 =
      {d with state := some true, inputPos := moveInputPos d.inputPos .pos} := by
    rw [MultiTapeTM.runFrom_one,
      MultiTapeTM.step_of_some hd]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]; rfl
    · funext j p
      rw [Action.apply_workTapes]
      simp only [sphRightTM, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext j
      rw [Action.apply_workTapePos]
      simp only [sphRightTM, SignType.coe_zero, add_zero]
    · rw [Action.apply_output]
      simp only [sphRightTM, Option.toList_none, List.append_nil]
  refine ⟨hstep, ?_, ?_, ?_⟩
  · by_cases h : d.inputPos.val = x.length + 1
    · have hp : d.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext h
      rw [hp, SignType.pos_eq_one, moveInputPos_rightBoundary]
      omega
    · rw [moveInputPos_pos_of_ne_right _ h]
      exact Nat.succ_pos _
  · intro u hu
    have : u = 0 := Nat.lt_one_iff.mp hu
    subst u
    rw [MultiTapeTM.runFrom_zero, hd]
    decide
  · intro u hu
    have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
    rcases this with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
    · rw [hstep]

/-- Emit the final verdict and halt, preserving the input and work tapes. The only output
leaf needed after the record test. [AB09, §1.2] -/
private def sphEmitTM (k : ℕ) {Γ : Type} (b : Γ) : MultiTapeTM k Γ Unit where
  q₀ := ()
  tr := fun _ _ _ => ⟨0, fun _ => (none, 0), some b, none⟩

/-- The verdict emitter appends exactly one symbol in one step, with no work-head motion.

**Proof sketch.** Read the five fields of its sole action using the public action equations. -/
private lemma sph_emit_run {k : ℕ} {Γ : Type} {x : List Γ} (b : Γ)
    (d : Cfg k Γ Unit x) (hd : d.state = some ()) :
    (sphEmitTM k b).runFrom d 1 = {d with state := none, output := d.output ++ [b]} ∧
      ∀ u ≤ 1, ((sphEmitTM k b).runFrom d u).workTapePos = d.workTapePos := by
  have hstep : (sphEmitTM k b).runFrom d 1 =
      {d with state := none, output := d.output ++ [b]} := by
    rw [MultiTapeTM.runFrom_one,
      MultiTapeTM.step_of_some hd]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]
      exact moveInputPos_zero _
    · funext j p
      rw [Action.apply_workTapes]
      simp only [sphEmitTM, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext j
      rw [Action.apply_workTapePos]
      simp only [sphEmitTM, SignType.coe_zero, add_zero]
    · rw [Action.apply_output]
      rfl
  refine ⟨hstep, ?_⟩
  intro u hu
  have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
  rcases this with rfl | rfl
  · rw [MultiTapeTM.runFrom_zero]
  · rw [hstep]

/-- The input validator's finite-state test: precisely the embedded binary digits. -/
private def sphDigit {Q : Type} : RecSym Q (Fin 3) → Bool
  | .digit _ => true
  | .cell _ _ => false
  | .st _ => false
  | .tag _ => false

/-- The validator accepts precisely embedded binary words, including the empty word.

**Proof sketch.** Induct on the input. A successful fold forces the head symbol to be a digit;
strip that digit and use the induction hypothesis on the tail. Conversely, prepend the
corresponding Boolean to the decoded tail. -/
private lemma sph_fold_valid {Q : Type} (ys : List (RecSym Q (Fin 3))) (a : Bool) :
    ys.foldl (fun b c => b && sphDigit c) a = true ↔
      a = true ∧ ∃ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) := by
  induction ys generalizing a with
  | nil =>
    rw [List.foldl_nil]
    exact ⟨fun h => ⟨h, [], rfl⟩, fun h => h.1⟩
  | cons y ys ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro ⟨hay, x, hx⟩
      obtain ⟨ha, hy⟩ := Bool.and_eq_true_iff.mp hay
      refine ⟨ha, ?_⟩
      cases y with
      | digit b =>
        refine ⟨b :: x, ?_⟩
        rw [List.map_cons, RecSym.digitEmb_apply, ← hx]
      | cell c m => cases hy
      | st q => cases hy
      | tag t => cases hy
    · rintro ⟨ha, x, hx⟩
      cases x with
      | nil => cases hx
      | cons b bs =>
        rw [List.map_cons] at hx
        obtain ⟨hy, ht⟩ := List.cons.inj hx
        refine ⟨Bool.and_eq_true_iff.mpr ⟨ha, ?_⟩, bs, ht⟩
        rw [hy, RecSym.digitEmb_apply]
        rfl

/-- The rich-input validation phase, on all of the diagonalizer's work tapes. Its successful
exit supplies a binary input for every subsequent phase; it moves no work head.
[AB09, Theorem 4.8, alphabet reduction]

**Proof sketch.** Use the published framed input fold and identify its final flag with
`sph_fold_valid`. The framed endpoint also restores the input head to its initial position. -/
private lemma sph_validation_run {k : ℕ} {Q : Type}
    {ys : List (RecSym Q (Fin 3))} (d : Cfg k (RecSym Q (Fin 3)) (ScanPhase Bool) ys)
    (hd : d.state = some (.fwd true)) (hin : d.inputPos = 1) :
    ∃ b : Bool,
      (inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d (2 * ys.length + 2) =
        {d with state := some (.done b)} ∧
      (b = true ↔ ∃ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3))) ∧
      (∀ u < 2 * ys.length + 2, ∀ a,
        ((inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d u).state ≠
          some (.done a)) ∧
      ∀ j u, u ≤ 2 * ys.length + 2 →
        ((inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d u).workTapePos j =
          d.workTapePos j := by
  obtain ⟨hr, hc, hh⟩ := inputFoldTM_run_ofCfg (fun a c => a && sphDigit c) true d hd hin
  refine ⟨ys.foldl (fun a c => a && sphDigit c) true, hr, ?_, hc, hh⟩
  exact ⟨fun h => ((sph_fold_valid ys true).mp h).2,
    fun h => (sph_fold_valid ys true).mpr ⟨rfl, h⟩⟩

/-- Witness tapes are after the record, radius, initializer scratch and runner scratch banks.
Separate scratch banks keep the runner disjoint from both the radius and the dirty witness. -/
private def sphWitnessSel (KI KR m : ℕ) : Fin m ↪ Fin (KI + KR + m + 2) where
  toFun i := ⟨KI + KR + 2 + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' : KI + KR + 2 + i.val = KI + KR + 2 + j.val :=
      congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h
    exact Nat.add_left_cancel h'

/-- The radius tape is outside the witness bank, including for a zero-tape witness. -/
private lemma sph_witness_cap (KI KR m : ℕ) :
    (1 : Fin (KI + KR + m + 2)) ∉ Set.range (sphWitnessSel KI KR m) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp only [sphWitnessSel, Function.Embedding.coeFn_mk, Fin.val_one] at this
  omega

/-- The constructibility witness returns with its complete binary radius on tape `1`, preserving
all tapes outside its bank and the radius tape. Its last emission is included in the captured
word. [AB09, Theorem 4.8, radius phase]

**Proof sketch.** Choose the witness's first halting time and lift its run to the record
alphabet. Apply the published returning capture embedding. Its capture and frame equations give
the endpoint. Its selected, capture and frame space equations bound each tape; summing gives a
constant multiple of the witness space and radius length. -/
private lemma sph_radius_run (KI KR : ℕ) {Q : Type} [DecidableEq Q]
    (g : ℕ → ℕ) (c : ℕ) (M : FinTM Bool)
    (hM : M.ComputesInSpace (fun x => (g x.length).bits) (fun n => c * g n))
    (x : List Bool)
    (tapes : Fin (KI + KR + M.k + 2) → ℤ → Option (RecSym Q (Fin 3)))
    (heads : Fin (KI + KR + M.k + 2) → ℤ) (out : List (RecSym Q (Fin 3))) :
    let e := RecSym.digitEmb Q (Fin 3)
    let ι := sphWitnessSel KI KR M.k
    let R := embedSilentRetTM ι 1 (M.tm.liftSymbols e)
    let start := (embedSilentCfg ι 1 tapes heads [] out
      ((M.tm.initCfg x).liftSymbols e)).mapState (Sum.inl : M.State → M.State ⊕ Unit)
    ∃ t : ℕ,
      (R.runFrom start t).state = some (Sum.inr ()) ∧
      (∀ u < t, (R.runFrom start u).state ≠ some (Sum.inr ())) ∧
      (R.runFrom start t).workTapes 1 =
        FinTM.bufferTape ((g x.length).bits.map RecSym.digit) ∧
      (R.runFrom start t).workTapePos 1 = ((g x.length).bits.length : ℤ) ∧
      (∀ j, j ∉ Set.range ι → j ≠ 1 →
        (R.runFrom start t).workTapes j = tapes j ∧
          (R.runFrom start t).workTapePos j = heads j) ∧
      (∀ u ≤ t, (R.runFrom start u).output = out) ∧
      R.spaceUsed start t ≤ (KI + KR + M.k + 2) *
        (c * g x.length + (g x.length).bits.length + 1) ∧
      ∀ u ≤ t, ∀ j,
        |(R.runFrom start u).workTapePos j| ≤
          |heads j| + (c * g x.length + (g x.length).bits.length : ℕ) := by
  classical
  dsimp only
  let e := RecSym.digitEmb Q (Fin 3)
  let ι := sphWitnessSel KI KR M.k
  let R := embedSilentRetTM ι 1 (M.tm.liftSymbols e)
  let a := (M.tm.initCfg x).liftSymbols e
  let start := (embedSilentCfg ι 1 tapes heads [] out a).mapState
    (Sum.inl : M.State → M.State ⊕ Unit)
  obtain ⟨v, hv, hsv⟩ := (FinTM.computesInSpace_iff _ _ _).mp hM x
  obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hv
  obtain ⟨t, htv, hlive, heq⟩ := M.tm.exists_first_halt (M.tm.initCfg x) hhalt
  have hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * g x.length :=
    (M.tm.spaceUsed_mono _ htv).trans hsv
  have ho : (M.tm.runFrom (M.tm.initCfg x) t).output = (g x.length).bits :=
    (congrArg Cfg.output heq).trans hout
  have hc : a.state ≠ none := by
    rw [Cfg.liftSymbols_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have hh : ((M.tm.liftSymbols e).runFrom a t).state = none := by
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state, heq, hhalt]
  have hl : ∀ u < t, ((M.tm.liftSymbols e).runFrom a u).state ≠ none := by
    intro u hu
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state]
    exact hlive u hu
  have hcap := sph_witness_cap KI KR M.k
  obtain ⟨hpre, hr, hcut⟩ := embedSilentRetTM_run ι 1 hcap (M.tm.liftSymbols e)
    tapes heads [] out a t hc hl hh
  have hout' : ((M.tm.liftSymbols e).runFrom a t).output =
      (g x.length).bits.map RecSym.digit := by
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_output, ho]
    apply List.map_congr_left
    intro b _
    exact RecSym.digitEmb_apply _ _ b
  refine ⟨t, ?_, hcut, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
  · rw [hr]
    have h := (embedSilentCfg_cap ι 1 hcap tapes heads [] out
      ((M.tm.liftSymbols e).runFrom a t)).1
    simpa only [List.nil_append, hout'] using h
  · rw [hr]
    have h := (embedSilentCfg_cap ι 1 hcap tapes heads [] out
      ((M.tm.liftSymbols e).runFrom a t)).2
    simpa only [List.nil_append, hout', List.length_map] using h
  · intro j hj hjc
    rw [hr]
    exact embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc
  · intro u hu
    rcases lt_or_eq_of_le hu with hu | rfl
    · rw [hpre u hu, Cfg.mapState_output, embedSilentCfg_output]
    · rw [hr, embedSilentCfg_output]
  · rw [MultiTapeTM.spaceUsed_eq_sum]
    calc
      _ ≤ (Finset.univ : Finset (Fin (KI + KR + M.k + 2))).card •
          (c * g x.length + (g x.length).bits.length + 1) := by
        apply Finset.sum_le_card_nsmul
        intro j _
        rw [MultiTapeTM.spaceUsedByTape_eq_card,
          embedSilentRetTM_visitedByTapeHead,
          ← MultiTapeTM.spaceUsedByTape_eq_card]
        by_cases hj : j ∈ Set.range ι
        · obtain ⟨i, rfl⟩ := hj
          rw [(embedSilentTM_visitedByTapeHead ι 1 hcap _ tapes heads [] out a t i).2]
          have h : (M.tm.liftSymbols e).spaceUsedByTape a t i ≤ c * g x.length :=
            calc
              _ ≤ (M.tm.liftSymbols e).spaceUsed a t :=
                (M.tm.liftSymbols e).spaceUsedByTape_le_spaceUsed a t i
              _ = M.tm.spaceUsed (M.tm.initCfg x) t :=
                MultiTapeTM.liftSymbols_spaceUsed M.tm e (M.tm.initCfg x) t
              _ ≤ _ := hs
          omega
        · by_cases hjc : j = 1
          · subst j
            have h := embedSilentTM_spaceUsedByTape_cap ι 1 hcap
              (M.tm.liftSymbols e) tapes heads [] out a t
            rw [hout', List.length_map] at h
            exact h.trans (by omega)
          · rw [(embedSilentTM_visitedByTapeHead_frame ι 1 hcap _
              tapes heads [] out a t j hj hjc).2]
            omega
      _ = _ := by rw [Finset.card_fin, smul_eq_mul]
  · intro u hu j
    have hpos : (R.runFrom start u).workTapePos j =
        (embedSilentCfg ι 1 tapes heads [] out
          ((M.tm.liftSymbols e).runFrom a u)).workTapePos j := by
      rcases lt_or_eq_of_le hu with hlt | rfl
      · rw [hpre u hlt, Cfg.mapState_workTapePos]
      · rw [hr]
    rw [hpos]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedSilentCfg_selected_pos, MultiTapeTM.liftSymbols_runFrom,
        Cfg.liftSymbols_workTapePos]
      have h := ((FinTM.inWindow_of_spaceUsed_le M x hs u hu).core_bounds i).1
      have hn := abs_nonneg (heads (ι i))
      exact h.trans (by push_cast; omega)
    · by_cases hjc : j = 1
      · subst j
        rw [(embedSilentCfg_cap ι 1 hcap tapes heads [] out _).2,
          MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_output,
          List.nil_append, List.length_map, abs_of_nonneg (by omega)]
        have h := (M.tm.output_prefix (M.tm.initCfg x) hu).length_le
        rw [ho] at h
        have hn := abs_nonneg (heads 1)
        push_cast
        omega
      · rw [(embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc).2]
        have hn : (0 : ℤ) ≤ (c * g x.length + (g x.length).bits.length : ℕ) :=
          Int.natCast_nonneg _
        omega


/-- The input rewind uses no work tapes, so its embedding preserves every work tape. -/
private def sphEmptySel (k : ℕ) : Fin 0 ↪ Fin k := Function.Embedding.ofIsEmpty

/-- The lifted binary input rewind, embedded on the empty bank, is valid from any positive
input position of an embedded binary word, with the entire physical work bank framed.

**Proof sketch.** Construct the zero-tape binary configuration at the same input position,
apply the published input rewind, lift its run, and use the R1 reconstruction theorem to
identify its initial and final embeddings with the physical configurations. -/
private lemma sph_input_rewind_run {k : ℕ} {Q : Type} [DecidableEq Q] {x : List Bool}
    (d : Cfg k (RecSym Q (Fin 3)) InputRewindPhase (x.map (RecSym.digitEmb Q (Fin 3))))
    (hd : d.state = some .start) (hp : 1 ≤ d.inputPos.val) :
    let R := embedEmitTM (sphEmptySel k)
      ((inputRewindTM 0).liftSymbols (RecSym.digitEmb Q (Fin 3)))
    R.runFrom d (d.inputPos.val + 1) = {d with state := some .done, inputPos := 1} ∧
      (∀ u < d.inputPos.val + 1, (R.runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ d.inputPos.val + 1, (R.runFrom d u).workTapePos = d.workTapePos := by
  let e := RecSym.digitEmb Q (Fin 3)
  let a : Cfg 0 Bool InputRewindPhase x :=
    ⟨some .start, ⟨d.inputPos.val, by simpa only [List.length_map] using d.inputPos.isLt⟩,
      Fin.elim0, Fin.elim0, []⟩
  have ha : a.inputPos.val = d.inputPos.val := rfl
  have hi : (a.liftSymbols e).inputPos = d.inputPos := by
    rw [Cfg.liftSymbols_inputPos]
    exact Fin.ext rfl
  have hs : embedEmitCfg (sphEmptySel k) d.workTapes d.workTapePos d.output
      (a.liftSymbols e) = d := by
    apply embedEmitCfg_eq
    · rw [Cfg.liftSymbols_state]; exact hd.symm
    · exact hi
    · rw [Cfg.liftSymbols_output]
      exact List.append_nil _
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => ⟨rfl, rfl⟩
  obtain ⟨hr, hc, hh⟩ := inputRewindTM_run a rfl (ha.symm ▸ hp)
  have hrun (u : ℕ) :
      (embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)).runFrom d u =
        embedEmitCfg (sphEmptySel k) d.workTapes d.workTapePos d.output
          (((inputRewindTM 0).runFrom a u).liftSymbols e) := by
    have h := embedEmitTM_runFrom (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)
      d.workTapes d.workTapePos d.output (a.liftSymbols e) u
    rw [hs, MultiTapeTM.liftSymbols_runFrom] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun, ← ha, hr]
    apply embedEmitCfg_eq
    · rw [Cfg.liftSymbols_state]
    · rw [Cfg.liftSymbols_inputPos]
      exact Fin.ext rfl
    · rw [Cfg.liftSymbols_output]
      exact List.append_nil _
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => ⟨rfl, rfl⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state, Cfg.liftSymbols_state]
    exact hc u (ha.symm ▸ hu)
  · intro u _
    rw [hrun]
    funext j
    exact (embedEmitCfg_unselected (sphEmptySel k) d.workTapes d.workTapePos d.output
      (((inputRewindTM 0).runFrom a u).liftSymbols e) j
      (by rintro ⟨i, _⟩; exact Fin.elim0 i)).2

/-- The two rewinds after radius capture: a right move makes the input position positive,
the zero-tape input rewind restores position one, and the radius rewind restores tape one.
Both seams use the published general-configuration composition. -/
private def sphRewindsTM (k : ℕ) (Q : Type) [DecidableEq Q] (cap : Fin k) :
    MultiTapeTM k (RecSym Q (Fin 3)) ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) :=
  seamCompTM
    (seamCompTM (sphRightTM k (RecSym Q (Fin 3))) true
      (embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols
        (RecSym.digitEmb Q (Fin 3)))) .start)
    (.inr .done) (rewindTM k cap) .start

/-- A common absolute head interval is preserved by a published general-configuration seam.

**Proof sketch.** Before the dispatch use the public left trajectory; afterwards use the
public right trajectory. State relabelling preserves every work-head position. -/
private lemma sph_seam_heads {k : ℕ} {Γ P Q : Type} [DecidableEq P] {x : List Γ}
    (A : MultiTapeTM k Γ P) (exit : P) (B : MultiTapeTM k Γ Q) (entry : Q)
    {d d' : Cfg k Γ P x} {t v : ℕ} (hr : A.runFrom d t = d')
    (he : d'.state = some exit) (hc : ∀ u < t, (A.runFrom d u).state ≠ some exit)
    (p : Fin k → ℤ) (r : ℕ)
    (hA : ∀ u ≤ t, ∀ j, |(A.runFrom d u).workTapePos j - p j| ≤ (r : ℤ))
    (hB : ∀ u ≤ v, ∀ j,
      |(B.runFrom (d'.mapState fun _ => entry) u).workTapePos j - p j| ≤ (r : ℤ)) :
    ∀ u ≤ t + 1 + v, ∀ j,
      |((seamCompTM A exit B entry).runFrom (d.mapState Sum.inl) u).workTapePos j - p j| ≤
        (r : ℤ) := by
  intro u hu j
  by_cases h : u ≤ t
  · rw [seamCompTM_runFrom_left A exit B entry hc u h, Cfg.mapState_workTapePos]
    exact hA u h j
  · obtain ⟨w, hw, rfl⟩ : ∃ w ≤ v, u = t + 1 + w := ⟨u - (t + 1), by omega, by omega⟩
    rw [seamCompTM_runFrom_right A exit B entry hr he hc w, Cfg.mapState_workTapePos]
    exact hB w hw j

/-- The paired rewinds on the tape plan, including an empty captured word and an input head
initially at zero. Every work-tape cell and the accumulated output are preserved.

**Proof sketch.** Compose the one-step right move and the lifted zero-tape rewind at their
first returns. Apply the framed radius rewind at the full captured word's length and compose
again. Read the endpoint through the public state-map equations. -/
private lemma sph_rewinds_run (KI KR m : ℕ) {Q : Type} [DecidableEq Q]
    {x : List Bool} (ws : List Bool)
    (d : Cfg (KI + KR + m + 2) (RecSym Q (Fin 3)) Bool
      (x.map (RecSym.digitEmb Q (Fin 3))))
    (hd : d.state = some false)
    (hcap : d.workTapes 1 = FinTM.bufferTape (ws.map RecSym.digit))
    (hpos : d.workTapePos 1 = (ws.length : ℤ)) :
    ∃ t,
      (sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) t =
        { state := some (Sum.inr RewindPhase.done)
          inputPos := 1
          workTapes := d.workTapes
          workTapePos := Function.update d.workTapePos 1 0
          output := d.output } ∧
      (∀ u < t,
        ((sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).state ≠ some (Sum.inr .done)) ∧
      ∀ u ≤ t, ∀ j,
        |((sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).workTapePos j - d.workTapePos j| ≤
            ((ws.length + 1 : ℕ) : ℤ) := by
  let k := KI + KR + m + 2
  let e := RecSym.digitEmb Q (Fin 3)
  let I := embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)
  let A := seamCompTM (sphRightTM k (RecSym Q (Fin 3))) true I .start
  let d₁ := {d with state := some true, inputPos := moveInputPos d.inputPos .pos}
  let a := d₁.mapState (fun _ => InputRewindPhase.start)
  let d₂ : Cfg k (RecSym Q (Fin 3)) InputRewindPhase (x.map e) :=
    {a with state := some InputRewindPhase.done, inputPos := 1}
  obtain ⟨h₁, hp, hc₁, hh₁⟩ := sph_right_run d hd
  obtain ⟨h₂, hc₂, hh₂⟩ := sph_input_rewind_run a
    (by rw [Cfg.mapState_state]; rfl)
    (by rw [Cfg.mapState_inputPos]; exact hp)
  have hA : A.runFrom (d.mapState Sum.inl) (1 + 1 + (a.inputPos.val + 1)) =
      d₂.mapState Sum.inr :=
    seamCompTM_run_ofCfg (sphRightTM k _) true I .start h₁ rfl hc₁ h₂
  have hAc := seamCompTM_firstReturn_ofCfg (sphRightTM k _) true I .start .done
    h₁ rfl hc₁ h₂ rfl hc₂
  let b := (d₂.mapState (Sum.inr : InputRewindPhase → Bool ⊕ InputRewindPhase)).mapState
    (fun _ => RewindPhase.start)
  have hb : b.state = some .start := by
    rw [Cfg.mapState_state, Cfg.mapState_state]
    rfl
  have hbh : b.workTapePos = d.workTapePos := by
    funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  have hbt : b.workTapes = d.workTapes := by
    funext j p
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  obtain ⟨h₃, hc₃, hh₃⟩ := rewindTM_run_ofCfg (1 : Fin k)
    (ws.map (RecSym.digit : Bool → RecSym Q (Fin 3))) ws.length
    (by rw [List.length_map]) b hb (by
      intro p _ _
      rw [hbt, hbh, hpos, sub_self, zero_add, hcap])
  let d₃ := { b with
    state := some RewindPhase.done
    workTapePos := Function.update b.workTapePos 1 (b.workTapePos 1 - ws.length) }
  have hend : d₃.mapState Sum.inr =
      ({ state := some (Sum.inr RewindPhase.done)
         inputPos := 1
         workTapes := d.workTapes
         workTapePos := Function.update d.workTapePos 1 0
         output := d.output } : Cfg k (RecSym Q (Fin 3))
           ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) (x.map e)) := by
    refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
    · rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j p
      exact congrFun (congrFun hbt j) p
    · funext j
      dsimp only [d₃]
      rw [hbh, hpos, sub_self]
    · rw [Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output]
  refine ⟨(1 + 1 + (a.inputPos.val + 1)) + 1 + (ws.length + 2), ?_, ?_, ?_⟩
  · exact (seamCompTM_run_ofCfg A (.inr .done) (rewindTM k 1) .start
      hA (by rw [Cfg.mapState_state]; rfl) hAc h₃).trans hend
  · exact seamCompTM_firstReturn_ofCfg A (.inr .done) (rewindTM k 1) .start .done
      hA (by rw [Cfg.mapState_state]; rfl) hAc h₃ rfl hc₃
  · have hAh := sph_seam_heads (sphRightTM k (RecSym Q (Fin 3))) true I .start
      h₁ rfl hc₁ d.workTapePos (ws.length + 1)
      (by
        intro u hu j
        rw [hh₁ u hu, sub_self, abs_zero]
        omega)
      (by
        intro u hu j
        have h := congrFun (hh₂ u hu) j
        rw [Cfg.mapState_workTapePos] at h
        rw [h, sub_self, abs_zero]
        omega)
    exact sph_seam_heads A (.inr .done) (rewindTM k 1) .start
      hA (by rw [Cfg.mapState_state]; rfl) hAc d.workTapePos (ws.length + 1) hAh
      (by
        intro u hu j
        change |((rewindTM k 1).runFrom b u).workTapePos j - d.workTapePos j| ≤
          ((ws.length + 1 : ℕ) : ℤ)
        have h := hh₃ j u hu
        by_cases hj : j = 1
        · rw [if_pos hj, hbh, Finset.mem_Icc] at h
          exact abs_le.mpr ⟨by push_cast; omega, by push_cast; omega⟩
        · rw [if_neg hj, hbh] at h
          rw [h, sub_self, abs_zero]
          omega)


/-- Read a selected configuration through R1 reconstruction, without unfolding the selector.
This common field calculation is used by the runner and final record test.

**Proof sketch.** Project the public reconstruction identity and use the public equations for
the forwarding transport's selected tapes, positions, state, input and output. -/
private lemma sph_select_fields {m k : ℕ} {Γ S : Type} {x : List Γ}
    (ι : Fin m ↪ Fin k) (d : Cfg k Γ S x) :
    (d.select ι).state = d.state ∧ (d.select ι).inputPos = d.inputPos ∧
      d.output ++ (d.select ι).output = d.output ∧
      (∀ i, (d.select ι).workTapes i = d.workTapes (ι i)) ∧
      (∀ i, (d.select ι).workTapePos i = d.workTapePos (ι i)) := by
  have hr := embedEmitCfg_select ι d
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg Cfg.state hr
    rwa [embedEmitCfg_state] at h
  · have h := congrArg Cfg.inputPos hr
    rwa [embedEmitCfg_inputPos] at h
  · have h := congrArg Cfg.output hr
    rwa [embedEmitCfg_output] at h
  · intro i
    have h : (embedEmitCfg ι d.workTapes d.workTapePos d.output (d.select ι)).workTapes
        (ι i) = d.workTapes (ι i) := congrArg (fun c => c.workTapes (ι i)) hr
    rwa [embedEmitCfg_selected_tape] at h
  · intro i
    have h : (embedEmitCfg ι d.workTapes d.workTapePos d.output (d.select ι)).workTapePos
        (ι i) = d.workTapePos (ι i) := congrArg (fun c => c.workTapePos (ι i)) hr
    rwa [embedEmitCfg_selected_pos] at h

/-- The record initializer occupies the record, radius and its own contiguous scratch bank. -/
private def sphInitSel (KI KR m : ℕ) : Fin (KI + 2) ↪ Fin (KI + KR + m + 2) :=
  Fin.castLEEmb (by omega)

/-- The initial-record phase on the diagonalizer's tape plan. Only the initializer's scratch
bank must be blank; the witness and runner banks are framed. [AB09, Theorem 4.8]

**Proof sketch.** Select the record, radius and initializer scratch tapes. Read the selected
configuration through the R1 reconstruction equation and its field equations. Apply the
published initial-record row, transport its run by R1 and reconstruct the framed endpoint. -/
private lemma sph_initial_record (M : FinTM Bool) (KR m : ℕ) :
    ∃ (KI : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry exit : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ p : ℤ, -1 ≤ p → p ≤ (recordLength M.k x.length s : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (KI + KR + m + 2), 2 ≤ j.val → j.val < KI + 2 →
          ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (recordLength M.k x.length s + ws.length + s + x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * (recordLength M.k x.length s + ws.length + s + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + (recordLength M.k x.length s : ℤ)
                  then fieldsTape (cfgRecord s (M.tm.initCfg x) 0) (q - d.workTapePos j)
                else d.workTapes j q} := by
  classical
  obtain ⟨KI, P, hF, hD, I, entry, exit, C, hI⟩ :=
    exists_recordInitTM M.k M.tm.q₀ (0 : Fin 3)
  letI := hF
  letI := hD
  let ι := sphInitSel KI KR m
  have h0 : ι 0 = 0 := Fin.ext rfl
  have h1 : ι 1 = 1 := Fin.ext rfl
  refine ⟨KI, P, hF, hD, embedEmitTM ι I, entry, exit, C, ?_⟩
  intro x s ws hws d hd hin hrad hslot hblank
  let a := d.select ι
  have hrecon : embedEmitCfg ι d.workTapes d.workTapePos d.output a = d :=
    embedEmitCfg_select ι d
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  obtain ⟨t, htime, hcut, henv, hr⟩ := hI s ws hws a (hstate.trans hd) (hinput.trans hin)
    (by intro p hp hp'; rw [htapes, hheads, h1]; exact hrad p hp hp')
    (by intro p hp hp'; rw [htapes, hheads, h0]; exact hslot p hp hp')
    (by
      intro j hj p
      rw [htapes]
      exact hblank (ι j) hj (by have := j.isLt; exact this) p)
  have hrun (u : ℕ) :
      (embedEmitTM ι I).runFrom d u =
        embedEmitCfg ι d.workTapes d.workTapePos d.output (I.runFrom a u) := by
    have h := embedEmitTM_runFrom ι I d.workTapes d.workTapePos d.output a u
    rwa [hrecon] at h
  refine ⟨t, htime, ?_, ?_, ?_⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · rw [hrun, hr, MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [embedEmitCfg_state]
    · rw [embedEmitCfg_inputPos]
      exact hinput
    · funext j q
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_tape]
        have hz : ι i = 0 ↔ i = 0 := by rw [← h0]; exact ι.injective.eq_iff
        simp only [a, hheads, htapes, hz]
      · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).1]
        have hj0 : j ≠ 0 := fun h => hj ⟨0, h0.trans h.symm⟩
        simp only [hj0, false_and, ite_false]
    · funext j
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_pos]
        exact hheads i
      · exact (embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2
    · rw [embedEmitCfg_output]
      exact houtput

/-- The runner uses record tape zero and its scratch bank, never the radius or witness bank. -/
private def sphRunnerSel (KI KR m : ℕ) : Fin (KR + 1) ↪ Fin (KI + KR + m + 2) where
  toFun i := ⟨if i.val = 0 then 0 else KI + 1 + i.val, by
    have := i.isLt
    split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' : (if i.val = 0 then 0 else KI + 1 + i.val) =
        (if j.val = 0 then 0 else KI + 1 + j.val) := congrArg Fin.val h
    split_ifs at h' <;> omega

/-- The published clocked runner on the diagonalizer's full tape plan. Its blank scratch
condition excludes both the radius tape and the dirty witness bank. [AB09, Theorem 4.8]

**Proof sketch.** Select record tape zero and the runner scratch bank. Apply the published
configuration-count runner with `summaryTag`, and transport its run, head envelope, silence
and nonexhausted record endpoint by R1. No new clock or simulation is constructed. -/
private lemma sph_runner_run (M : FinTM Bool) :
    ∃ (KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (KR + 1) (RecSym M.State (Fin 3)) P)
      (entry : P) (exit : WindowExit → P) (C : ℕ),
      (∀ e, exit e ≠ entry) ∧ Function.Injective exit ∧
      ∀ (KI m : ℕ) {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : Fin 3),
      c.InWindow s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        (∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
          ∀ p, d.workTapes j p = none) →
        let H := embedEmitTM (sphRunnerSel KI KR m) R
        ∃ (t : ℕ) (out : WindowExit),
          t ≤ C * 2 ^ (C * (recordLength M.k x.length s + 1)) ∧
          (H.runFrom d t).state = some (exit out) ∧
          (∀ u < t, ∀ e, (H.runFrom d u).state ≠ some (exit e)) ∧
          (∀ u ≤ t, ∀ j, |(H.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          (∀ u ≤ t, (H.runFrom d u).output = d.output) ∧
          (∀ N ≤ M.configBound x.length s + 1,
            (windowRun M.tm s summaryTag N c τ).1 ≠ .exhausted →
            out = (windowRun M.tm s summaryTag N c τ).1) ∧
          (out ≠ .exhausted → ∃ N,
            (windowRun M.tm s summaryTag N c τ).1 = out ∧
            H.runFrom d t =
              { d with
                state := some (exit out)
                workTapes := fun j q =>
                  if j = 0 ∧ d.workTapePos 0 ≤ q ∧
                      q < d.workTapePos 0 + (recordLength M.k x.length s : ℤ)
                    then fieldsTape (cfgRecord s (windowRun M.tm s summaryTag N c τ).2.1
                      (windowRun M.tm s summaryTag N c τ).2.2) (q - d.workTapePos 0)
                  else d.workTapes j q }) := by
  classical
  obtain ⟨KR, P, hF, hD, R, entry, exit, C, hne, hinj, hR⟩ :=
    exists_configWindowRunnerTM M summaryTag summaryTag_none
  letI := hF
  letI := hD
  refine ⟨KR, P, hF, hD, R, entry, exit, C, hne, hinj, ?_⟩
  intro KI m x s c τ hc d hd hrec hblank
  dsimp only
  let ι := sphRunnerSel KI KR m
  have h0 : ι 0 = 0 := by
    apply Fin.ext
    simp only [ι, sphRunnerSel, Function.Embedding.coeFn_mk, Fin.val_zero, if_pos]
  have hv (i : Fin (KR + 1)) (hi : i ≠ 0) : (ι i).val = KI + 1 + i.val := by
    have hz : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    exact if_neg hz
  let a := d.select ι
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  have hrec' : RecordAt a 0 (cfgRecord s c τ) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [htapes, hheads, h0]
    exact hrec p hp hp'
  obtain ⟨t, out, ht, he, hcut, henv, hs, _, hvote, hend⟩ := hR s c τ hc a
    (hstate.trans hd) hrec' (by
      intro i hi p
      rw [htapes]
      apply hblank (ι i)
      · rw [hv i hi]
        have : 0 < i.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hi)
        omega
      · rw [hv i hi]
        have := i.isLt
        omega)
  have hrun (u : ℕ) : (embedEmitTM ι R).runFrom d u =
      embedEmitCfg ι d.workTapes d.workTapePos d.output (R.runFrom a u) := by
    have h := embedEmitTM_runFrom ι R d.workTapes d.workTapePos d.output a u
    rwa [embedEmitCfg_select] at h
  refine ⟨t, out, ht, ?_, ?_, ?_, ?_, hvote, ?_⟩
  · rw [hrun, embedEmitCfg_state]
    exact he
  · intro u hu e
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu e
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · intro u hu
    rw [hrun, embedEmitCfg_output, hs u hu]
    exact houtput
  · intro hn
    obtain ⟨N, hN, hr⟩ := hend hn
    refine ⟨N, hN, ?_⟩
    rw [hrun, hr]
    apply Cfg.ext
    · rw [embedEmitCfg_state]
    · rw [embedEmitCfg_inputPos]
      exact hinput
    · funext j q
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_tape]
        have hz : ι i = 0 ↔ i = 0 := by rw [← h0]; exact ι.injective.eq_iff
        simp only [a, hheads, htapes, h0, hz]
      · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).1]
        have hj0 : j ≠ 0 := fun h => hj ⟨0, h0.trans h.symm⟩
        simp only [hj0, false_and, ite_false]
    · funext j
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_pos]
        exact hheads i
      · exact (embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2
    · rw [embedEmitCfg_output]
      exact houtput


/-- A one-tape record test selects the physical record tape alone. -/
private def sphRecordSel (k : ℕ) : Fin 1 ↪ Fin (k + 1) where
  toFun _ := 0
  inj' := fun _ _ _ => Subsingleton.elim _ _

/-- The final record test, on the full work bank, asks whether the encoded configuration is
halted and its output summary is the singleton-true summary. It preserves every physical field
except its finite verdict state. [AB09, Theorem 4.8]

**Proof sketch.** Apply the published one-tape record test to the selected record tape and
transport the framed endpoint and head envelope by R1. -/
private lemma sph_test_run (M : FinTM Bool) :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM 1 (RecSym M.State (Fin 3)) P) (entry yes no : P) (C : ℕ),
      yes ≠ no ∧
      ∀ (k : ℕ) {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : Fin 3)
        {ys : List (RecSym M.State (Fin 3))}
        (d : Cfg (k + 1) (RecSym M.State (Fin 3)) P ys),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        let H := embedEmitTM (sphRecordSel k) R
        ∃ t ≤ C * (recordLength M.k x.length s + 1),
          (∀ u < t, (H.runFrom d u).state ≠ some yes ∧
            (H.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, ∀ j, |(H.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          H.runFrom d t =
            {d with state := some (if c.state = none ∧ τ = 1 then yes else no)} := by
  classical
  obtain ⟨P, hF, hD, R, entry, yes, no, C, hne, hR⟩ :=
    exists_recordTestTM (k := M.k)
      (fun (q : Option M.State) (τ : Fin 3) => decide (q = none ∧ τ = 1))
  letI := hF
  letI := hD
  refine ⟨P, hF, hD, R, entry, yes, no, C, hne, ?_⟩
  intro k x s c τ ys d hd hrec
  dsimp only
  let ι := sphRecordSel k
  have h0 : ι 0 = 0 := rfl
  let a := d.select ι
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  have hrec' : RecordAt a 0 (cfgRecord s c τ) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [htapes, hheads, h0]
    exact hrec p hp hp'
  obtain ⟨t, ht, hcut, henv, hr⟩ := hR s c τ a (hstate.trans hd) hrec'
  rw [joinFields_cfgRecord_length] at ht henv
  have hrun (u : ℕ) : (embedEmitTM ι R).runFrom d u =
      embedEmitCfg ι d.workTapes d.workTapePos d.output (R.runFrom a u) := by
    have h := embedEmitTM_runFrom ι R d.workTapes d.workTapePos d.output a u
    rwa [embedEmitCfg_select] at h
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · rw [hrun, hr]
    apply embedEmitCfg_eq
    · simp only [decide_eq_true_eq]
    · exact hinput
    · exact houtput
    · intro i
      exact ⟨htapes i, hheads i⟩
    · exact fun _ _ => ⟨rfl, rfl⟩


/-- The emitter leaf as a framed contract, with a singleton head interval on every tape. -/
private def sphEmitContract {k : ℕ} {Γ : Type} (b : Γ) (x : List Γ) :
    Contract (sphEmitTM k b) () {none} Unit x where
  pre := fun _ _ => True
  time := fun _ _ => 1
  post := fun _ d => {d with state := none, output := d.output ++ [b]}
  lo := fun _ d => d.workTapePos
  hi := fun _ d => d.workTapePos
  run := fun _ d hd _ => (sph_emit_run b d hd).1
  exit_mem := fun _ _ _ _ => Set.mem_singleton _
  cut := by
    intro _ d hd _ u hu
    have : u = 0 := Nat.lt_one_iff.mp hu
    subst u
    rw [MultiTapeTM.runFrom_zero, hd]
    exact Option.some_ne_none _
  env := by
    intro _ d hd _ u hu j
    rw [(sph_emit_run b d hd).2 u hu]
    exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-- The two-exit seam attaches the opposite one-bit answer to each record-test verdict. -/
private def sphVerdictTM {k : ℕ} {Q P : Type} [DecidableEq P]
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (yes no : P) :
    MultiTapeTM k (RecSym Q (Fin 3)) ((P ⊕ Unit) ⊕ Unit) :=
  seamCompTM₂ R yes no (sphEmitTM k (RecSym.digit false)) ()
    (sphEmitTM k (RecSym.digit true)) ()

/-- A framed record test followed by its opposite-bit emitter halts, and inherits the test's
head envelope. This also covers a halted record whose summary is not singleton true.

**Proof sketch.** The two-exit run theorem selects the one-step emitter. The public branching
contract combines the test's certified interval with the emitter's stationary heads; the hull
is the test's original interval. -/
private lemma sph_verdict_run {k : ℕ} {Q P : Type} [DecidableEq P]
    {ys : List (RecSym Q (Fin 3))} (R : MultiTapeTM k (RecSym Q (Fin 3)) P)
    (entry yes no : P) (hne : yes ≠ no) (d : Cfg k (RecSym Q (Fin 3)) P ys)
    (hd : d.state = some entry) (b : Bool) (t B : ℕ)
    (hr : R.runFrom d t = {d with state := some (if b then yes else no)})
    (hcut : ∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no)
    (henv : ∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (B : ℤ)) :
    (sphVerdictTM R yes no).runFrom ((d.mapState Sum.inl).mapState Sum.inl) (t + 2) =
        { state := none
          inputPos := d.inputPos
          workTapes := d.workTapes
          workTapePos := d.workTapePos
          output := d.output ++ [RecSym.digit (!b)] } ∧
      ∀ u ≤ t + 2, ∀ j,
        |((sphVerdictTM R yes no).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).workTapePos j -
          d.workTapePos j| ≤ (B : ℤ) := by
  classical
  let d' := {d with state := some (if b then yes else no)}
  let d₀ := (d.mapState (Sum.inl : P → P ⊕ Unit)).mapState
    (Sum.inl : P ⊕ Unit → (P ⊕ Unit) ⊕ Unit)
  let C₀ : Contract R entry {some yes, some no} Unit ys :=
    { pre := fun _ a => a = d
      time := fun _ _ => t
      post := fun _ _ => d'
      lo := fun _ _ j => d.workTapePos j - B
      hi := fun _ _ j => d.workTapePos j + B
      run := by intro _ a _ ha; subst a; exact hr
      exit_mem := by
        intro _ _ _ _
        cases b
        · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
        · exact Set.mem_insert _ _
      cut := by
        intro _ a _ ha u hu
        subst a
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact hcut u hu
      env := by
        intro _ a _ ha u hu j
        subst a
        exact Contract.mem_Icc_of_abs_le (henv u hu j) }
  let C := Contract.branch hne C₀ (sphEmitContract (RecSym.digit false) ys)
    (sphEmitContract (RecSym.digit true) ys) (fun _ => ()) (fun _ => ())
    (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro)
  have hd₀ : d₀.state = some (Sum.inl (Sum.inl entry)) := by
    rw [Cfg.mapState_state, Cfg.mapState_state, hd]
    rfl
  have hp : C.pre () d₀ := by
    rw [Contract.branch_pre]
    change (d₀.mapState fun _ => entry) = d
    simp only [d₀, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  have htime : C.time () d₀ = t + 2 := by
    rw [Contract.branch_time]
    dsimp only [C₀, sphEmitContract]
    rw [ite_self]
  refine ⟨?_, ?_⟩
  · obtain ⟨hy, hn⟩ := seamCompTM₂_run_ofCfg R yes no hne
      (sphEmitTM k (RecSym.digit false)) () (sphEmitTM k (RecSym.digit true)) () hr hcut
    have ht : t + 2 = t + 1 + 1 := by omega
    rw [ht]
    cases b
    · have h := hn rfl 1
      rw [(sph_emit_run (RecSym.digit true) _
        (by rw [Cfg.mapState_state]; rfl)).1] at h
      rw [h]
      refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
      · rfl
      · rw [Cfg.mapState_inputPos]
      · funext j p
        rw [Cfg.mapState_workTapes]
      · funext j
        rw [Cfg.mapState_workTapePos]
      · rw [Cfg.mapState_output]
        rfl
    · have h := hy rfl 1
      rw [(sph_emit_run (RecSym.digit false) _
        (by rw [Cfg.mapState_state]; rfl)).1] at h
      rw [h]
      refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
      · rw [Cfg.mapState_state]; rfl
      · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
      · funext j p
        rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      · funext j
        rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      · rw [Cfg.mapState_output, Cfg.mapState_output]
        rfl
  · intro u hu j
    have h := C.env () d₀ hd₀ hp u (htime.symm ▸ hu) j
    rw [Contract.branch_lo, Contract.branch_hi] at h
    dsimp only [C₀, sphEmitContract] at h
    simp only [Cfg.mapState_workTapePos, ite_self] at h
    dsimp only [d'] at h
    rw [min_eq_left (by omega), max_eq_left (by omega), Finset.mem_Icc] at h
    dsimp only [d₀, sphVerdictTM] at h ⊢
    exact abs_le.mpr ⟨by omega, by omega⟩


/-- Any halted record returned by the window runner has the actual halting run's state and
output summary, regardless of which stopped round count the runner's record clause supplies.

**Proof sketch.** Compare that round count with one past a certified halting time by the
published stop-uniqueness theorem, then read the public output-summary characterization. -/
private lemma sph_summary (M : FinTM Bool) (x w : List Bool) (s t N : ℕ)
    (ht : M.ComputesInTime x w t)
    (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s)
    (hN : (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).1 = .halted) :
    ((windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.1).state = none ∧
      ((windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.2 = 1 ↔ w = [true]) := by
  have h := windowRun_summary_of_halts M x ht hs (Nat.lt_succ_self t)
  have heq := windowRun_stop_unique M.tm s summaryTag N (t + 1) (M.tm.initCfg x) 0
    (by rw [hN]; intro hbad; cases hbad)
    (by rw [h]; exact (fun hbad => WindowExit.noConfusion hbad : WindowExit.halted ≠ .exhausted))
  rw [heq, h]
  exact ⟨((FinTM.computesInTime_iff _ _ _ _).mp ht).1, outSummaryCode_eq_one_iff w⟩


/-- Once a seam dispatches, no other left-hand anchor is reached. Before dispatch it inherits
the host's avoidance of that anchor.

**Proof sketch.** The public left trajectory gives the host's cut and the distinct dispatch
anchor at the endpoint. The public right trajectory has only right-hand states or a halt. -/
private lemma sph_seam_avoids {k : ℕ} {Γ P Q : Type} [DecidableEq P] {x : List Γ}
    (A : MultiTapeTM k Γ P) (exit other : P) (B : MultiTapeTM k Γ Q) (entry : Q)
    {d d' : Cfg k Γ P x} {t : ℕ} (hr : A.runFrom d t = d')
    (he : d'.state = some exit) (hne : exit ≠ other)
    (hc : ∀ u < t, (A.runFrom d u).state ≠ some exit)
    (ho : ∀ u < t, (A.runFrom d u).state ≠ some other) :
    ∀ u, ((seamCompTM A exit B entry).runFrom (d.mapState Sum.inl) u).state ≠
      some (Sum.inl other) := by
  intro u hbad
  by_cases h : u ≤ t
  · rw [seamCompTM_runFrom_left A exit B entry hc u h, Cfg.mapState_state] at hbad
    have hh : (A.runFrom d u).state = some other :=
      Option.map_injective Sum.inl_injective hbad
    rcases lt_or_eq_of_le h with h | rfl
    · exact ho u h hh
    · rw [hr, he] at hh
      exact hne (Option.some.inj hh)
  · obtain ⟨w, rfl⟩ : ∃ w, u = t + 1 + w := Nat.exists_eq_add_of_le (Nat.lt_of_not_le h)
    rw [seamCompTM_runFrom_right A exit B entry hr he hc w, Cfg.mapState_state] at hbad
    obtain ⟨_, _, hq⟩ := Option.map_eq_some_iff.mp hbad
    exact Sum.inr_ne_inl hq

/-- Writing a layout's interior between its two blank boundary cells installs that record.
This is the shared boundary argument for the initializer and the stopped runner.

**Proof sketch.** Read `RecordAt` through its public equivalence. Inside the span use the
written field tape. The only other required offsets are minus one and the layout length;
both the old tape and the public layout boundary equations are blank there. -/
private lemma sph_written_record {k : ℕ} {Γ P : Type} {x : List Γ}
    (d : Cfg (k + 1) Γ P x) (q : Option P) (fs : List (List Γ)) (L : ℕ)
    (hL : (joinFields fs).length = L)
    (hl : d.workTapes 0 (d.workTapePos 0 - 1) = none)
    (hr : d.workTapes 0 (d.workTapePos 0 + L) = none) :
    RecordAt
      { d with
        state := q
        workTapes := fun j z =>
          if j = 0 ∧ d.workTapePos 0 ≤ z ∧ z < d.workTapePos 0 + (L : ℤ)
            then fieldsTape fs (z - d.workTapePos 0) else d.workTapes j z }
      0 fs := by
  rw [recordAt_iff]
  intro p hp hp'
  rw [hL] at hp'
  change (if (0 : Fin (k + 1)) = 0 ∧ d.workTapePos 0 ≤ d.workTapePos 0 + p ∧
      d.workTapePos 0 + p < d.workTapePos 0 + (L : ℤ)
    then fieldsTape fs (d.workTapePos 0 + p - d.workTapePos 0)
    else d.workTapes 0 (d.workTapePos 0 + p)) = fieldsTape fs p
  by_cases h : 0 ≤ p ∧ p < (L : ℤ)
  · rw [if_pos ⟨rfl, by omega, by omega⟩]
    congr 1
    ring
  · rw [if_neg (by rintro ⟨_, h₁, h₂⟩; exact h ⟨by omega, by omega⟩)]
    have : p = -1 ∨ p = (L : ℤ) := by omega
    rcases this with rfl | rfl
    · rw [fieldsTape_of_neg fs (by omega), ← sub_eq_add_neg]
      exact hl
    · rw [fieldsTape_of_length_le fs (by rw [hL])]
      exact hr


/-- The runner's three exits use published single-exit seams: a halted run enters the verdict
test, and either a window exit or exhaustion enters the true emitter. Exhaustion never reads
the unspecified record tape. -/
private def sphRunnerTailTM {k : ℕ} {Q P S : Type} [DecidableEq P] [DecidableEq S]
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (exit : WindowExit → P)
    (V : MultiTapeTM k (RecSym Q (Fin 3)) S) (entry : S) :
    MultiTapeTM k (RecSym Q (Fin 3)) (((P ⊕ S) ⊕ Unit) ⊕ Unit) :=
  seamCompTM
    (seamCompTM (seamCompTM R (exit .halted) V entry) (Sum.inl (exit .left))
      (sphEmitTM k (RecSym.digit true)) ())
    (Sum.inl (Sum.inl (exit .exhausted))) (sphEmitTM k (RecSym.digit true)) ()

/-- Run the runner's three-exit suffix. A certificate about the halted branch's output is
preserved; both other branches emit true. All heads remain in a common certified interval.

**Proof sketch.** On a halted verdict, both outer seams stay in their left segments while the
test runs. On a window exit, the middle seam dispatches the true emitter; on exhaustion, the
outer seam does so. The public seam trajectories transport the endpoint and each head bound.
The clock and record simulation remain entirely the supplied runner's. -/
private lemma sph_runner_tail_run {k : ℕ} {Q P S : Type} [DecidableEq P] [DecidableEq S]
    {ys : List (RecSym Q (Fin 3))}
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (exit : WindowExit → P)
    (hi : Function.Injective exit) (V : MultiTapeTM k (RecSym Q (Fin 3)) S) (entry : S)
    (d d' : Cfg k (RecSym Q (Fin 3)) P ys) (t B : ℕ) (out : WindowExit)
    (hr : R.runFrom d t = d') (he : d'.state = some (exit out))
    (hc : ∀ u < t, ∀ e, (R.runFrom d u).state ≠ some (exit e))
    (ho : d'.output = d.output)
    (hh : ∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (B : ℤ))
    (pred : Bool → Prop)
    (hv : out = .halted → ∃ v b,
      (V.runFrom (d'.mapState fun _ => entry) v).state = none ∧
      (V.runFrom (d'.mapState fun _ => entry) v).output =
        d'.output ++ [RecSym.digit b] ∧ pred b ∧
      ∀ u ≤ v, ∀ j,
        |(V.runFrom (d'.mapState fun _ => entry) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ)) :
    ∃ v b,
      ((sphRunnerTailTM R exit V entry).runFrom
        (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) v).state = none ∧
      ((sphRunnerTailTM R exit V entry).runFrom
        (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) v).output =
          d.output ++ [RecSym.digit b] ∧
      (out = .halted → pred b) ∧ (out ≠ .halted → b = true) ∧
      ∀ u ≤ v, ∀ j,
        |((sphRunnerTailTM R exit V entry).runFrom
          (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) u).workTapePos j -
          d.workTapePos j| ≤ (B : ℤ) := by
  let E := sphEmitTM k (RecSym.digit true : RecSym Q (Fin 3))
  let A := seamCompTM R (exit .halted) V entry
  let C := seamCompTM A (Sum.inl (exit .left)) E ()
  let a := d.mapState (Sum.inl : P → P ⊕ S)
  let a' := d'.mapState (Sum.inl : P → P ⊕ S)
  let c := a.mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)
  let c' := a'.mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)
  have hAp (u : ℕ) (hu : u ≤ t) : A.runFrom a u = (R.runFrom d u).mapState Sum.inl :=
    seamCompTM_runFrom_left R (exit .halted) V entry (fun u hu => hc u hu .halted) u hu
  have hAr : A.runFrom a t = a' := by rw [hAp t le_rfl, hr]
  have hAc (u : ℕ) (hu : u < t) (e : WindowExit) :
      (A.runFrom a u).state ≠ some (Sum.inl (exit e)) := by
    rw [hAp u hu.le, Cfg.mapState_state]
    intro h
    exact hc u hu e (Option.map_injective Sum.inl_injective h)
  have hCp (u : ℕ) (hu : u ≤ t) : C.runFrom c u = (A.runFrom a u).mapState Sum.inl :=
    seamCompTM_runFrom_left A (Sum.inl (exit .left)) E ()
      (fun u hu => hAc u hu .left) u hu
  have hCr : C.runFrom c t = c' := by rw [hCp t le_rfl, hAr]
  have hCc (u : ℕ) (hu : u < t) (e : WindowExit) :
      (C.runFrom c u).state ≠ some (Sum.inl (Sum.inl (exit e))) := by
    rw [hCp u hu.le, Cfg.mapState_state]
    intro h
    exact hAc u hu e (Option.map_injective Sum.inl_injective h)
  cases out with
  | halted =>
    obtain ⟨v, b, hvs, hvo, hpred, hvh⟩ := hv rfl
    have hAl := sph_seam_avoids R (exit .halted) (exit .left) V entry hr he
      (fun h => WindowExit.noConfusion (hi h)) (fun u hu => hc u hu .halted)
      (fun u hu => hc u hu .left)
    have hAe := sph_seam_avoids R (exit .halted) (exit .exhausted) V entry hr he
      (fun h => WindowExit.noConfusion (hi h)) (fun u hu => hc u hu .halted)
      (fun u hu => hc u hu .exhausted)
    have hC (u : ℕ) : C.runFrom c u = (A.runFrom a u).mapState Sum.inl :=
      seamCompTM_runFrom_left A (Sum.inl (exit .left)) E ()
        (fun u _ => hAl u) u le_rfl
    have hCe (u : ℕ) : (C.runFrom c u).state ≠ some (Sum.inl (Sum.inl (exit .exhausted))) := by
      rw [hC, Cfg.mapState_state]
      intro h
      exact hAe u (Option.map_injective Sum.inl_injective h)
    have hW (u : ℕ) : (sphRunnerTailTM R exit V entry).runFrom (c.mapState Sum.inl) u =
        ((A.runFrom a u).mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)).mapState Sum.inl := by
      rw [seamCompTM_runFrom_left C (Sum.inl (Sum.inl (exit .exhausted))) E ()
        (fun u _ => hCe u) u le_rfl, hC]
    have hA := seamCompTM_runFrom_right R (exit .halted) V entry hr he
      (fun u hu => hc u hu .halted) v
    have hAh := sph_seam_heads R (exit .halted) V entry hr he
      (fun u hu => hc u hu .halted) d.workTapePos B hh hvh
    refine ⟨t + 1 + v, b, ?_, ?_, fun _ => hpred, fun h => False.elim (h rfl), ?_⟩
    · rw [hW, hA, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, hvs]
      rfl
    · rw [hW, hA, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output, hvo, ho]
    · intro u hu j
      rw [hW, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      exact hAh u hu j
  | left =>
    have ha' : a'.state = some (Sum.inl (exit .left)) := by
      rw [Cfg.mapState_state, he]; rfl
    have havoid := sph_seam_avoids A (Sum.inl (exit .left))
      (Sum.inl (exit .exhausted)) E () hAr ha'
      (fun h => WindowExit.noConfusion (hi (Sum.inl.inj h)))
      (fun u hu => hAc u hu .left) (fun u hu => hAc u hu .exhausted)
    have hw (u : ℕ) : (sphRunnerTailTM R exit V entry).runFrom (c.mapState Sum.inl) u =
        (C.runFrom c u).mapState Sum.inl :=
      seamCompTM_runFrom_left C (Sum.inl (Sum.inl (exit .exhausted))) E ()
        (fun u _ => havoid u) u le_rfl
    have hea : (a'.mapState fun _ => ()).state = some () := by
      rw [Cfg.mapState_state, ha']; rfl
    obtain ⟨her, heh⟩ := sph_emit_run (RecSym.digit true) (a'.mapState fun _ => ()) hea
    have hC := seamCompTM_run_ofCfg A (Sum.inl (exit .left)) E () hAr ha'
      (fun u hu => hAc u hu .left) her
    have hAh : ∀ u ≤ t, ∀ j, |(A.runFrom a u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [hAp u hu, Cfg.mapState_workTapePos]
      exact hh u hu j
    have hEh : ∀ u ≤ 1, ∀ j,
        |(E.runFrom (a'.mapState fun _ => ()) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [heh u hu, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      exact hr ▸ hh t le_rfl j
    have hCh := sph_seam_heads A (Sum.inl (exit .left)) E () hAr ha'
      (fun u hu => hAc u hu .left) d.workTapePos B hAh hEh
    refine ⟨t + 1 + 1, true, ?_, ?_, fun h => WindowExit.noConfusion h, fun _ => rfl, ?_⟩
    · rw [hw, hC, Cfg.mapState_state, Cfg.mapState_state]; rfl
    · rw [hw, hC, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, Cfg.mapState_output, ho]
    · intro u hu j
      rw [hw, Cfg.mapState_workTapePos]
      exact hCh u hu j
  | exhausted =>
    have hc' : c'.state = some (Sum.inl (Sum.inl (exit .exhausted))) := by
      rw [Cfg.mapState_state, Cfg.mapState_state, he]; rfl
    have hec : (c'.mapState fun _ => ()).state = some () := by
      rw [Cfg.mapState_state, hc']; rfl
    obtain ⟨her, heh⟩ := sph_emit_run (RecSym.digit true) (c'.mapState fun _ => ()) hec
    have hW := seamCompTM_run_ofCfg C (Sum.inl (Sum.inl (exit .exhausted))) E ()
      hCr hc' (fun u hu => hCc u hu .exhausted) her
    have hCh : ∀ u ≤ t, ∀ j, |(C.runFrom c u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [hCp u hu, Cfg.mapState_workTapePos, hAp u hu, Cfg.mapState_workTapePos]
      exact hh u hu j
    have hEh : ∀ u ≤ 1, ∀ j,
        |(E.runFrom (c'.mapState fun _ => ()) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [heh u hu, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos]
      exact hr ▸ hh t le_rfl j
    have hWh := sph_seam_heads C (Sum.inl (Sum.inl (exit .exhausted))) E () hCr hc'
      (fun u hu => hCc u hu .exhausted) d.workTapePos B hCh hEh
    refine ⟨t + 1 + 1, true, ?_, ?_, fun h => WindowExit.noConfusion h, fun _ => rfl, hWh⟩
    · rw [hW, Cfg.mapState_state]; rfl
    · rw [hW, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, ho]


/-- The complete clocked simulation suffix on the tape plan. Starting from the universal
machine's initial record, it halts with one bit. Every halting run that fits the window receives
the opposite acceptance answer, and the suffix's head bound is uniform in the input's code.
[AB09, Theorem 4.8]

**Proof sketch.** Put the published runner and record test on disjoint framed selections, then
attach the tested opposite-bit verdict and the two unconditional true branches. The returned
record's blank boundaries follow from the old record and the public layout boundary equations.
Stop uniqueness identifies its summary with any certified halting run in the window. -/
private lemma sph_suffix (M : FinTM Bool) :
    ∃ (KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : ∀ KI m, MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry : P) (C : ℕ),
      ∀ (KI m : ℕ) {x : List Bool} (s : ℕ)
        (d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3)))),
        d.state = some entry → RecordAt d 0 (cfgRecord s (M.tm.initCfg x) 0) →
        (∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
          ∀ p, d.workTapes j p = none) →
        ∃ t b,
          ((D KI m).runFrom d t).state = none ∧
          ((D KI m).runFrom d t).output = d.output ++ [RecSym.digit b] ∧
          (∀ u ≤ t, ∀ j, |((D KI m).runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          (∀ w : List Bool,
            M.ComputesInTime x w (M.configBound x.length s) →
            M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
            b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KR, PR, hFR, hDR, R, ren, rex, CR, _, hinj, hR⟩ := sph_runner_run M
  letI := hFR
  letI := hDR
  obtain ⟨PT, hFT, hDT, T, ten, yes, no, CT, hne, hT⟩ := sph_test_run M
  letI := hFT
  letI := hDT
  let H (KI m : ℕ) := embedEmitTM (sphRunnerSel KI KR m) R
  let J (KI m : ℕ) := embedEmitTM (sphRecordSel (KI + KR + m + 1)) T
  let V (KI m : ℕ) := sphVerdictTM (J KI m) yes no
  let ven : (PT ⊕ Unit) ⊕ Unit := .inl (.inl ten)
  let D (KI m : ℕ) := sphRunnerTailTM (H KI m) rex (V KI m) ven
  let en : (((PR ⊕ ((PT ⊕ Unit) ⊕ Unit)) ⊕ Unit) ⊕ Unit) := .inl (.inl (.inl ren))
  refine ⟨KR, _, inferInstance, inferInstance, D, en, CR + CT, ?_⟩
  intro KI m x s d hd hrec hblank
  let a := d.mapState (fun _ => ren)
  have ha : a.state = some ren := by rw [Cfg.mapState_state, hd]; rfl
  have har : RecordAt a 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
    exact hrec p hp hp'
  have hab : ∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
      ∀ p, a.workTapes j p = none := by
    intro j hj hj' p
    rw [Cfg.mapState_workTapes]
    exact hblank j hj hj' p
  have hstart : (((a.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) = d := by
    simp only [a, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  obtain ⟨t, out, _, he, hc, hh, ho, hword, hend⟩ := hR KI m s (M.tm.initCfg x) 0
    (by rw [MultiTapeTM.initCfg_eq]; exact Cfg.inWindow_init _ _ s) a ha har hab
  let a' := (H KI m).runFrom a t
  have ha' : a'.state = some (rex out) := he
  let L := recordLength M.k x.length s
  let B := (CR + CT) * (L + 1)
  have hRB : CR * (L + 1) ≤ B := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hTB : CT * (L + 1) ≤ B := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  let pred (b : Bool) := ∀ w : List Bool,
    M.ComputesInTime x w (M.configBound x.length s) →
    M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
    b = !(decide (w = [true]))
  have hV : out = .halted → ∃ v b,
      ((V KI m).runFrom (a'.mapState fun _ => ven) v).state = none ∧
      ((V KI m).runFrom (a'.mapState fun _ => ven) v).output =
        a'.output ++ [RecSym.digit b] ∧ pred b ∧
      ∀ u ≤ v, ∀ j,
        |((V KI m).runFrom (a'.mapState fun _ => ven) u).workTapePos j - a.workTapePos j| ≤
          (B : ℤ) := by
    intro hout
    obtain ⟨N, hN, hr⟩ := hend (by rw [hout]; intro hbad; cases hbad)
    let cN := (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.1
    let τN := (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.2
    have hl : a.workTapes 0 (a.workTapePos 0 - 1) = none := by
      have h := (recordAt_iff _ _ _).mp har (-1) le_rfl (by omega)
      rw [fieldsTape_of_neg _ (by omega), ← sub_eq_add_neg] at h
      exact h
    have hright : a.workTapes 0 (a.workTapePos 0 + (L : ℤ)) = none := by
      have h := (recordAt_iff _ _ _).mp har (L : ℤ) (by omega)
        (by rw [joinFields_cfgRecord_length])
      rw [fieldsTape_of_length_le _ (by rw [joinFields_cfgRecord_length])] at h
      exact h
    have hrecN : RecordAt a' 0 (cfgRecord s cN τN) := by
      dsimp only [a']
      rw [hr]
      exact sph_written_record a _ (cfgRecord s cN τN) L
        (joinFields_cfgRecord_length _ _ _) hl hright
    let z := a'.mapState (fun _ => ten)
    have hz : z.state = some ten := by rw [Cfg.mapState_state, he]; rfl
    have hzr : RecordAt z 0 (cfgRecord s cN τN) := by
      rw [recordAt_iff] at hrecN ⊢
      intro p hp hp'
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      exact hrecN p hp hp'
    obtain ⟨v, _, hcutT, hheadsT, hrunT⟩ := hT (KI + KR + m + 1) s cN τN z hz hzr
    let b := decide (cN.state = none ∧ τN = 1)
    obtain ⟨hvr, hvh⟩ := sph_verdict_run (J KI m) ten yes no hne z hz b v (CT * (L + 1))
      (by simpa only [b, decide_eq_true_eq] using hrunT) hcutT hheadsT
    have hmaps : ((z.mapState Sum.inl).mapState Sum.inl) = a'.mapState (fun _ => ven) := by
      simp only [z, Cfg.mapState_mapState]
      rfl
    rw [hmaps] at hvr hvh
    refine ⟨v + 2, !b, ?_, ?_, ?_, ?_⟩
    · rw [hvr]
    · rw [hvr, Cfg.mapState_output]
    · intro w hw hs
      have hsumm := sph_summary M x w s (M.configBound x.length s) N hw hs (hN.trans hout)
      have hf : (cN.state = none ∧ τN = 1) ↔ w = [true] :=
        ⟨fun h => hsumm.2.mp h.2, fun h => ⟨hsumm.1, hsumm.2.mpr h⟩⟩
      dsimp only [b]
      exact congrArg Bool.not (decide_eq_decide.mpr hf)
    · intro u hu j
      have h := hvh u hu j
      have hzhead : z.workTapePos j = a.workTapePos j := by
        rw [Cfg.mapState_workTapePos]
        dsimp only [a']
        rw [hr]
      rw [hzhead] at h
      exact h.trans (by exact_mod_cast hTB)
  obtain ⟨v, b, hvs, hvo, hpred, _, hvh⟩ := sph_runner_tail_run (H KI m) rex hinj
    (V KI m) ven a a' t B out rfl he hc (ho t le_rfl)
    (fun u hu j => (hh u hu j).trans (by exact_mod_cast hRB)) pred hV
  rw [hstart] at hvs hvo hvh
  refine ⟨v, b, hvs, ?_, ?_, ?_⟩
  · rw [Cfg.mapState_output] at hvo
    exact hvo
  · intro u hu j
    have h := hvh u hu j
    rw [Cfg.mapState_workTapePos] at h
    exact h
  · intro w hw hs
    have hsummary := windowRun_summary_of_halts M x hw hs
      (Nat.lt_succ_self (M.configBound x.length s))
    have hout := hword (M.configBound x.length s + 1) le_rfl
      (by rw [hsummary]
          exact (fun hbad => WindowExit.noConfusion hbad : WindowExit.halted ≠ .exhausted))
    rw [hsummary] at hout
    exact hpred hout w hw hs


/-- Initialize the simulated machine's record from the radius word, then run the complete
clocked suffix. Scratch banks are disjoint from the radius and witness tapes.

**Proof sketch.** Invoke the framed initializer, install its record using the shared boundary
calculation, and pass its untouched runner bank to the suffix. The published seam composes the
runs; the initializer restores every head, so both envelopes have the same centre. -/
private lemma sph_record_suffix (M : FinTM Bool) (m : ℕ) :
    ∃ (KI KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ j : Fin (KI + KR + m + 2), j.val < KI + KR + 2 → j ≠ 1 →
          ∀ p, d.workTapes j p = none) →
        ∃ t b,
          (D.runFrom d t).state = none ∧
          (D.runFrom d t).output = d.output ++ [RecSym.digit b] ∧
          (∀ u ≤ t, ∀ j, |(D.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + ws.length + s + 1) : ℕ) : ℤ)) ∧
          (∀ w : List Bool,
            M.ComputesInTime x w (M.configBound x.length s) →
            M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
            b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KR, PS, hFS, hDS, S, sen, CS, hS⟩ := sph_suffix M
  letI := hFS
  letI := hDS
  obtain ⟨KI, PI, hFI, hDI, I, ien, iex, CI, hI⟩ := sph_initial_record M KR m
  letI := hFI
  letI := hDI
  let D := seamCompTM I iex (S KI m) sen
  refine ⟨KI, KR, PI ⊕ PS, inferInstance, inferInstance, D, Sum.inl ien, CI + CS, ?_⟩
  intro x s ws hws d hd hin hrad hblank
  let a := d.mapState (fun _ => ien)
  have ha : a.state = some ien := by rw [Cfg.mapState_state, hd]; rfl
  have hstart : a.mapState Sum.inl = d := by
    simp only [a, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  let L := recordLength M.k x.length s
  have hblank' (j : Fin (KI + KR + m + 2)) (hj : j.val < KI + KR + 2) (hj1 : j ≠ 1)
      (p : ℤ) : a.workTapes j p = none := by
    rw [Cfg.mapState_workTapes]
    exact hblank j hj hj1 p
  obtain ⟨t, _, hc, hh, hr⟩ := hI s ws hws a ha
    (by rw [Cfg.mapState_inputPos]; exact hin)
    (by
      intro p hp hp'
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      exact hrad p hp hp')
    (by
      intro p _ _
      exact hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
    (by
      intro j hj hj' p
      exact hblank' j (by omega) (by
        intro h; subst j; rw [Fin.val_one] at hj; omega) p)
  let a' := I.runFrom a t
  have he : a'.state = some iex := by dsimp only [a']; rw [hr]
  have hah (j) : a'.workTapePos j = d.workTapePos j := by
    dsimp only [a']; rw [hr, Cfg.mapState_workTapePos]
  have hao : a'.output = d.output := by dsimp only [a']; rw [hr, Cfg.mapState_output]
  have har : RecordAt a' 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    have hwritten := sph_written_record a (some iex) (cfgRecord s (M.tm.initCfg x) 0) L
      (joinFields_cfgRecord_length _ _ _)
      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
    dsimp only [a']
    rw [recordAt_iff] at hwritten ⊢
    intro p hp hp'
    rw [hr]
    exact hwritten p hp hp'
  let z := a'.mapState (fun _ => sen)
  have hz : z.state = some sen := by rw [Cfg.mapState_state, he]; rfl
  have hzr : RecordAt z 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    rw [recordAt_iff] at har ⊢
    intro p hp hp'
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
    exact har p hp hp'
  have hzb (j : Fin (KI + KR + m + 2)) (hj : KI + 2 ≤ j.val)
      (hj' : j.val < KI + KR + 2) (p : ℤ) : z.workTapes j p = none := by
    rw [Cfg.mapState_workTapes]
    dsimp only [a']
    rw [hr]
    have hj0 : j ≠ 0 := by intro h; subst j; rw [Fin.val_zero] at hj; omega
    simpa only [hj0, false_and, ↓reduceIte] using
      hblank' j hj' (by intro h; subst j; rw [Fin.val_one] at hj; omega) p
  obtain ⟨v, b, hvs, hvo, hvh, hpred⟩ := hS KI m s z hz hzr hzb
  have hrun := seamCompTM_run_ofCfg I iex (S KI m) sen (rfl : I.runFrom a t = a')
    he hc (rfl : (S KI m).runFrom z v = (S KI m).runFrom z v)
  rw [hstart] at hrun
  let B := (CI + CS) * (L + ws.length + s + 1)
  have hIB : CI * (L + ws.length + s + 1) ≤ B :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hSB : CS * (L + 1) ≤ B :=
    Nat.mul_le_mul (Nat.le_add_left _ _) (by omega)
  refine ⟨t + 1 + v, b, ?_, ?_, ?_, hpred⟩
  · rw [hrun, Cfg.mapState_state, hvs, Option.map_none]
  · rw [hrun, Cfg.mapState_output, hvo, Cfg.mapState_output, hao]
  · have hen := sph_seam_heads I iex (S KI m) sen (rfl : I.runFrom a t = a') he hc
      d.workTapePos B
      (by
        intro u hu j
        have h := hh u hu j
        rw [Cfg.mapState_workTapePos] at h
        exact h.trans (by exact_mod_cast hIB))
      (by
        intro u hu j
        have h := hvh u hu j
        rw [Cfg.mapState_workTapePos, hah] at h
        exact h.trans (by exact_mod_cast hSB))
    rw [hstart] at hen
    exact hen


/-- The complete record-and-radius envelope is linear in any bound above `logSpace`.
The coefficient depends only on the fixed simulated machine's tape count.

**Proof sketch.** The radius needs at most its value in binary digits. An input position
needs at most twice `logSpace n` digits. Insert these bounds in the public record-length
formula and absorb the additive constants using the logarithmic floor. -/
private lemma sph_record_size (g : ℕ → ℕ) (hg : ∀ n, logSpace n ≤ g n) (k n : ℕ) :
    recordLength k n (g n) + (g n).bits.length + g n + 1 ≤ (4 * k + 9) * g n := by
  have hfloor : 1 ≤ g n := by have h := hg n; rw [logSpace_eq] at h; omega
  have hb : (g n).bits.length ≤ g n := length_bits_le_self _
  have hp : posWidth n ≤ 2 * g n := by
    rw [posWidth_eq]
    have hpow : n + 1 < 2 ^ (Nat.log 2 n + 2) :=
      (LogProg.succ_le_two_pow_log n).trans_lt
        (Nat.pow_lt_pow_right (by decide) (by omega))
    have h := LogProg.length_bits_le hpow
    have hg' := hg n
    rw [logSpace_eq] at hg'
    omega
  rw [recordLength_eq]
  have hk : k ≤ k * g n := Nat.le_mul_of_pos_right k hfloor
  nlinarith


/-- The diagonalizer after validation, on embedded binary inputs. It computes the radius,
rewinds, initializes the record, and runs the clocked opposite-verdict suffix.

**Proof sketch.** Use the returning witness capture and two existing seams. Its blank frame
provides the initializer and runner banks. Add the radius, rewind and record envelopes,
then use the logarithmic floor to bound their sum by a fixed multiple of the radius. -/
private lemma sph_valid_machine (M : FinTM Bool) (g : ℕ → ℕ)
    (hg : ∀ n, logSpace n ≤ g n) (c : ℕ) (G : FinTM Bool)
    (hG : G.ComputesInSpace (fun x => (g x.length).bits) (fun n => c * g n)) :
    ∃ (k : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : MultiTapeTM k (RecSym M.State (Fin 3)) P) (entry : P) (B : ℕ),
      ∀ x : List Bool, ∃ t b,
        (D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) t).state = none ∧
        (D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) t).output =
          [RecSym.digit b] ∧
        (∀ u ≤ t, ∀ j,
          |(D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) u).workTapePos j| ≤
            ((B * g x.length : ℕ) : ℤ)) ∧
        (∀ w : List Bool,
          M.ComputesInTime x w (M.configBound x.length (g x.length)) →
          M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
          b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KI, KR, PS, hFS, hDS, S, sen, C, hS⟩ := sph_record_suffix M G.k
  letI := hFS
  letI := hDS
  let k := KI + KR + G.k + 2
  let e := RecSym.digitEmb M.State (Fin 3)
  let ι := sphWitnessSel KI KR G.k
  let R := embedSilentRetTM ι 1 (G.tm.liftSymbols e)
  let W := sphRewindsTM k M.State 1
  let wen : (Bool ⊕ InputRewindPhase) ⊕ RewindPhase := .inl (.inl false)
  let A := seamCompTM W (.inr RewindPhase.done) S sen
  let aen : ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) ⊕ PS := .inl wen
  let D := seamCompTM R (.inr ()) A aen
  let en : (G.State ⊕ Unit) ⊕ (((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) ⊕ PS) :=
    .inl (.inl G.tm.q₀)
  let B := c + 3 + C * (4 * M.k + 9)
  refine ⟨k, _, inferInstance, inferInstance, D, en, B, ?_⟩
  intro x
  let ws := (g x.length).bits
  let start := (embedSilentCfg ι 1 (fun _ _ => none) (fun _ => 0) [] []
    ((G.tm.initCfg x).liftSymbols e)).mapState (Sum.inl : G.State → G.State ⊕ Unit)
  have hcap := sph_witness_cap KI KR G.k
  have hstart : start.mapState Sum.inl = Cfg.init en (x.map e) := by
    refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
    · rw [Cfg.mapState_state, embedSilentCfg_state,
        Cfg.liftSymbols_state, MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_state]
      rfl
    · rw [Cfg.mapState_inputPos, embedSilentCfg_inputPos,
        Cfg.liftSymbols_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos, Cfg.init_inputPos]
      apply Fin.ext
      change (1 : Fin (x.length + 2)).val = (1 : Fin ((x.map e).length + 2)).val
      rw [Fin.val_one, Fin.val_one]
    · funext j p
      rw [Cfg.mapState_workTapes, Cfg.init_workTapes]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedSilentCfg_selected_tape, Cfg.liftSymbols_workTapes,
          MultiTapeTM.initCfg_eq, Cfg.init_workTapes, Option.map_none]
      · by_cases hjc : j = 1
        · subst j
          rw [(embedSilentCfg_cap ι 1 hcap _ _ [] [] _).1,
            Cfg.liftSymbols_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
            List.map_nil, List.nil_append, FinTM.bufferTape_nil]
        · rw [(embedSilentCfg_unselected ι 1 _ _ [] [] _ j hj hjc).1]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedSilentCfg_selected_pos, Cfg.liftSymbols_workTapePos,
          MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
      · by_cases hjc : j = 1
        · subst j
          rw [(embedSilentCfg_cap ι 1 hcap _ _ [] [] _).2,
            Cfg.liftSymbols_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
            List.map_nil, List.nil_append, List.length_nil, Nat.cast_zero]
        · rw [(embedSilentCfg_unselected ι 1 _ _ [] [] _ j hj hjc).2]
    · rw [Cfg.mapState_output, embedSilentCfg_output, Cfg.init_output]
  obtain ⟨t, hrs, hrc, hrt, hrp, hrf, hro, _, hrh⟩ :=
    sph_radius_run KI KR (Q := M.State) g c G hG x (fun _ _ => none) (fun _ => 0) []
  let r := R.runFrom start t
  have hrs' : r.state = some (Sum.inr ()) := hrs
  let d := r.mapState (fun _ => false)
  have hd : d.state = some false := by rw [Cfg.mapState_state, hrs']; rfl
  obtain ⟨u, hwr, hwc, hwh⟩ := sph_rewinds_run KI KR G.k ws d hd
    (by funext p; rw [Cfg.mapState_workTapes]; exact congrFun hrt p)
    (by rw [Cfg.mapState_workTapePos]; exact hrp)
  have hwi : (d.mapState Sum.inl).mapState Sum.inl = r.mapState (fun _ => wen) := by
    dsimp only [d]
    rw [Cfg.mapState_mapState, Cfg.mapState_mapState]
    rfl
  rw [hwi] at hwr hwc hwh
  let z := W.runFrom (r.mapState fun _ => wen) u
  have hze : z.state = some (Sum.inr RewindPhase.done) := by dsimp only [z]; rw [hwr]
  have hzt (j p) : z.workTapes j p = r.workTapes j p := by
    dsimp only [z]; rw [hwr, Cfg.mapState_workTapes]
  have hzh (j) : z.workTapePos j = Function.update r.workTapePos 1 0 j := by
    dsimp only [z]; rw [hwr]
    have hheads : d.workTapePos = r.workTapePos := by
      funext i
      rw [Cfg.mapState_workTapePos]
    rw [hheads]
  have hzo : z.output = [] := by
    dsimp only [z]; rw [hwr, Cfg.mapState_output]
    exact hro t le_rfl
  let y := z.mapState (fun _ => sen)
  have hy : y.state = some sen := by rw [Cfg.mapState_state, hze]; rfl
  obtain ⟨v, b, hss, hso, hsh, hpred⟩ := hS (g x.length) ws
    ((counterValue_eq _).symm.trans (counterValue_bits _)) y hy
    (by rw [Cfg.mapState_inputPos]; dsimp only [z]; rw [hwr])
    (by
      intro p _ _
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hzh, Function.update_self,
        zero_add, hzt, hrt])
    (by
      intro j hj hjc p
      rw [Cfg.mapState_workTapes, hzt]
      have hjr : j ∉ Set.range ι := by
        rintro ⟨i, hi⟩
        have h := congrArg Fin.val hi
        simp only [ι, sphWitnessSel, Function.Embedding.coeFn_mk] at h
        omega
      exact congrFun (hrf j hjr hjc).1 p)
  have hai : (r.mapState (fun _ => wen)).mapState Sum.inl = r.mapState (fun _ => aen) := by
    rw [Cfg.mapState_mapState]
    rfl
  have hAr := seamCompTM_run_ofCfg W (.inr RewindPhase.done) S sen
    (rfl : W.runFrom (r.mapState fun _ => wen) u = z) hze hwc
    (rfl : S.runFrom y v = S.runFrom y v)
  rw [hai] at hAr
  have hDr := seamCompTM_run_ofCfg R (.inr ()) A aen
    (rfl : R.runFrom start t = r) hrs' hrc hAr
  rw [hstart] at hDr
  let rR := c * g x.length + ws.length
  let rW := rR + (ws.length + 1)
  let rS := C * (recordLength M.k x.length (g x.length) + ws.length + g x.length + 1)
  let radius := rW + rS
  have hRH (a : ℕ) (ha : a ≤ t) (j) : |(R.runFrom start a).workTapePos j| ≤ (rR : ℤ) := by
    simpa only [abs_zero, zero_add] using hrh a ha j
  have hWH (a : ℕ) (ha : a ≤ u) (j) :
      |(W.runFrom (r.mapState fun _ => wen) a).workTapePos j| ≤ (rW : ℤ) := by
    have h₁ := hwh a ha j
    rw [Cfg.mapState_workTapePos] at h₁
    have h₂ := hRH t le_rfl j
    calc
      _ ≤ |(W.runFrom (r.mapState fun _ => wen) a).workTapePos j - r.workTapePos j| +
          |r.workTapePos j| := by
            simpa only [sub_zero] using abs_sub_le
              ((W.runFrom (r.mapState fun _ => wen) a).workTapePos j) (r.workTapePos j) (0 : ℤ)
      _ ≤ ((ws.length + 1 : ℕ) : ℤ) + (rR : ℤ) := add_le_add h₁ h₂
      _ = _ := by dsimp only [rW]; push_cast; ring
  have hSH (a : ℕ) (ha : a ≤ v) (j) : |(S.runFrom y a).workTapePos j| ≤ (radius : ℤ) := by
    have h₁ := hsh a ha j
    rw [Cfg.mapState_workTapePos] at h₁
    have h₂ := hWH u le_rfl j
    calc
      _ ≤ |(S.runFrom y a).workTapePos j - z.workTapePos j| + |z.workTapePos j| := by
        simpa only [sub_zero] using
          abs_sub_le ((S.runFrom y a).workTapePos j) (z.workTapePos j) (0 : ℤ)
      _ ≤ (rS : ℤ) + (rW : ℤ) := add_le_add h₁ h₂
      _ = _ := by dsimp only [radius]; push_cast; ring
  have hAH := sph_seam_heads W (.inr RewindPhase.done) S sen
    (rfl : W.runFrom (r.mapState fun _ => wen) u = z) hze hwc (fun _ => 0) radius
    (by
      intro a ha j
      rw [sub_zero]
      exact (hWH a ha j).trans (by dsimp only [radius]; push_cast; omega))
    (by intro a ha j; rw [sub_zero]; exact hSH a ha j)
  rw [hai] at hAH
  have hDH := sph_seam_heads R (.inr ()) A aen
    (rfl : R.runFrom start t = r) hrs' hrc (fun _ => 0) radius
    (by
      intro a ha j
      rw [sub_zero]
      exact (hRH a ha j).trans (by dsimp only [radius, rW]; push_cast; omega)) hAH
  rw [hstart] at hDH
  have hsize : radius ≤ B * g x.length := by
    have hrecord := sph_record_size g hg M.k x.length
    have hbits : ws.length ≤ g x.length := length_bits_le_self _
    have hfloor : 1 ≤ g x.length := by have h := hg x.length; rw [logSpace_eq] at h; omega
    have h := Nat.mul_le_mul_left C hrecord
    dsimp only [radius, rW, rR, rS, B]
    nlinarith
  refine ⟨t + 1 + (u + 1 + v), b, ?_, ?_, ?_, hpred⟩
  · rw [hDr, Cfg.mapState_state, Cfg.mapState_state, hss, Option.map_none, Option.map_none]
  · rw [hDr, Cfg.mapState_output, Cfg.mapState_output, hso, Cfg.mapState_output,
      hzo, List.nil_append]
  · intro a ha j
    have h := hDH a ha j
    rw [sub_zero] at h
    exact h.trans (by exact_mod_cast hsize)


/-- Turn a certified bounded halting run into a first-exit contract at its first halt.

**Proof sketch.** The public first-halt theorem preserves the endpoint and shortens the
run. Restrict the given head envelope to that prefix and use equality as the precondition. -/
private lemma sph_halt_contract {k : ℕ} {Γ P : Type} {ys : List Γ}
    (M : MultiTapeTM k Γ P) (entry : P) (d : Cfg k Γ P ys) (t B : ℕ)
    (ht : (M.runFrom d t).state = none)
    (hh : ∀ u ≤ t, ∀ j, |(M.runFrom d u).workTapePos j| ≤ (B : ℤ)) :
    ∃ C : Contract M entry {none} Unit ys,
      (∀ a, C.pre () a ↔ a = d) ∧ C.post () d = M.runFrom d t ∧
      (∀ a j, C.lo () a j = -(B : ℤ) ∧ C.hi () a j = (B : ℤ)) := by
  obtain ⟨u, hu, hc, he⟩ := M.exists_first_halt d ht
  let C : Contract M entry {none} Unit ys :=
    { pre := fun _ a => a = d
      time := fun _ _ => u
      post := fun _ _ => M.runFrom d t
      lo := fun _ _ _ => -(B : ℤ)
      hi := fun _ _ _ => (B : ℤ)
      run := by intro _ a _ ha; subst a; exact he
      exit_mem := by intro _ a _ _; exact ht
      cut := by
        intro _ a _ ha v hv
        subst a
        exact hc v hv
      env := by
        intro _ a _ ha v hv j
        subst a
        rw [Finset.mem_Icc]
        exact abs_le.mp (hh v (hv.trans hu) j) }
  exact ⟨C, fun _ => Iff.rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩


/-- Add the published input validator to a binary-input machine. Foreign symbols are rejected
before its work tapes are used, so the resulting finite machine is space bounded on all inputs.

**Proof sketch.** The validation contract branches to a first-halt contract of the supplied
machine or the false emitter. Both use the same absolute head interval. Read the branch's
public endpoint and envelope equations, then sum the interval bound over the physical tapes. -/
private lemma sph_validated_machine {k : ℕ} {Q P : Type} [Fintype Q] [DecidableEq Q]
    [Fintype P] [DecidableEq P]
    (V : MultiTapeTM k (RecSym Q (Fin 3)) P) (entry : P) (S : ℕ → ℕ)
    (pred : List Bool → Bool → Prop)
    (hV : ∀ x : List Bool, ∃ t b,
      (V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) t).state = none ∧
      (V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) t).output =
        [RecSym.digit b] ∧
      (∀ u ≤ t, ∀ j,
        |(V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) u).workTapePos j| ≤
          (S x.length : ℤ)) ∧ pred x b) :
    ∃ D : FinTM (RecSym Q (Fin 3)),
      ∀ ys : List (RecSym Q (Fin 3)), ∃ t b,
        D.ComputesInTime ys [RecSym.digit b] t ∧
        D.tm.spaceUsed (D.tm.initCfg ys) t ≤ k * (2 * S ys.length + 1) ∧
        ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x b := by
  classical
  let F : MultiTapeTM k (RecSym Q (Fin 3)) (ScanPhase Bool) :=
    inputFoldTM k (fun a c => a && sphDigit c) true
  let E := sphEmitTM k (RecSym.digit false : RecSym Q (Fin 3))
  let R := seamCompTM₂ F (.done true) (.done false) V entry E ()
  let en : (ScanPhase Bool ⊕ P) ⊕ Unit := .inl (.inl (.fwd true))
  let D : FinTM (RecSym Q (Fin 3)) :=
    { k := k
      State := (ScanPhase Bool ⊕ P) ⊕ Unit
      fintypeState := inferInstance
      decEqState := inferInstance
      tm := {R with q₀ := en} }
  refine ⟨D, ?_⟩
  intro ys
  let a : Cfg k (RecSym Q (Fin 3)) (ScanPhase Bool) ys := Cfg.init (.fwd true) ys
  obtain ⟨b, hr, hvalid, hcut, hheads⟩ := sph_validation_run a
    (Cfg.init_state _ _) (Cfg.init_inputPos _ _)
  let a' := {a with state := some (ScanPhase.done b)}
  let radius := S ys.length
  have hrad : (0 : ℤ) ≤ radius := Int.natCast_nonneg _
  let C₀ : Contract F (.fwd true) {some (.done true), some (.done false)} Unit ys :=
    { pre := fun _ d => d = a
      time := fun _ _ => 2 * ys.length + 2
      post := fun _ _ => a'
      lo := fun _ _ _ => -(radius : ℤ)
      hi := fun _ _ _ => (radius : ℤ)
      run := by intro _ d _ hd; subst d; exact hr
      exit_mem := by
        intro _ d _ _
        cases b <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, a', or_true, true_or]
      cut := by
        intro _ d _ hd u hu hm
        subst d
        rcases hm with hm | hm
        · exact hcut u hu true hm
        · exact hcut u hu false hm
      env := by
        intro _ d _ hd u hu j
        subst d
        rw [hheads j u hu, Cfg.init_workTapePos, Finset.mem_Icc]
        exact ⟨by omega, hrad⟩ }
  have hstart₁ : a'.mapState (fun _ => entry) = Cfg.init entry ys := by
    refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
    · rw [Cfg.init_state]; rfl
    · rw [Cfg.init_inputPos, Cfg.init_inputPos]
    · funext j p; rw [Cfg.init_workTapes, Cfg.init_workTapes]
    · funext j; rw [Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.init_output, Cfg.init_output]
  have hC₁ : ∃ C₁ : Contract V entry {none} Unit ys,
      (b = true → C₁.pre () (Cfg.init entry ys)) ∧
      (∀ d j, C₁.lo () d j = -(radius : ℤ) ∧ C₁.hi () d j = (radius : ℤ)) ∧
      (b = true → ∃ ans,
        (C₁.post () (Cfg.init entry ys)).state = none ∧
        (C₁.post () (Cfg.init entry ys)).output = [RecSym.digit ans] ∧
        ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x ans) := by
    by_cases hb : b = true
    · obtain ⟨x, rfl⟩ := hvalid.mp hb
      obtain ⟨v, ans, hvs, hvo, hvh, hp⟩ := hV x
      obtain ⟨C₁, hpre, hpost, henv⟩ := sph_halt_contract V entry
        (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) v radius hvs
        (by simpa only [radius, List.length_map] using hvh)
      refine ⟨C₁, fun _ => (hpre _).mpr rfl, henv, ?_⟩
      intro _
      refine ⟨ans, ?_, ?_, ?_⟩
      · rw [hpost]; exact hvs
      · rw [hpost]; exact hvo
      · intro x' hx
        have heq : x = x' := List.map_injective_iff.mpr (RecSym.digitEmb Q (Fin 3)).injective hx
        subst x'
        exact hp
    · let C₁ : Contract V entry {none} Unit ys :=
        { pre := fun _ _ => False
          time := fun _ _ => 0
          post := fun _ d => d
          lo := fun _ _ _ => -(radius : ℤ)
          hi := fun _ _ _ => (radius : ℤ)
          run := by intro _ _ _ h; exact False.elim h
          exit_mem := by intro _ _ _ h; exact False.elim h
          cut := by intro _ _ _ h; exact False.elim h
          env := by intro _ _ _ h; exact False.elim h }
      exact ⟨C₁, fun h => False.elim (hb h), fun _ _ => ⟨rfl, rfl⟩,
        fun h => False.elim (hb h)⟩
  obtain ⟨C₁, hpre₁, henv₁, hpost₁⟩ := hC₁
  have hne : (ScanPhase.done true : ScanPhase Bool) ≠ .done false := by
    intro h; cases h
  let C := Contract.branch hne C₀ C₁ (sphEmitContract (RecSym.digit false) ys)
    (fun _ => ()) (fun _ => ())
    (by
      intro _ d _ hd he
      have hb : b = true := ScanPhase.done.inj (Option.some.inj he)
      change C₁.pre () (a'.mapState fun _ => entry)
      rw [hstart₁]
      exact hpre₁ hb)
    (fun _ _ _ _ _ => True.intro)
  let d₀ : Cfg k (RecSym Q (Fin 3)) ((ScanPhase Bool ⊕ P) ⊕ Unit) ys := Cfg.init en ys
  have hd₀ : d₀.state = some (Sum.inl (Sum.inl (.fwd true))) := Cfg.init_state _ _
  have hpre : C.pre () d₀ := by
    rw [Contract.branch_pre]
    change (d₀.mapState fun _ => ScanPhase.fwd true) = a
    refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
    · rw [Cfg.init_state, Cfg.init_state]; rfl
    · rw [Cfg.init_inputPos, Cfg.init_inputPos]
    · funext j p; rw [Cfg.init_workTapes, Cfg.init_workTapes]
    · funext j; rw [Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.init_output, Cfg.init_output]
  have hh (u : ℕ) (hu : u ≤ C.time () d₀) (j) :
      |(R.runFrom d₀ u).workTapePos j| ≤ (radius : ℤ) := by
    have h := C.env () d₀ hd₀ hpre u hu j
    rw [Contract.branch_lo, Contract.branch_hi] at h
    dsimp only [C₀, sphEmitContract] at h
    rw [(henv₁ _ j).1, (henv₁ _ j).2] at h
    simp only [a', a, Cfg.mapState_workTapePos, Cfg.init_workTapePos] at h
    split_ifs at h
    · simpa only [min_self, max_self, Finset.mem_Icc, ← abs_le] using h
    · rw [min_eq_left (by omega), max_eq_left hrad, Finset.mem_Icc] at h
      exact abs_le.mpr h
  have hend : ∃ ans,
      (R.runFrom d₀ (C.time () d₀)).state = none ∧
      (R.runFrom d₀ (C.time () d₀)).output = [RecSym.digit ans] ∧
      ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x ans := by
    have hr' := C.run () d₀ hd₀ hpre
    rw [Contract.branch_post] at hr'
    dsimp only [C₀] at hr'
    by_cases hb : b = true
    · obtain ⟨ans, hs, ho, hp⟩ := hpost₁ hb
      rw [if_pos (by change some (ScanPhase.done b) = some (.done true); rw [hb]),
        hstart₁] at hr'
      refine ⟨ans, ?_, ?_, hp⟩
      · rw [hr', Cfg.mapState_state, Cfg.mapState_state, hs, Option.map_none, Option.map_none]
      · rw [hr', Cfg.mapState_output, Cfg.mapState_output, ho]
    · rw [if_neg (by intro h; exact hb (ScanPhase.done.inj (Option.some.inj h)))] at hr'
      refine ⟨false, ?_, ?_, ?_⟩
      · rw [hr', Cfg.mapState_state]
        rfl
      · rw [hr', Cfg.mapState_output]
        dsimp only [sphEmitContract]
        rw [Cfg.mapState_output, Cfg.init_output, List.nil_append]
      · intro x hx
        exact False.elim (hb (hvalid.mpr ⟨x, hx⟩))
  obtain ⟨ans, hstate, hout, hp⟩ := hend
  have hrun (u : ℕ) : D.tm.runFrom (D.tm.initCfg ys) u = R.runFrom d₀ u := by
    rw [MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀]
  refine ⟨C.time () d₀, ans, ?_, ?_, hp⟩
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [hrun]
    exact ⟨hstate, hout⟩
  · apply MultiTapeTM.spaceUsed_le_of_abs_le
    intro u hu j
    rw [hrun, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos, sub_zero]
    exact hh u hu j


/-- A space-constructible radius admits a diagonal language for any fixed finite binary
machine: whenever that machine halts within the radius, the language gives the opposite bit.

**Proof sketch.** Validate before computing the radius and running the fixed machine's window.
Choose the resulting total output as the language's indicator. The all-input head envelope
bounds space at the halting time and hence at every time. Apply the published alphabet
reduction and absorb its constants using the constructible bound's logarithmic floor. -/
private lemma sph_diagonal_language (M : FinTM Bool) (g : ℕ → ℕ) (hg : SpaceConstructible g) :
    ∃ L : Language Bool, L ∈ SPACE g ∧
      ∀ (x w : List Bool),
        M.ComputesInTime x w (M.configBound x.length (g x.length)) →
        M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
        MultiTapeTM.indicator (L : Set (List Bool)) x = !(decide (w = [true])) := by
  classical
  obtain ⟨hfloor, c, _, G, hG⟩ := (spaceConstructible_iff g).mp hg
  obtain ⟨k, P, hFP, hDP, V, entry, B, hV⟩ := sph_valid_machine M g hfloor c G hG
  letI := hFP
  letI := hDP
  let pred (x : List Bool) (b : Bool) := ∀ w : List Bool,
    M.ComputesInTime x w (M.configBound x.length (g x.length)) →
    M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
    b = !(decide (w = [true]))
  obtain ⟨D, hD⟩ := sph_validated_machine V entry (fun n => B * g n) pred hV
  choose t answer ht hs hp using hD
  let e := RecSym.digitEmb M.State (Fin 3)
  let L : Language Bool := {x | answer (x.map e) = true}
  have hind (x : List Bool) : MultiTapeTM.indicator (L : Set (List Bool)) x =
      answer (x.map e) := by
    let bit := MultiTapeTM.indicator (L : Set (List Bool)) x
    let E : FinTM Bool :=
      { k := 0
        State := Unit
        fintypeState := inferInstance
        decEqState := inferInstance
        tm := sphEmitTM 0 bit }
    have hleaf := (sph_emit_run bit (E.tm.initCfg x)
      (by rw [MultiTapeTM.initCfg_eq, Cfg.init_state])).1
    have he : E.ComputesInTime x [bit] 1 := by
      apply (FinTM.computesInTime_iff _ _ _ _).mpr
      rw [hleaf]
      refine ⟨rfl, ?_⟩
      rw [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append]
    have hlang := (E.toFinNDTM_haltsWithin_and_accepts_iff (L := L) he).2
    have hacc : E.toFinNDTM.AcceptsWithin x 1 ↔ bit = true := by
      rw [FinNDTM.acceptsWithin_iff]
      constructor
      · rintro ⟨w, hw, _, ho⟩
        simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
          MultiTapeTM.toNDTM_runWith, hw] at ho
        rw [hleaf, MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append] at ho
        exact List.singleton_inj.mp ho
      · intro hb
        refine ⟨[false], rfl, ?_, ?_⟩
        · simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
            MultiTapeTM.toNDTM_runWith, List.length_singleton, hleaf]
        · simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
            MultiTapeTM.toNDTM_runWith, List.length_singleton]
          rw [hleaf, MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append, hb]
    have htest : answer (x.map e) = true ↔ bit = true := hlang.trans hacc
    change bit = answer (x.map e)
    exact Bool.eq_iff_iff.mpr htest.symm
  let S (n : ℕ) := k * (2 * (B * g n) + 1)
  obtain ⟨c', N, hN⟩ := FinTM.decidesInSpace_of_alphabetReduction e D L S
    (by
      intro x
      refine ⟨t (x.map e), ?_⟩
      rw [hind, List.map_singleton, RecSym.digitEmb_apply]
      exact ht (x.map e))
    (by
      intro ys u
      exact (ht ys).spaceUsed_le_of_halt (hs ys) u)
  have hL : L ∈ SPACE (fun n => S n + 1) := mem_SPACE_iff.mpr ⟨c', N, hN⟩
  have hb (n : ℕ) : S n + 1 ≤ (k * (2 * B + 1) + 1) * g n := by
    have hn : 1 ≤ g n := by have h := hfloor n; rw [logSpace_eq] at h; omega
    calc
      _ ≤ k * (2 * (B * g n) + g n) + g n :=
        Nat.add_le_add (Nat.mul_le_mul_left k (Nat.add_le_add_left hn _)) hn
      _ = _ := by ring
  refine ⟨L, SPACE.mono_const hb hL, ?_⟩
  intro x w htime hspace
  rw [hind]
  exact hp (x.map e) x rfl w htime hspace


/-- A linear-space decider for the quadratically padded language suffices for the separation
from `NP`. [AB09, Exercise 3.2]

**Proof sketch.** If linear space were `NP`, the padded language would belong to `NP`. Its
polynomial-time padding map pulls it back to the original quadratic-space language, by the
published closure of `NP` under polynomial-time preimages. This reverses the strict inclusion
given by the space hierarchy at the linear and quadratic bounds. -/
private lemma sph_linear_ne_NP_of_padding
    (hH : ∀ f g : ℕ → ℕ, SpaceConstructible f → SpaceConstructible g →
      (∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) → SPACE f ⊂ SPACE g)
    (hpad : ∀ L : Language Bool, L ∈ SPACE (fun n => n ^ 2 + 1) →
      ({y | ∃ x ∈ L,
        y = pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)} : Language Bool) ∈
        SPACE (fun n => n + 1)) :
    SPACE (fun n => n + 1) ≠ NP := by
  intro heq
  have hback : SPACE (fun n => n ^ 2 + 1) ⊆ SPACE (fun n => n + 1) := by
    intro L hL
    let p : List Bool → List Bool := fun x =>
      pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)
    let L' : Language Bool := {y | ∃ x ∈ L, y = p x}
    have hp : PolyTimeComputable p :=
      polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary 1 2)
    have hL' : L' ∈ NP := heq ▸ hpad L hL
    have hpull : p ⁻¹' L' = L := by
      apply Set.ext
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, hxy⟩ := (show ∃ y ∈ L, p x = p y from hx)
        have he : x = y := by
          simpa only [p, pairFstD_pairEncode] using congrArg pairFstD hxy
        exact he.symm ▸ hy
      · intro hx
        exact (show ∃ y ∈ L, p x = p y from ⟨x, hx, rfl⟩)
    have hpre := preimage_mem_NP hp hL'
    rw [hpull] at hpre
    exact heq.symm ▸ hpre
  have hstrict := hH (fun n => n + 1) (fun n => n ^ 2 + 1)
    spaceConstructible_linear (spaceConstructible_poly 2 (by norm_num))
    (fun A => ⟨A + 1, fun n hn => by
      nlinarith [Nat.mul_le_mul_right (n + 1) hn]⟩)
  exact hstrict.2 hback

/-- **The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through
[AB09]): for
space-constructible `f` and `g`, if every constant multiple of `f` is
eventually below `g` (that is, `f = o(g)`), then `SPACE f ⊊ SPACE g`.
Constant-factor hypothesis — no square and no logarithmic term, by a
universal simulation with constant-factor space overhead (the
self-application universal `U₀` of the sketch, the sibling of
`Complexity.space_universal`); both constructibility hypotheses are the
book's, and the proof uses `g`'s witness and floor but, of `f`'s, only the
bundled floor. Positivity of both bounds is automatic from the bundled
`logSpace` floor, so the zero-bound convention needs no side condition.

**Proof sketch.** *Inclusion.* `hfg` at `A = 1` gives `f n ≤ g n` from some
`N` on; below `N` each `f n` is at most `F := max_{n<N} f n` times
`g n ≥ 1` (`g`'s floor), so `f ≤ max F 1 · g` everywhere and
`Complexity.SPACE.mono_const` applies.

*The universal machine `U₀`.* One fixed machine for the scheme
`Complexity.TimeHierarchy.code`: on an input `x = pairEncode α w` it canonizes
`α` from the doubled prefix (the chapter-1 startup, `Turing.universalCanonTM`),
returns its input head to the origin, and simulates the coded machine on `x`
itself — self-application, so no `preTM` copy is needed — with its own input
head as the simulated one (the native device: the simulated input is all of
`U₀`'s input, so its left boundary is a real blank and no position is stored)
and the step block on the canonical table. Its forward ledger: for each
`α` a constant `C_α` such that whenever the coded machine halts on `x` with
some output, having visited at most `s` cells, `U₀` halts on `x` with the
same output, having visited at most `C_α · (s + 1)` cells
(`Turing.exists_selfUniversal`). This is `space_universal`'s forward clause
with the native device in place of the bounded-prefix ruler, so no header
ruler is needed; only this direction is used.

*The diagonalizer `D`.* On input `x` with `n = |x|`, over the record alphabet:
(i) validate the input (`Turing.inputFoldTM`), so that
`D`'s space is bounded on foreign rich inputs, as
`Turing.FinTM.alphabet_reduction_spaceUsed` requires, and compute
`bits (g n)` by `g`'s witness, captured on a work tape, in `O(g n)` cells;
(ii) form the radius `r = a · g n` for a fixed `a ≥ 1`
(`a = 1` suffices, the code-dependent constant being paid by the hypothesis
below; a power of two costs only low zero digits) and write `U₀`'s initial
record on `x` at radius `r`, tagged with the empty-output summary
(`Turing.exists_recordInitTM`); (iii) run the configuration-count windowed runner at `U₀`
(`Turing.exists_configWindowRunnerTM`): each round tests the record for a halted state, else
applies one step of `U₀` (leaving the window is an exit), the tag updated by the three-valued
output summary `Turing.outSummary` (`summaryTag`; append-compatible,
`Turing.outSummary_append_congr`; coded in `Fin 3`), so the emitted word is never buffered.
The runner carries its own configuration-count clock, whose value suffices for every round up
to `Turing.FinTM.configBound U₀ n r + 1`, in `O(record length)` cells.
(iv) Answer `false` if the runner stopped at a halted
record with summary `accept` (output exactly `[true]`,
`Turing.outSummary_eq_accept_iff`), and `true` on every other exit: halted
with another output, window exit, or clock exhaustion. `D` halts on every
input. Its cells are the witness's `O(g n)`, the record's
`k₀ · (2r + 1) + posWidth n + k₀ + 4` (`Turing.recordLength`), the record
runner's `O(record length)` scratch and clock: all `O(g n)` with
constants depending only on `U₀` and `g`'s witness, **uniformly in the code
part of `x`**, because the window, not `U₀`'s constant, bounds the
simulation; the `posWidth n = O(logSpace n)` terms are
absorbed by `g`'s floor. After the alphabet reduction, the language `L_D`
that `D` decides lies in `SPACE g`.

*`L_D ∉ SPACE f`.* Suppose `M` decides `L_D` within `c₀ · f n` cells. Then
`M` halts within `configBound M n (c₀ · f n)` steps
(`Turing.FinTM.ComputesInTime.of_spaceUsed_le`), and its space bound holds at
every time (`Turing.MultiTapeTM.spaceUsed_mono` up to the halt, the halted
configuration frozen after it). The space-faithful normal form
`Turing.FinTM.one_work_tape_binary_spaceUsed` gives a one-work-tape binary
`M'` within `c · (c₀ · f n + 1)` cells. Relabel it to a coded machine `N` within the same space
(`Turing.exists_codeTM_spaceUsed`) and set
`α_M := code.encode N`, so that `code.decode α_M = N`. Pad the **payload**,
never the code: on `x = pairEncode α_M w`, `U₀` outputs `N`'s verdict
`[x ∈ L_D]` within `C_{α_M} · (c · (c₀ · f n + 1) + 1) ≤ A · f n` cells,
where `A := C_{α_M} · (c · c₀ + c + 1)`, using `1 ≤ f n`. The hypothesis
`hfg` at this one `A` gives `N₀` with `A · f n ≤ g n ≤ r` for `n ≥ N₀`;
take `w := List.replicate N₀ true`. Then every configuration of `U₀`'s run
on `x` up to its halt is in the radius-`r` window, since each
tape's visited cells form an interval around `0` of size at most `r`
(`Turing.MultiTapeTM.abs_pos_lt_card_visited`) and every nonblank cell was
visited (`Turing.MultiTapeTM.mem_visited_of_ne_none`); and the halt comes by
step `configBound U₀ n r` (`ComputesInTime.of_spaceUsed_le` at the bound
`r`), before the clock runs out. So the runner stops at `U₀`'s halted record,
whose summary is `accept` exactly when `x ∈ L_D`, and `D` answers the
opposite: `x ∈ L_D ↔ x ∉ L_D`, a contradiction. The construction uses
`U₀` with its forward ledger (the step block at one coded work tape, the
native input device and the chapter-1 startup); the configuration-count
windowed runner `exists_configWindowRunnerTM` at `U₀` with the output-summary tag, after
the record initializer `exists_recordInitTM` and followed by the record test
`exists_recordTestTM`; the radius phase (`g`'s witness captured, radius digits);
the window-containment lemma from the visited-interval facts;
`exists_codeTM_spaceUsed` and the all-times space bound of a decider; the
contradiction arithmetic; `D`'s `DecidesInSpace` packaging through the
alphabet reduction. -/
theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) :
    SPACE f ⊂ SPACE g := by
  classical
  obtain ⟨U, hU⟩ := exists_selfUniversal TimeHierarchy.code
  obtain ⟨L, hLg, hdiag⟩ := sph_diagonal_language U g hg
  refine ⟨sph_inclusion hg hfg, ?_⟩
  intro hback
  obtain ⟨c, M, hM⟩ := mem_SPACE_iff.mp (hback hLg)
  obtain ⟨x, t, ht, hs, htime, _⟩ := sph_code_window f g hf hfg U hU L c M hM
  rw [htime] at ht hs
  have h := hdiag x [MultiTapeTM.indicator (L : Set (List Bool)) x] ht hs
  cases hb : MultiTapeTM.indicator (L : Set (List Bool)) x <;>
    simp only [hb, List.cons.injEq, and_true, Bool.false_eq_true, Bool.true_eq_false, decide_false,
      decide_true, Bool.not_false, Bool.not_true] at h

/-- **`L ⊊ PSPACE`** — the strict step of the p. 92 chain ([AB09, §4.3.2,
"the hierarchy theorems imply `L ⊊ PSPACE`"]).

**Proof sketch.** `Complexity.space_hierarchy` at `f := logSpace`,
`g := fun n => n + 1` (both constructible — the received
`Complexity.spaceConstructible_logSpace` and
`Complexity.spaceConstructible_linear`; domination:
`A · logSpace n ≤ n + 1` eventually, a logarithm-versus-identity
inequality), then `SPACE (n + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE` at degree one) and strictness
transports along the inclusion. -/
theorem LOGSPACE_ssubset_PSPACE : LOGSPACE ⊂ PSPACE := by
  exact sph_logspace_ssubset space_hierarchy

/-- **`SPACE(n + 1) ≠ NP`** ([AB09, Exercise 3.2], stated at the positive
normalization `n + 1` — the literal `SPACE(n)` is the zero-work-tape class).
Neither inclusion between the
two classes is claimed, matching the book's remark.

**Proof sketch.** Suppose `SPACE (n + 1) = NP`. Padding transfers space bounds down: for
`L ∈ SPACE (n² + 1)`, the padded language
`L' := {y | ∃ x ∈ L, y = pairEncode x (List.replicate ((|x| + 1)²) true)}` (padded members of
`L` only; padded length exactly `m = (n + 1)² + 2n + 2`) lies in `SPACE (m + 1)`: validate the
padding, then run the `L`-decider on the first component, the pad supplying the room. So
`L' ∈ NP` by the assumption. The padding map is polynomial-time computable and `L` is the
preimage of `L'` under it, so `L ∈ NP` (`Complexity.preimage_mem_NP`), that is
`L ∈ SPACE (n + 1)`. Hence `SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
`Complexity.space_hierarchy` at the constructible pair
(`Complexity.spaceConstructible_linear`,
`Complexity.spaceConstructible_poly` at degree two; domination
`A · (n + 1) ≤ n² + 1` eventually). The argument uses the padded-language space decider,
the padding map's polynomial-time computability, `preimage_mem_NP` and the strictness
extraction. -/
theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP := by
  apply sph_linear_ne_NP_of_padding space_hierarchy
  intro L hL
  have h := mem_SPACE_padLang (T := fun n => n + 1) 1 2 hL
    (fun n => by
      have : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ n) 2
      dsimp only
      omega) (fun m => le_rfl)
  have he : padLang L (fun n => 1 * (n + 1) ^ 2) =
      {y | ∃ x ∈ L, y = pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)} := by
    apply Set.ext
    intro y
    exact mem_padLang_iff
  rwa [he] at h

end Complexity
