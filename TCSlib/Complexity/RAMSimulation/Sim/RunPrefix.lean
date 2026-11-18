/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunInstruction
import TCSlib.Complexity.RAMSimulation.Sim.RunSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Certificates for prefixes of the shared simulation run

An execution certificate records an actual branch word, its exact source footprint, the
consumed coins, and one common time/head-envelope bound. Its source trace is valid for every
stream agreeing with those consumed coins; future bits need not be chosen in advance.

## Main definitions

* `WordRAM.Sim.RunExecution`: the invariant carried by the shared fuel induction.

## Main results

The endpoint is either a completed verdict or a live cutoff at the specified number of
ordinary source steps. Both kinds carry the same branch and resource certificate.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2; Definition 4.1.)
-/

namespace WordRAM.Sim

open Turing

/-- A driven execution prefix. Its table cells are the initial set `T` together with exactly
the source trace's touched cells. Completed executions halt before the fuel cutoff; live
executions restore every head and remain at an encoded instruction entry. -/
structure RunExecution {P : XProgram} {fn : Bool} {Mw : FinTM Bool}
    (A : RunSetup P fn Mw) {W : ℕ} {x : List Bool} (D : RunDriver W)
    (B : ℕ → Bool → Prop) (s fuel : ℕ) (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
    (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x) (coins : List Bool) where
  word : List Bool
  finish : Turing.Cfg (8 + A.extraTapes) Bool A.State x
  steps : ℕ
  last : XCfg W
  cells : Finset ℤ
  outCoins : List Bool
  coins_extend : ∃ extra, outCoins = coins ++ extra
  coin_index : last.rd = outCoins.length
  coins_ok : RunCoinsSatisfy B outCoins
  source : ∀ ρ, RunCoinsAgree outCoins ρ → RunSourceTrace P x ρ steps c last cells
  run : A.host.runWith word d = finish
  time_bound : word.length ≤ (steps + 1) * A.blockTime x.length W (T ∪ cells).card
  envelope : ∀ u ≤ word.length, ∀ j,
    |(A.host.runWith (word.take u) d).workTapePos j - d.workTapePos j| ≤
      (A.blockRadius x.length W (T ∪ cells).card : ℕ)
  follows : ∀ χ, D.Follows χ → word = runChoices χ s word.length
  ending :
    (∃ v, xstep P x outCoins last = .inr v ∧ finish.state = none ∧
      finish.output = (if fn then last.out else [v]) ∧ steps < fuel) ∨
    (steps = fuel ∧ ∃ par : Bool,
      finish.state = some ⟨some (runPosition P last.pc, par),
        (A.phases (runPosition P last.pc)).entry⟩ ∧
      Encodes A.width fn (T ∪ cells) last (Fin.castAddEmb A.extraTapes) o finish ∧
      finish.workTapePos = d.workTapePos)

/-- With zero fuel, the empty branch is a live cutoff at the original encoded entry.
It touches no source cells, consumes no coins and leaves every head fixed.

**Proof sketch.** Use the empty source trace and branch. The original entry and encoding give
the live cutoff; empty touched cells leave its table unchanged. Its sole prefix has zero
head displacement, and its time is zero. -/
theorem RunExecution.zero {P : XProgram} {fn : Bool} {Mw : FinTM Bool}
    (A : RunSetup P fn Mw) {W : ℕ} {x : List Bool} (D : RunDriver W)
    (B : ℕ → Bool → Prop) (s : ℕ) (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
    (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x) (coins : List Bool) (par : Bool)
    (hrd : c.rd = coins.length) (hc : RunCoinsSatisfy B coins)
    (hd : d.state = some ⟨some (runPosition P c.pc, par),
      (A.phases (runPosition P c.pc)).entry⟩)
    (he : Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o d) :
    Nonempty (RunExecution A D B s 0 T c o d coins) := by
  refine ⟨{
    word := []
    finish := d
    steps := 0
    last := c
    cells := ∅
    outCoins := coins
    coins_extend := ⟨[], (List.append_nil coins).symm⟩
    coin_index := hrd
    coins_ok := hc
    source := fun _ _ => RunSourceTrace.nil c
    run := NDTM.runWith_nil
    time_bound := Nat.zero_le _
    envelope := ?_
    follows := ?_
    ending := Or.inr ⟨rfl, par, hd, ?_, rfl⟩ }⟩
  · intro u hu j
    rw [List.length_nil] at hu
    have hz : u = 0 := Nat.eq_zero_of_le_zero hu
    subst u
    rw [List.take_zero, NDTM.runWith_nil, sub_self, abs_zero]
    exact Nat.cast_nonneg _
  · intro χ hD
    rw [List.length_nil, runChoices_zero]
  · simpa only [Finset.union_empty] using he

/-- A driven verdict step is a completed execution certificate for any positive fuel.
It adds no ordinary source step, touched cell or consumed coin.

**Proof sketch.** Keep the given branch endpoint and envelope, and use the empty exact source
trace. `source_verdict_stream` makes the verdict valid for the unchanged consumed prefix.
The block bound is already the certificate's one-phase time bound; the source cell union is
unchanged because its newly touched set is empty. -/
theorem RunExecution.of_verdict {P : XProgram} {fn : Bool} {Mw : FinTM Bool}
    (A : RunSetup P fn Mw) {W : ℕ} {x ρ : List Bool} (D : RunDriver W)
    (B : ℕ → Bool → Prop) (s fuel : ℕ) (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
    (d e : Turing.Cfg (8 + A.extraTapes) Bool A.State x) (coins w : List Bool) (v : Bool)
    (hrd : c.rd = coins.length) (hc : RunCoinsSatisfy B coins)
    (hs : xstep P x ρ c = .inr v) (hr : A.host.runWith w d = e)
    (he : e.state = none) (ho : e.output = (if fn then c.out else [v]))
    (ht : w.length ≤ A.blockTime x.length W T.card)
    (henv : ∀ u ≤ w.length, ∀ j,
      |(A.host.runWith (w.take u) d).workTapePos j - d.workTapePos j| ≤
        (A.blockRadius x.length W T.card : ℕ))
    (hfollows : ∀ χ, D.Follows χ → w = runChoices χ s w.length) :
    Nonempty (RunExecution A D B s (fuel + 1) T c o d coins) := by
  refine ⟨{
    word := w
    finish := e
    steps := 0
    last := c
    cells := ∅
    outCoins := coins
    coins_extend := ⟨[], (List.append_nil coins).symm⟩
    coin_index := hrd
    coins_ok := hc
    source := fun _ _ => RunSourceTrace.nil c
    run := hr
    time_bound := ?_
    envelope := ?_
    follows := hfollows
    ending := Or.inl ⟨v, source_verdict_stream hs coins, he, ho, Nat.succ_pos fuel⟩ }⟩
  · simpa only [Finset.union_empty, zero_add, one_mul] using ht
  · simpa only [Finset.union_empty] using henv

/-- Prepending an ordinary instruction to a driven tail preserves the execution certificate.
The touched sets are unioned, coin prefixes extend, and the common head radius is taken over
the final table rather than added over instructions.

**Proof sketch.** Any stream agreeing with the tail's final coins agrees with the current
instruction's consumed bit, so `source_step_coin_congr` supplies the first source step.
Concatenate the branch words by `NDTM.runWith_append`. Monotonicity in table size bounds the
first block by the final block cost; the tail already has that bound. Restored heads let
`runEnvelope_append` keep the maximum radius. The tail's verdict or live cutoff gives the
corresponding endpoint, with one additional ordinary source step. -/
theorem RunExecution.prepend {P : XProgram} {fn : Bool} {Mw : FinTM Bool}
    (A : RunSetup P fn Mw) {W : ℕ} {x : List Bool} (D : RunDriver W)
    (B : ℕ → Bool → Prop) (s fuel : ℕ) (T : Finset ℤ) (c c' : XCfg W)
    (o : Fin 8 → ℤ) (d e : Turing.Cfg (8 + A.extraTapes) Bool A.State x)
    (coins w : List Bool) (b : Bool) (hrd : c.rd = coins.length)
    (hs : xstep P x (coins ++ [b]) c = .inl c')
    (hr : A.host.runWith w d = e) (hh : e.workTapePos = d.workTapePos)
    (ht : w.length ≤ A.blockTime x.length W T.card)
    (henv : ∀ u ≤ w.length, ∀ j,
      |(A.host.runWith (w.take u) d).workTapePos j - d.workTapePos j| ≤
        (A.blockRadius x.length W T.card : ℕ))
    (hfollows : ∀ χ, D.Follows χ → w = runChoices χ s w.length)
    (R : RunExecution A D B (s + w.length) fuel
      (T ∪ (P.getD c.pc (.base .reject)).touches c.mem) c' o e
      (runNextCoins (P.getD c.pc (.base .reject)) coins b)) :
    Nonempty (RunExecution A D B s (fuel + 1) T c o d coins) := by
  let K := (P.getD c.pc (.base .reject)).touches c.mem
  have hcard : T.card ≤ (T ∪ (K ∪ R.cells)).card :=
    Finset.card_le_card Finset.subset_union_left
  refine ⟨{
    word := w ++ R.word
    finish := R.finish
    steps := R.steps + 1
    last := R.last
    cells := K ∪ R.cells
    outCoins := R.outCoins
    coins_extend := ?_
    coin_index := R.coin_index
    coins_ok := R.coins_ok
    source := ?_
    run := ?_
    time_bound := ?_
    envelope := ?_
    follows := ?_
    ending := ?_ }⟩
  · obtain ⟨pre, hp⟩ := runNextCoins_prefix (P.getD c.pc (.base .reject)) coins b
    obtain ⟨extra, he⟩ := R.coins_extend
    exact ⟨pre ++ extra, he.trans ((congrArg (fun z => z ++ extra) hp).trans
      (List.append_assoc coins pre extra))⟩
  · intro ρ hρ
    obtain ⟨extra, he⟩ := R.coins_extend
    have hn : RunCoinsAgree (runNextCoins (P.getD c.pc (.base .reject)) coins b) ρ :=
      runCoinsAgree_append_left _ extra ρ (by rw [← he]; exact hρ)
    have hfirst : xstep P x ρ c = .inl c' := by
      apply (source_step_coin_congr P x ρ (coins ++ [b]) c ?_).trans hs
      intro hcoin
      rw [hrd, runNextCoins_read _ _ _ _ hn hcoin,
        runCoinsAgree_append_bit coins (coins ++ [b]) b (runCoinsAgree_refl _)]
    exact RunSourceTrace.cons hfirst (R.source ρ hρ)
  · rw [NDTM.runWith_append, hr, R.run]
  · rw [List.length_append]
    have htail : R.word.length ≤
        (R.steps + 1) * A.blockTime x.length W (T ∪ (K ∪ R.cells)).card := by
      simpa only [Finset.union_assoc] using R.time_bound
    have hfirst := ht.trans (A.blockTime_mono x.length W hcard)
    calc
      w.length + R.word.length ≤ A.blockTime x.length W (T ∪ (K ∪ R.cells)).card +
          (R.steps + 1) * A.blockTime x.length W (T ∪ (K ∪ R.cells)).card :=
        Nat.add_le_add hfirst htail
      _ = (R.steps + 1 + 1) * A.blockTime x.length W (T ∪ (K ∪ R.cells)).card := by
        rw [Nat.add_mul (R.steps + 1) 1, one_mul, Nat.add_comm]
  · apply runEnvelope_append A.host w R.word d e _ hr hh
    · intro u hu j
      exact (henv u hu j).trans (by exact_mod_cast (A.blockRadius_mono x.length W hcard))
    · simpa only [Finset.union_assoc] using R.envelope
  · intro χ hD
    calc
      w ++ R.word = runChoices χ s w.length ++
          runChoices χ (s + w.length) R.word.length :=
        congrArg₂ List.append (hfollows χ hD) (R.follows χ hD)
      _ = runChoices χ s (w.length + R.word.length) :=
        (runChoices_append χ s w.length R.word.length).symm
      _ = runChoices χ s (w ++ R.word).length := by rw [List.length_append]
  · rcases R.ending with ⟨v, hv, hd, ho, hf⟩ | ⟨hf, par, hd, he, hheads⟩
    · exact Or.inl ⟨v, hv, hd, ho, Nat.succ_lt_succ hf⟩
    · refine Or.inr ⟨congrArg (fun n => n + 1) hf, par, hd, ?_, hheads.trans hh⟩
      simpa only [Finset.union_assoc] using he

/-- A halting RAM run rules out the execution certificate's live cutoff and bounds its exact
footprint. Its completed output is the output of that RAM run.

**Proof sketch.** `RunSourceTrace.bounded_by_halt` compares the certificate with the halting
witness, giving a strict bound below the fuel and inclusion in the witness's footprint. This
contradicts a live cutoff. For the remaining verdict, form a `HaltsWithin` witness from the
exact source trace and use the published `HaltsWithin.unique` to identify verdict and output. -/
theorem RunExecution.completed {P : XProgram} {fn : Bool} {Mw : FinTM Bool}
    {A : RunSetup P fn Mw} {W : ℕ} {x ρ : List Bool} {D : RunDriver W}
    {B : ℕ → Bool → Prop} {s t : ℕ} {T : Finset ℤ} {o : Fin 8 → ℤ}
    {d : Turing.Cfg (8 + A.extraTapes) Bool A.State x} {coins : List Bool}
    (R : RunExecution A D B s t T (XCfg.init W x.length) o d coins)
    {v : Bool} {out : List Bool} {f : ℕ}
    (h : HaltsWithin P x ρ W t v out f) (ha : RunCoinsAgree R.outCoins ρ) :
    R.steps < t ∧ R.cells.card ≤ f ∧ R.finish.state = none ∧
      R.finish.output = (if fn then out else [v]) := by
  obtain ⟨n, c₂, K, hn, hK, hr, hv, ho⟩ := (haltsWithin_iff P x ρ t v out f).mp h
  have htrace := R.source ρ ha
  obtain ⟨hsteps, hcells⟩ := htrace.bounded_by_halt hr hv
  have hlt : R.steps < t := hsteps.trans_lt hn
  have hcard : R.cells.card ≤ f := (Finset.card_le_card hcells).trans hK
  rcases R.ending with ⟨v', hv', hd, hout, _⟩ | ⟨hcut, _⟩
  · have hmade : HaltsWithin P x ρ W t v' R.last.out f :=
      (haltsWithin_iff P x ρ t v' R.last.out f).mpr
        ⟨R.steps, R.last, K, hlt, hK, htrace.to_stepsIn (↑K) hcells,
          source_verdict_stream hv' ρ, rfl⟩
    obtain ⟨heqv, heqo⟩ := h.unique hmade
    exact ⟨hlt, hcard, hd, by rw [← heqv, ← heqo] at hout; exact hout⟩
  · omega

end WordRAM.Sim
