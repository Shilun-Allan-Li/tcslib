/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.RepeatedVerifier
import TCSlib.Cryptography.Composability.SequentialZK.ErrSoundness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Explicit soundness error under abstract sequential repetition

## Main definitions

Private tape and phase-test functions express conditioning on earlier verifier blocks.

## Main results

* `Composability.PaddedVerifierSpec.outV_eq`: the repeated output is its terminal verdict.
* `Composability.PaddedVerifierSpec.accept_le`: aggregate acceptance is at most `s(|x|)^q`.
* `Composability.PaddedVerifierSpec.sound`: aggregate rejection is at least `1-s(|x|)^q`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition).
-/

namespace TCSlib.Cryptography.Composability

/-- `phaseTape q c F` is the string of the `q` consecutive `c`-bit blocks of `F`. -/
private def phaseTape (q c : ℕ) (F : Fin q → Fin c → Bool) : List Bool :=
  List.ofFn ((FunFamily.blocks q c).symm F)

/-- Block `i` of `phaseTape q c F` is `List.ofFn (F i)`. -/
private theorem phaseTape_block (q c : ℕ) (F : Fin q → Fin c → Bool) (i : Fin q) :
    coinBlock c i (phaseTape q c F) = List.ofFn (F i) := by
  have he := FunFamily.ofFn_blocks q c ((FunFamily.blocks q c).symm F) i
  rw [Equiv.apply_symm_apply] at he
  exact (coinBlock_eq c i (phaseTape q c F)).trans he.symm

/-- `zeroTail q c i pre` has block `pre j` below `i` and the all-false block afterwards. -/
private def zeroTail (q c i : ℕ) (pre : Fin i → Fin c → Bool) : Fin q → Fin c → Bool :=
  fun j => if h : (j : ℕ) < i then pre ⟨j, h⟩ else fun _ => false

/-- `phaseGood π ρ P x z rP q i pre fresh` is acceptance of `π.V` on `fresh` against the
prover whose tape is `rP` and whose earlier received messages come from `ρ` on the tape
formed from `pre` and an all-false suffix. -/
private def phaseGood (π ρ : Protocol) (P : Strategy) (x z rP : List Bool) (q i : ℕ)
    (pre : Fin i → π.V.Coins x.length) (fresh : π.V.Coins x.length) : Prop :=
  π.V.next x z (List.ofFn fresh)
    (exec (prefixProver P [] rP
      (exec P ρ.V π.verifierFirst x [] z rP
        (phaseTape q (π.V.coinLen x.length) (zeroTail q (π.V.coinLen x.length) i pre))
        (2 * π.rounds.eval x.length * i)).1)
      π.V π.verifierFirst x [] z [] (List.ofFn fresh) (π.rounds.eval x.length)).2 = [true]

/-- Each fixed-prefix phase test has acceptance at most the original soundness error. -/
private theorem phaseGood_section {π ρ : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (h : InteractiveProofErr π L s) (x : List Bool) (hx : x ∉ L) (P : Strategy)
    (z rP : List Bool) (q i : ℕ) (pre : Fin i → π.V.Coins x.length) :
    uprob (phaseGood π ρ P x z rP q i pre) ≤ s x.length :=
  prefixProver_accept_le h x hx P [] rP
    (exec P ρ.V π.verifierFirst x [] z rP
      (phaseTape q (π.V.coinLen x.length) (zeroTail q (π.V.coinLen x.length) i pre))
      (2 * π.rounds.eval x.length * i)).1 z

/-- An accepting aggregate phase test is the corresponding conditional `phaseGood` test.

**Proof sketch.** Replace every block at and after the phase by zeros. The verifier-prefix
reader shows this leaves the earlier transcript fixed. The phase-history reader then
identifies the aggregate test with the original verifier against the induced fixed-prefix
prover. Reading the actual phase block supplies the fresh local verifier tape. -/
private theorem phaseGood_of_test {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
    (d : PaddedVerifierSpec π ρ x q p terminal) (P : Strategy) (z rP : List Bool)
    (F : Fin q → π.V.Coins x.length) (i : Fin q)
    (htest : π.V.next x z
      (coinBlock (π.V.coinLen x.length) i (phaseTape q (π.V.coinLen x.length) F))
      (((exec P ρ.V π.verifierFirst x [] z rP (phaseTape q (π.V.coinLen x.length) F)
        (2 * π.rounds.eval x.length * q)).2.drop (i * π.rounds.eval x.length)).take p) =
        [true]) :
    phaseGood π ρ P x z rP q i (fun j => F (Fin.castLE i.isLt.le j)) (F i) := by
  let c := π.V.coinLen x.length
  let k := π.rounds.eval x.length
  let pre : Fin i → π.V.Coins x.length := fun j => F (Fin.castLE i.isLt.le j)
  let F0 : Fin q → π.V.Coins x.length := zeroTail q c i pre
  have hblocks : ∀ l < (i : ℕ), coinBlock c l (phaseTape q c F) =
      coinBlock c l (phaseTape q c F0) := by
    intro l hl
    have hlq : l < q := lt_trans hl i.isLt
    rw [phaseTape_block q c F ⟨l, hlq⟩, phaseTape_block q c F0 ⟨l, hlq⟩]
    apply congrArg List.ofFn
    funext b
    change F ⟨l, hlq⟩ b =
      (if h : l < (i : ℕ) then pre ⟨l, h⟩ else fun _ => false) b
    rw [dif_pos hl]
    rfl
  -- Earlier received histories ignore every block at or beyond the current phase.
  have he := exec_eq_of_verifier_blocks P ρ.V π.V π.verifierFirst x [] z rP
    (phaseTape q c F) (phaseTape q c F0) k q c i (terminal z)
    (d.next_eq z) i.isLt
    (fun t _ hm => d.index_eq P [] z rP (phaseTape q c F) t hm) hblocks
  have hprior := congrArg Prod.fst he
  -- Read the real phase and its fresh block from the original full table.
  rw [d.phase_take P [] z rP (phaseTape q c F) i i.isLt] at htest
  change π.V.next x z (coinBlock c i (phaseTape q c F))
    (exec (prefixProver P [] rP
      (exec P ρ.V π.verifierFirst x [] z rP (phaseTape q c F) (2 * k * i)).1)
      π.V π.verifierFirst x [] z [] (coinBlock c i (phaseTape q c F)) k).2 = [true] at htest
  simp only [phaseTape_block q c F i] at htest
  change π.V.next x z (List.ofFn (F i))
    (exec (prefixProver P [] rP
      (exec P ρ.V π.verifierFirst x [] z rP (phaseTape q c F0) (2 * k * i)).1)
      π.V π.verifierFirst x [] z [] (List.ofFn (F i)) k).2 = [true]
  rw [← hprior]
  exact htest

/-- For specification `d`, prover `P`, auxiliary inputs `y`, `z`, and joint coins `r`,
`ρ.outV P x y z r` equals `terminal z (List.ofFn r.2) hist`, where `hist` is the verifier
component of `exec P ρ.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (2*k*q)`
and `k=π.rounds.eval |x|`. [PS10, Theorem 175.1, the aggregate verdict]. -/
theorem PaddedVerifierSpec.outV_eq {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
    (d : PaddedVerifierSpec π ρ x q p terminal) (P : Strategy) (y z : List Bool)
    (r : ρ.ExecCoins P x) :
    ρ.outV P x y z r = terminal z (List.ofFn r.2)
      (exec P ρ.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
        (2 * π.rounds.eval x.length * q)).2 := by
  rw [Protocol.outV_eq, Protocol.transcriptWith_eq, d.rounds_eq, d.first_eq]
  rw [d.next_eq, if_pos (d.boundary_lengths P y z (List.ofFn r.1)
    (List.ofFn r.2) q le_rfl).2]

/-- For specification `d : PaddedVerifierSpec π ρ x q p terminal`, original soundness
`h : InteractiveProofErr π L s`, a no-instance `x ∉ L`, prover `P`, and verifier auxiliary
input `z`, `Pr[ρ.outV P x [] z = [true]] ≤ s |x| ^ q`.
[PS10, Theorem 175.1, multiplication of sequential soundness error].

**Proof sketch.** Zero phases give the bound one. Otherwise fix prover coins maximizing
acceptance and read the verifier tape as independent original coin blocks. Define the
phase test by fixing the earlier coin blocks and replacing future blocks by zeros. Earlier
transcripts are unaffected by that replacement, so every aggregate phase test is this
conditional test on the current fresh block. Each section accepts with probability at
most the original error. The adaptive product theorem bounds all phase tests by its
`q`-th power; averaging over the fixed prover coins only decreases acceptance. -/
theorem PaddedVerifierSpec.accept_le {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
    (d : PaddedVerifierSpec π ρ x q p terminal) {L : Language Bool} {s : ℕ → ℝ}
    (h : InteractiveProofErr π L s) (hx : x ∉ L) (P : Strategy) (z : List Bool) :
    uprob (fun r : ρ.ExecCoins P x => ρ.outV P x [] z r = [true]) ≤ s x.length ^ q := by
  by_cases hq : q = 0
  · subst q
    simpa only [pow_zero] using
      (uprob_le_one (fun r : ρ.ExecCoins P x => ρ.outV P x [] z r = [true]))
  · -- Fix a prover tape at least as successful as its uniform average.
    obtain ⟨rP, hrP⟩ := ρ.exists_proverCoins_le P x [] z (fun out => out = [true])
    refine hrP.trans ?_
    let c := π.V.coinLen x.length
    let e : (Fin q → π.V.Coins x.length) ≃ ρ.V.Coins x.length :=
      (FunFamily.blocks q c).symm.trans
        (Equiv.arrowCongr (finCongr d.coinLen_eq.symm) (Equiv.refl Bool))
    have htape (F : Fin q → π.V.Coins x.length) :
        List.ofFn (e F) = phaseTape q c F :=
      ofFn_arrowCongr_finCongr d.coinLen_eq.symm ((FunFamily.blocks q c).symm F)
    -- On every full table, aggregate acceptance implies all fixed-prefix phase tests.
    have hmono :
        uprob (fun F : Fin q → π.V.Coins x.length =>
          ρ.outV P x [] z (rP, e F) = [true]) ≤
        uprob (fun F : Fin q → π.V.Coins x.length => ∀ i : Fin q,
          phaseGood π ρ P x z (List.ofFn rP) q i
            (fun j => F (Fin.castLE i.isLt.le j)) (F i)) := by
      apply uprob_mono
      intro F hacc i
      rw [d.outV_eq, htape F, d.terminal_eq] at hacc
      split_ifs at hacc with hall
      · have hitest := List.all_eq_true.mp hall i (List.mem_range.mpr i.isLt)
        exact phaseGood_of_test d P z (List.ofFn rP) F i (of_decide_eq_true hitest)
      · cases hacc
    -- Apply the section bound on every earlier prefix, then the adaptive product bound.
    have hadapt :
        uprob (fun F : Fin q → π.V.Coins x.length => ∀ i : Fin q,
          phaseGood π ρ P x z (List.ofFn rP) q i
            (fun j => F (Fin.castLE i.isLt.le j)) (F i)) ≤ s x.length ^ q :=
      uprob_adaptive_all_le q (s x.length) (h.sound_nonneg x hx)
        (fun i => phaseGood π ρ P x z (List.ofFn rP) q i)
        (fun i _ pre => phaseGood_section h x hx P z (List.ofFn rP) q i pre)
    have htable := hmono.trans hadapt
    rw [uprob_comp_equiv e (fun rV => ρ.outV P x [] z (rP, rV) = [true])] at htable
    exact htable

/-- For specification `d : PaddedVerifierSpec π ρ x q p terminal`, original soundness
`h : InteractiveProofErr π L s`, a no-instance `x ∉ L`, prover `P`, and verifier auxiliary
input `z`, `1-s |x| ^ q ≤ Pr[ρ.outV P x [] z = [false]]`.
[PS10, Theorem 175.1, sequential soundness error `s^q`].

**Proof sketch.** Zero phases require only nonnegativity of a probability. Otherwise the
aggregate verdict is binary, so rejection is exactly the complement of acceptance.
Subtract the acceptance upper bound from one. -/
theorem PaddedVerifierSpec.sound {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
    (d : PaddedVerifierSpec π ρ x q p terminal) {L : Language Bool} {s : ℕ → ℝ}
    (h : InteractiveProofErr π L s) (hx : x ∉ L) (P : Strategy) (z : List Bool) :
    1 - s x.length ^ q ≤
      uprob (fun r : ρ.ExecCoins P x => ρ.outV P x [] z r = [false]) := by
  by_cases hq : q = 0
  · subst q
    simpa only [pow_zero, sub_self] using
      (uprob_nonneg (fun r : ρ.ExecCoins P x => ρ.outV P x [] z r = [false]))
  · have hiff (r : ρ.ExecCoins P x) :
        ρ.outV P x [] z r = [false] ↔ ¬ ρ.outV P x [] z r = [true] := by
      rw [d.outV_eq, d.terminal_eq]
      split_ifs <;> decide
    rw [OneWay.uprob_congr hiff, uprob_not]
    exact sub_le_sub_left (d.accept_le h hx P z) 1

end TCSlib.Cryptography.Composability
