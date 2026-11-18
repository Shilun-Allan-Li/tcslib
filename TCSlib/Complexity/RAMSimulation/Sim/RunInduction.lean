/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunPrefix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The shared RAM simulation induction

One fuel induction applies to arbitrary timed branch choices and to branches realizing a
prescribed source coin stream. Every instruction uses the published phase host and restores
the work heads before the next instruction. The resulting certificate contains exact source
touches, consumed coins and uniform time and head bounds.

## Main definitions

No additional machine or execution relation is introduced.

## Main results

* `WordRAM.Sim.RunSetup.run_execution`: a driven execution certificate for every fuel bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2; Definition 4.1.)
-/

namespace WordRAM.Sim.RunSetup

open Turing

/-- Every encoded instruction entry admits a driven simulation prefix. It either completes a
verdict before the fuel bound or reaches exactly that many ordinary source steps. Its source
trace works for every stream agreeing with the coins consumed by this prefix.
[AB09, Exercise 1.9], with explicit resource and read-once coin invariants.

**Proof sketch.** Induct on fuel. At zero, use the empty live certificate. At positive fuel,
`instruction_run` executes the next instruction using the driver's entry bit. A verdict gives
`RunExecution.of_verdict`. Otherwise update the consumed prefix with `runNextCoins`, use
`source_step_rd` to identify the successor coin index, and apply the induction hypothesis at
the restored encoded successor. `RunExecution.prepend` concatenates the actual branch and
source trace while keeping one common head envelope. -/
theorem run_execution {P : XProgram} {fn : Bool} {Mw : FinTM Bool}
    (A : RunSetup P fn Mw) {W : ℕ} {x : List Bool} (D : RunDriver W)
    (B : ℕ → Bool → Prop) (hD : D.Respects B) (s fuel : ℕ) (T : Finset ℤ)
    (c : XCfg W) (o : Fin 8 → ℤ)
    (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x) (coins : List Bool) (par : Bool)
    (hrd : c.rd = coins.length) (hc : RunCoinsSatisfy B coins)
    (hd : d.state = some ⟨some (runPosition P c.pc, par),
      (A.phases (runPosition P c.pc)).entry⟩)
    (he : Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o d) :
    Nonempty (RunExecution A D B s fuel T c o d coins) := by
  induction fuel generalizing s T c d coins par with
  | zero => exact RunExecution.zero A D B s T c o d coins par hrd hc hd he
  | succ fuel ih =>
    let b := D.coin s c
    have hcoin : isCoin (P.getD c.pc (.base .reject)) = true →
        (coins ++ [b]).getD c.rd false = D.coin s c := by
      intro _
      rw [hrd]
      exact runCoinsAgree_append_bit coins (coins ++ [b]) b (runCoinsAgree_refl _)
    obtain ⟨w, e, ht, hr, henv, hfollows, hresult⟩ :=
      A.instruction_run (ρ := coins ++ [b]) D s par T c o d hd he hcoin
    cases hs : xstep P x (coins ++ [b]) c with
    | inl c' =>
      rw [hs] at hresult
      obtain ⟨he', hd', hh⟩ := hresult
      have hrd' : c'.rd = (runNextCoins (P.getD c.pc (.base .reject)) coins b).length := by
        rw [source_step_rd hs, hrd, runNextCoins_length]
      have hc' : RunCoinsSatisfy B (runNextCoins (P.getD c.pc (.base .reject)) coins b) :=
        runNextCoins_satisfy B _ coins b hc
          (by rw [← hrd]; exact (RunDriver.respects_iff D B).mp hD s c)
      obtain ⟨R⟩ := ih (s + w.length) (T ∪ (P.getD c.pc (.base .reject)).touches c.mem)
        c' e (runNextCoins (P.getD c.pc (.base .reject)) coins b) (!par) hrd' hc' hd' he'
      exact RunExecution.prepend A D B s fuel T c c' o d e coins w b hrd hs hr hh ht
        henv hfollows R
    | inr v =>
      rw [hs] at hresult
      exact RunExecution.of_verdict A D B s fuel T c o d e coins w v hrd hc hs hr
        hresult.1 hresult.2 ht henv hfollows

end WordRAM.Sim.RunSetup
