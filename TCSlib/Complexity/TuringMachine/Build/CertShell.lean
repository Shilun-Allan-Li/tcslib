/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
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
# Machine-construction library: the certificate shell (W2-V)

The plain verifier side of certificate enumeration ([AB09, Claim 2.4 and Theorem 2.6]): a
plain machine run on an input with a certificate preloaded on a work tape becomes a decider
of the concatenated language, and projecting along certificates of the prescribed length
recovers the outcome condition. Its customers are the `NP^EXPCOM ⊆ EXP` summit (with
`TCSlib.Complexity.TuringMachine.Build.OracleSim`) and, in the 12.2c window, the chapter-2
shell it generalizes (the private `cont_choiceVerifier_mem_P` of
`TCSlib.Complexity.ClassNP.Nondeterminism`).

**Status: statement layer** (the shell is sorried with a proof sketch, and its fill follows
the §12.8 fill; the projection identity is proved).

## Main results

* `Turing.FinTM.exists_certificateShell` — the shell (sorried).
* `Turing.FinTM.certificateShell_proj` — its projection identity (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Claim 2.4, Theorem 2.6.)
-/

namespace Turing

/-- **The certificate shell** (row W2-V; [AB09, Claim 2.4 and Theorem 2.6], the verifier
side of the enumeration): let the plain machine `P`, started from `Cfg.ofWords` over the
input `x` with the certificate `u` on its tape `j` and every other tape empty, halt by
`T (|x| + |u|)` with output `out x u` whenever `|u| = C·(|x| + 1)^c`. Then some plain machine
decides the language of the strings `x ++ u` with `|u| = C·(|x| + 1)^c` and
`out x u = [true]` within `b·((m + 1)^e + T m)`. With `Complexity.exists_proj_decider`
this decides `{x | ∃ u, |u| = C·(|x| + 1)^c ∧ out x u = [true]}`
(`Turing.FinTM.certificateShell_proj`).

**Proof sketch.** Install the split `pairEncode x u` of the input `y` (the empty word on
failure, which rejects) on a work tape by the native-input clean call
`Turing.FinTM.exists_inputCallTM` (R8.5e, a §12.8 statement: this fill is sequenced after
the §12.8 fill) at `Turing.FinTM.computesFunInTime_splitSolve C c`; duplicate it
(`Turing.copyTM_run_ofCfg`), install `x` and `u` by the install-mode clean calls of
`Turing.FinTM.computesFunInTime_pairFst` and `computesFunInTime_pairSnd`, and move them to
the Z1 buffer and to bank tape `j` (`Turing.transferTM_run_ofCfg`); run `P` under Z1 from
`Turing.vhostCfg (Cfg.ofWords P.q₀ (Function.update (fun _ => []) j u)) true 1 []` (the
tag `true` is valid at position `1` for every `x`), inside the **returning** R1 capture
`Turing.embedSilentRetTM` over `Turing.vhostEmitTM P` (locksteps
`Turing.vhostEmitTM_runFrom` and `Turing.embedSilentRetTM_run`; the closed
`Turing.vhostSilentTM` would die with `P`), which lands in its return anchor at `P`'s first
halt with `P`'s output on the capture tape; a three-state scan of the capture (first cell
`true`, second blank) gives the verdict, which is emitted. Phases by R2 seams; time
`c·(m + 1)^(c + 2) + O(m) + T m + O(T m + 1)`. Template: the private 2B shell of
`TCSlib.Complexity.ClassNP.Nondeterminism` (`cont_choiceVerifier_mem_P`, the paired-input
loader and `choiceCore`), harvested with the core made a parameter. -/
theorem FinTM.exists_certificateShell (P : FinTM Bool) (j : Fin P.k) (C c : ℕ)
    (out : List Bool → List Bool → List Bool) (T : ℕ → ℕ)
    (hP : ∀ x u : List Bool, u.length = C * (x.length + 1) ^ c →
      (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (Function.update (fun _ => []) j u))
          (T (x.length + u.length))).state = none ∧
        (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (Function.update (fun _ => []) j u))
          (T (x.length + u.length))).output = out x u) :
    ∃ (V : FinTM Bool) (b e : ℕ),
      V.DecidesInTime {y | ∃ x u, y = x ++ u ∧ u.length = C * (x.length + 1) ^ c ∧
          out x u = [true]}
        fun m => b * ((m + 1) ^ e + T m) := by
  sorry

/-- **The shell's projection identity**: projecting the shell's language along
certificates of the prescribed length recovers the outcome condition, the split of
`x ++ u` being unique because `n ↦ n + C·(n + 1)^c` is strictly increasing.

**Proof sketch.** Equal concatenations with prescribed certificate lengths have equal
parts: the shared split `Turing.append_split_unique` at
`Turing.certificateLength_strictMono`, the same lemma the plain Theorem 2.6 uses (wave-1
statement gate, round 1, finding 2). -/
theorem FinTM.certificateShell_proj (C c : ℕ) (out : List Bool → List Bool → List Bool) :
    {x : List Bool | ∃ u, u.length = C * (x.length + 1) ^ c ∧
        x ++ u ∈ {y : List Bool | ∃ x u, y = x ++ u ∧ u.length = C * (x.length + 1) ^ c ∧
          out x u = [true]}} =
      {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ out x u = [true]} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, x', u', he, hu', ho⟩
    obtain ⟨rfl, rfl⟩ := append_split_unique (f := fun n => C * (n + 1) ^ c)
      (certificateLength_strictMono C c) hu hu' he
    exact ⟨u, hu, ho⟩
  · rintro ⟨u, hu, ho⟩
    exact ⟨u, hu, x, u, rfl, hu, ho⟩

end Turing
