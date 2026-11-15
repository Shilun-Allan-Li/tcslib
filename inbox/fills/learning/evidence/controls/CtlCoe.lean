import TCSlib.Cryptography.Randomness.Learning.Random

/-! Coercion probe (not a negative control): one explicit application of the instance
`FinDist.instCoeFunForallReal` (`⟨FinDist.prob⟩`) closed by `rfl`. It was written as the negative
control of the strict seals, but it passes under every seal: the strict variant makes the
instance irreducible (status checked by `probes/CoeProbe.lean`), yet Lean still reduces a
projection of an instance (`instCoeFunForallReal.1`, trace in `logs/coe-probe.log`). So sealing
a projection coercion has no effect on elaboration, and the strict and coe variants agree. -/

theorem ctl_unfold_coe (p : TCSlib.InformationTheory.FinDist Bool) (b : Bool) :
    @CoeFun.coe (TCSlib.InformationTheory.FinDist Bool) (fun _ => Bool → ℝ)
      TCSlib.InformationTheory.FinDist.instCoeFunForallReal p b = p.prob b := rfl
