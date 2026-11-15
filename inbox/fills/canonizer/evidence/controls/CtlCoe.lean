import TCSlib.Cryptography.Asymptotic.Universal

/-! Coercion probe (not a negative control): one explicit application of the projection
coercion `FinDist.instCoeFunForallReal` (`⟨FinDist.prob⟩`) closed by `rfl`. Lean reduces a
projection of an instance even when the instance is irreducible (as in the strict seals), so this
probe passes under every seal: sealing a projection coercion has no effect on elaboration, and the
strict and coe variants agree. -/

theorem ctl_unfold_coe (p : TCSlib.InformationTheory.FinDist Bool) (b : Bool) :
    @CoeFun.coe (TCSlib.InformationTheory.FinDist Bool) (fun _ => Bool → ℝ)
      TCSlib.InformationTheory.FinDist.instCoeFunForallReal p b = p.prob b := rfl
