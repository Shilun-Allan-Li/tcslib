import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula

/-! Coercion probe (not a negative control): one explicit application of the projection coercion
`FinDist.instCoeFunForallReal` (`⟨FinDist.prob⟩`) closed by `rfl`. Lean reduces a projection of
an instance even when the instance is irreducible, so this is expected to pass under every seal. -/

theorem ctl_unfold_coe (p : TCSlib.InformationTheory.FinDist Bool) (b : Bool) :
    @CoeFun.coe (TCSlib.InformationTheory.FinDist Bool) (fun _ => Bool → ℝ)
      TCSlib.InformationTheory.FinDist.instCoeFunForallReal p b = p.prob b := rfl
