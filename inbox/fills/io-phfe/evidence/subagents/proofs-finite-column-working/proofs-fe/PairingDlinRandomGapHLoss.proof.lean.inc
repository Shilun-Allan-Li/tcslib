by
    rw [G.dlinMatrixSlack_eq κ, publicParamsGen_eq G κ, ProbComp.expect_bind]
    apply congrArg (ProbComp.expect (ProbComp.sample (G.gen.Coins κ)))
    funext ρ
    let d : GroupDescription G κ := ⟨G.desc κ ρ, ⟨ρ, rfl⟩⟩
    let c : ℝ :=
      2 / ((G.group κ d.val).order : ℝ) - 1 / ((G.group κ d.val).order : ℝ) ^ 2
    change ProbComp.expect
        (publicParamsCore G κ d <$> ProbComp.sample (GeneratorDraw G κ d)) loss =
      2 / ((G.inst κ ρ).order : ℝ) - 1 / ((G.inst κ ρ).order : ℝ) ^ 2
    rw [ProbComp.expect_map, G.inst_eq κ ρ]
    change ProbComp.expect (ProbComp.sample (GeneratorDraw G κ d))
      (fun g => loss (publicParamsCore G κ d g)) = c
    have hOrder (g : GeneratorDraw G κ d) :
        (publicParamsCore G κ d g).group.order = (G.group κ d.val).order := ?_
    swap
    · rw [PublicParams.group_eq (publicParamsCore G κ d g), publicParamsCore_eq G κ d g]
    have hIntegrand :
        (fun g : GeneratorDraw G κ d => loss (publicParamsCore G κ d g)) =
          (fun _ => c) :=
      funext (fun g => congrArg
        (fun n : ℕ => 2 / (n : ℝ) - 1 / (n : ℝ) ^ 2) (hOrder g))
    rw [hIntegrand]
    exact ProbComp.expect_const (ProbComp.sample (GeneratorDraw G κ d)) c
