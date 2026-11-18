/-- The raw PHFE scheme is perfectly correct for every honest draw, in the target-group
exponent [GJLS21, Definition 4.2; Wee20, Section 3.1, (4)-(5)].

**Proof sketch.** Read the raw projection equations and honest experiment. Apply the typed
quadratic correctness theorem to the decoded inputs and coefficient tensor. The class
adapter identity identifies its scalar value with the generic class evaluation; the exact
pushforward laws give AllOutputs of that result. -/
theorem wee20PHFE_raw_correct (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) (hPG : PHFE.PGSound PG) :
    (wee20PHFE_raw G ℓ n d PG).Correct := by
  have hEmbed : (wee20PHFE_raw G ℓ n d PG).embed = PHFE.embedValue G ℓ n d := sorry
  refine ((wee20PHFE_raw G ℓ n d PG).correct_iff).2 ?_
  intro κ f x y
  rw [FEScheme.Raw.honestRun_eq]
  simp only [FEScheme.Raw.setup_eq, FEScheme.Raw.enc_eq, FEScheme.Raw.keyGen_eq,
    Games.OracleComp.map_eq_bind, Games.OracleComp.bind_assoc,
    Games.OracleComp.pure_bind]
  refine Games.OracleComp.AllOutputs.bind (Games.OracleComp.allOutputs_true _) ?_
  intro pp _
  refine Games.OracleComp.AllOutputs.bind (Games.OracleComp.allOutputs_true _) ?_
  intro a _
  refine Games.OracleComp.AllOutputs.bind (Games.OracleComp.allOutputs_true _) ?_
  intro s _
  refine Games.OracleComp.AllOutputs.bind (Games.OracleComp.allOutputs_true _) ?_
  intro t _
  apply Games.OracleComp.allOutputs_pure.mpr
  simp only [wee20PHFE_raw_dec, wee20PHFE_raw_keyCore, wee20PHFE_raw_encCore,
    wee20PHFE_raw_setupCore, wee20PHFE_raw_cprm, hEmbed,
    PHFE.keyCore_eq, PHFE.encCore_eq, PHFE.setupCore_eq, PHFE.dec_eq,
    PHFE.embedValue_eq, PHFE.class_eval_eq G ℓ n d PG hPG]
  exact congrArg some (Quadratic.quadratic_dec_eq G n n PG κ pp
    (PHFE.decodeFunction G ℓ n d κ pp f) (PHFE.decodePublic G ℓ n d κ pp x)
    (PHFE.decodePrivate G ℓ n d κ pp y) (PHFE.decodePrivate G ℓ n d κ pp y) a s t)
