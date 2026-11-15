import TCSlib.Cryptography.Randomness.Learning.Random

/-! Positive control: the same facts through published readers (`LearnPRF.firstBit_eq`,
`PolyExpr.eval_const`), and the coercion as written in source (`p b`, which elaborates to the
projection `p.prob b`). Passes unsealed and under every seal. -/

theorem ctl_reader_firstBit {n : ℕ} (y : Fin n → Bool) :
    TCSlib.Cryptography.Randomness.LearnPRF.firstBit y = (List.ofFn y).headD false :=
  TCSlib.Cryptography.Randomness.LearnPRF.firstBit_eq y

theorem ctl_reader_eval : (Complexity.PolyExpr.const 1).eval 5 = 1 :=
  Complexity.PolyExpr.eval_const 1 5

theorem ctl_reader_coe (p : TCSlib.InformationTheory.FinDist Bool) (b : Bool) :
    p b = p.prob b := rfl
