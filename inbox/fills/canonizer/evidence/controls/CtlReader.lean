import TCSlib.Cryptography.Asymptotic.Universal

/-! Positive control: the route's facts through published readers (the two readers of this fill
and `PolyExpr.eval_const`). Passes unsealed and under every seal. -/

theorem ctl_reader_codeFormat (xs : List Bool) :
    Turing.oneTapeFormat.serialize (Turing.oneTapeFormat.decode xs) =
      (Turing.codeDecode xs).serialize :=
  Turing.oneTapeFormat_serialize_decode xs

theorem ctl_reader_codeSimulator (α : List Bool) :
    Turing.oneTapeMachineFormat.serialize (Turing.oneTapeMachineFormat.decode α) =
      Turing.oneTapeFormat.serialize (Turing.oneTapeFormat.decode α) :=
  Turing.oneTapeMachineFormat_serialize_decode α

theorem ctl_reader_eval : (Complexity.PolyExpr.const 1).eval 5 = 1 :=
  Complexity.PolyExpr.eval_const 1 5
