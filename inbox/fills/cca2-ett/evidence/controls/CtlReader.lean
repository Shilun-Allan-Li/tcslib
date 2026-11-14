import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games

/-! Positive control: the same facts through published readers (`ETTGame.wR_eq`,
`PolyExpr.eval_const`). Passes unsealed and under both seals. -/

theorem ctl_reader_wR (w : List Bool) :
    TCSlib.Cryptography.Composability.ETTGame.wR w = Complexity.pairFstD w :=
  TCSlib.Cryptography.Composability.ETTGame.wR_eq w

theorem ctl_reader_eval : (Complexity.PolyExpr.const 1).eval 5 = 1 :=
  Complexity.PolyExpr.eval_const 1 5
