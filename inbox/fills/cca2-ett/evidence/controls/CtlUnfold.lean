import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games

/-! Negative control: exactly one unfolding of a foreign TCSlib definition (`ETTGame.wR`, a `def`
of `EncryptThenTag/Games.lean`) by `rfl`. Passes unsealed; must fail exactly once sealed (A, B). -/

theorem ctl_unfold_wR (w : List Bool) :
    TCSlib.Cryptography.Composability.ETTGame.wR w = Complexity.pairFstD w := rfl
