import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW BoolCircuit
abbrev TP (n q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : Parameters := ⟨⟨n, 2, q, hq⟩, ℓ, hℓ⟩
def info (P : Parameters) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let c := nandFormula P 0 0
  (P.columns, c.depth, c.size, c.maxFanin, decDepth P)
#eval info (TP 0 2 1 (by decide) (by decide))
#eval info (TP 0 4 2 (by decide) (by decide))
#eval info (TP 1 2 1 (by decide) (by decide))
#eval info (TP 1 4 2 (by decide) (by decide))
#eval info (TP 1 5 3 (by decide) (by decide))
#eval info (TP 1 8 3 (by decide) (by decide))
