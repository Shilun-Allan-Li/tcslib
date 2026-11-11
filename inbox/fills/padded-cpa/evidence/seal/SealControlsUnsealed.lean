import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

/-! Seal controls of the padded-cpa fill (unsealed: every example must pass): seven readings through a definition body. -/

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Composability.ChallengeSim

-- Control 1: `PolyExpr.eval` through its body.
example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
-- Control 2: `zeroBits` through its body.
example (d : ℕ) (j : Fin d) : zeroBits d j = false := rfl
-- Control 3: `padFin` through its body.
example (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false := rfl
-- Control 4: `seedIn` through its body.
example (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) := rfl
-- Control 5: `simulate` through its body.
example {ι σ α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec σ unifSpec) (a : α) (s : σ) :
    simulate impl (.pure a) s = .pure (a, s) := rfl
-- Control 6: the helper `chRun` through its body.
example {ins outs : Fin 2 → ℕ} (g : (Fin (ins 1) → Bool) → List Bool) (a : ℕ)
    (s : Option (Fin (outs 1) → Bool)) : chRun g (.pure a) s = (a, s) := rfl
-- Control 7: the helper `recDin` through its body.
example (L : PolyExpr) : recDin L 1 = .const 2 := rfl
