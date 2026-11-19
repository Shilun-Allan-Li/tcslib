import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity

/-! gsw-6b-u15-u17, probe U17-P1 (C12, optional; evidence only, outside the library): on the toy instance
`n = 1`, `m = 1`, `q = 4`, `ℓ = 2` (so `N = 4`), `L = 1`, with a two-seed noise, `#eval` compares
`levelHybrid P χ L μ L r` with `leveledView P χ L μ r` (decidable equality of the whole view) on 16 seeds
for each bit `μ`, and, as a control, `levelHybrid P χ L μ 0 r` with `leveledView P χ L μ r` (expected to
differ on some seed: `H_0` replaces the level key). Expected: `true` everywhere for `H_L`. -/

open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

def toyP : Parameters :=
  ⟨⟨1, 1, 4, by decide⟩, 2, by decide⟩

def toyχ : LWE.Noise where
  Coins := Bool
  sample := fun b => if b then 1 else -1

def toyKeySeed (k : ℕ) : KeySeed toyP toyχ :=
  (fun _ _ => (k : ZMod 4), fun _ => ((k / 4 + 1 : ℕ) : ZMod 4), fun _ => decide (k % 2 = 0))

def toyCoins (k : ℕ) : Coins toyP := fun _ j => Nat.testBit k j.val

def toySeed (k : ℕ) : LeveledSeeds toyP toyχ 1 :=
  (fun d => toyKeySeed (k + 3 * d.val), fun _ i => toyCoins (k + 5 * i.val + 1), toyCoins (k + 7))

def checkTop (μ : Bool) (k : ℕ) : Bool :=
  decide (levelHybrid toyP toyχ 1 μ 1 (toySeed k) = leveledView toyP toyχ 1 μ (toySeed k))

def checkBottom (μ : Bool) (k : ℕ) : Bool :=
  decide (levelHybrid toyP toyχ 1 μ 0 (toySeed k) = leveledView toyP toyχ 1 μ (toySeed k))

#eval (List.range 16).all (checkTop false) && (List.range 16).all (checkTop true)
#eval [false, true].map fun μ => (List.range 16).map (checkTop μ)
#eval [false, true].map fun μ => (List.range 16).map (checkBottom μ)
