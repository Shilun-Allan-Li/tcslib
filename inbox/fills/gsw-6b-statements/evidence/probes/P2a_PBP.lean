import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme

/-! Probe P2a (gsw-6b statements, check 7): `homEvalPBP` (G2), noise-free, kernel `decide`.
`n = 1`, `m = 2`, `ℓ = 3`, `q = 5` (`N = 6`): the width-3 permutation program `B3` of length 3 on
2 inputs (maps `id`, `+1`, `+2` on `Fin 3`), noise-free inputs `x j • G`; for every input `x`,
start `s₀` and coordinate `i`: `homEvalPBP P B3 cts (Pi.single s₀ G) i =
(decide (B3.yield x s₀ = i)).toNat • G` (G2's message with noise 0). `B3.IsPermutation` by
`decide`. -/

open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit BranchingProgram

namespace P2

abbrev TP (q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : Parameters := ⟨⟨1, 2, q, hq⟩, ℓ, hℓ⟩
abbrev P5 : Parameters := TP 5 3 (by decide) (by decide)

def enc0 (P : Parameters) (b : ℤ) : Ciphertext P := (b : ZMod P.lwe.modulus) • gadget P

/-- Width-3 program on 2 inputs: `⟨x₀: id | +1⟩, ⟨x₁: +1 | +2⟩, ⟨x₀: +2 | id⟩`. -/
def B3 : BranchingProgram 3 2 :=
  ⟨[⟨0, id, fun i => i + 1⟩, ⟨1, fun i => i + 1, fun i => i + 2⟩, ⟨0, fun i => i + 2, id⟩]⟩

/-- Bijectivity of a map `Fin 3 → Fin 3` from injectivity (finite type), decided pointwise. -/
theorem bij3 (f : Fin 3 → Fin 3) (h : ∀ a b, f a = f b → a = b) : Function.Bijective f :=
  (Finite.injective_iff_bijective).1 fun a b => h a b

theorem B3_perm : B3.IsPermutation := by
  intro ι hι
  simp only [B3, List.mem_cons, List.not_mem_nil, or_false] at hι
  rcases hι with rfl | rfl | rfl <;> exact ⟨bij3 _ (by decide), bij3 _ (by decide)⟩
theorem B3_length : B3.length = 3 := by decide

/-- G2 noise-free, kernel `decide`. -/
theorem g2_noisefree : ∀ (x : Fin 2 → Bool) (s₀ i : Fin 3),
    homEvalPBP P5 B3 (fun j => enc0 P5 (x j).toNat) (Pi.single s₀ (gadget P5)) i =
      enc0 P5 (decide (B3.yield x s₀ = i)).toNat := by
  decide +kernel

end P2

#print axioms P2.g2_noisefree
#print axioms P2.B3_perm
