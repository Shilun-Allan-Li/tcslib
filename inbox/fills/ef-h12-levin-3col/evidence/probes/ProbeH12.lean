import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringWitness
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Padding
open TCSlib.Cryptography TCSlib.Cryptography.LevinHardness
/-! H12 probes (evidence only, kernel `decide`). One variable (`K = 1`): literal codes 0 (x₀),
1 (¬x₀); clause code c = ℓ₁ + 2ℓ₂ + 4ℓ₃ < 8. Formula {(x₀ ∨ x₀ ∨ x₀)} = code 0. -/
-- the gadget graph has 3 + 2 + 48 = 53 vertices
example : gadgetN 1 = 53 := by decide
-- the satisfying assignment x₀ = true gives a proper colouring (completeness witness)
example : ProperColoring (gadgetGraph 1 (fun c => c == 0)) (fun u => gadgetColor 1 (fun _ => true) u) := by
  decide
-- the falsifying assignment x₀ = false does not (the clause gadget forces it)
example : ¬ ProperColoring (gadgetGraph 1 (fun c => c == 0))
    (fun u => gadgetColor 1 (fun _ => false) u) := by decide
-- formula {(x₀), (¬x₀)} = codes {0, 7}: x₀ = true fails on clause 7, x₀ = false on clause 0
example : ¬ ProperColoring (gadgetGraph 1 (fun c => c == 0 || c == 7))
    (fun u => gadgetColor 1 (fun _ => true) u) := by decide
-- padding: exact length B² (H12-P2 at the padding stage)
example : (padWord (encGraph (gadgetGraph 1 (fun c => c == 0))) 60).length = 3600 := by
  rw [padWord_encGraph, length_encGraph]
