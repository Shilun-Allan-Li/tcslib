import TCSlib.Cryptography.Foundations.Probability
import Lean

/-- Deliberately read the foreign probability definition, for the seal control only. -/
example (p : Fin 1 → Prop) : TCSlib.Cryptography.uprob p =
    (Nat.card {a // p a} : ℝ) / Fintype.card (Fin 1) := by
  rfl
