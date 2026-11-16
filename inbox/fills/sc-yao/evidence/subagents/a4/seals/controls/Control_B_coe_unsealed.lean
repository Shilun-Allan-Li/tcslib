import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulator
import Lean

/-- Deliberate foreign definitional read for the seal control. -/
example (p : Fin 1 → Prop) : TCSlib.Cryptography.uprob p =
    (Nat.card {a // p a} : ℝ) / Fintype.card (Fin 1) := by
  rfl
