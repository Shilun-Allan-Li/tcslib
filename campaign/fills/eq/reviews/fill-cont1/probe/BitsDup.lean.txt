import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.Contract.Catalog
import TCSlib.Complexity.TuringMachine.Build.Contract.Seam
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.BufferWords
import TCSlib.Complexity.TuringMachine.Build.WordTests

/-! Review probe: are the new `Nat.bits` privates one-step consequences of Mathlib lemmas in the
owned file's import closure? -/

#check @Nat.size_eq_bits_len
#check @Nat.size_le_size
#check @Nat.lt_size_self
#check @Nat.size_le
#check @Nat.lt_size

example {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

example (n : ℕ) : n < 2 ^ (Nat.bits n).length := by
  rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self n

example (n : ℕ) : 2 ^ (Nat.bits n).length ≤ 2 * n + 1 := by
  exact?

example {n : ℕ} (hn : 1 ≤ n) : Nat.log 2 n + 1 = (Nat.bits n).length := by
  exact?

example {n : ℕ} (hn : 1 ≤ n) : Nat.log 2 n + 1 = Nat.size n := by
  exact?

example (x : ℕ) : x ^ 6 ≤ 6 ^ 6 * 2 ^ x := by
  exact?

example (m : ℕ) : Nat.ofDigits 2 ((List.replicate m true).map Bool.toNat) = 2 ^ m - 1 := by
  exact?
