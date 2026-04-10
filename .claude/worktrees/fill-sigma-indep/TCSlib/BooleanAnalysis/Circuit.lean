-- import Mathlib.Data.Real.Basic
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.Data.Vector.Basic
-- import Mathlib.Algebra.MvPolynomial.Basic
-- import Mathlib.Algebra.MvPolynomial.Eval
-- import Mathlib.Data.ZMod.Basic
-- import Mathlib.Data.Fintype.Vector
-- import Mathlib.Data.Real.Sqrt
-- import Mathlib.Data.Fintype.Pi
-- import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Vector.Basic

-- unbounded fan-in circuit
inductive Circuit (n : ℕ) where
  | input (i : Fin n)           : Circuit n
  | not   (c : Circuit n)       : Circuit n
  | and   (cs : List (Circuit n)) : Circuit n
  | or    (cs : List (Circuit n)) : Circuit n

namespace Circuit

/-
mutually recursive evaluation. "mutual" is needed so that Lean can suspend
the circular dependency rule. furthermore somehow Lean knows that this will
terminate.
-/
mutual
def eval {n : ℕ} (v : Vector Bool n) : Circuit n → Bool
  | input i => v.get i
  | not c   => !(eval v c)
  | and cs  => evalAnd v cs
  | or cs   => evalOr v cs

def evalAnd {n : ℕ} (v : Vector Bool n) : List (Circuit n) → Bool
  | [] => true --base case: this does not change output
  | c :: cs => eval v c && evalAnd v cs --kinda inefficient i guess.

def evalOr {n : ℕ} (v : Vector Bool n) : List (Circuit n) → Bool
  | [] => false
  | c :: cs => eval v c || evalOr v cs
end

-- mutually recursive depth calculation
mutual
def depth {n : ℕ} : Circuit n → ℕ
  | input _ => 0
  | not c   => depth c
  | and cs  => 1 + maxDepth cs
  | or cs   => 1 + maxDepth cs

def maxDepth {n : ℕ} : List (Circuit n) → ℕ
  | [] => 0
  | c :: cs => max (depth c) (maxDepth cs)
end

-- mutually recursive size calculation
mutual
def size {n : ℕ} : Circuit n → ℕ
  | input _ => 1
  | not c   => size c
  | and cs  => 1 + sumSize cs
  | or cs   => 1 + sumSize cs

def sumSize {n : ℕ} : List (Circuit n) → ℕ
  | [] => 0
  | c :: cs => size c + sumSize cs
end

end Circuit

def parity {n : ℕ} (v : Vector Bool n) : Bool :=
  v.toList.foldl xor false
