import TCSlib.Cryptography.SecretSharing.ShamirEfficient
open Turing Complexity TCSlib.Shamir TCSlib.SecretSharing

/-! H11-P1: shares at p = 7, k = 2, n = 3, and reconstruction from every 2-set.
Parameter word ⟨7, ⟨1^2, 3⟩⟩; party i (0-based) is the residue i + 1; coins r < 7^1. -/
def P : List Bool := pairEncode (Nat.bits 7) (pairEncode (List.replicate 2 true) (Nat.bits 3))
def num (w : List Bool) : ℕ := Complexity.LogProg.bitsVal w
def shareM (sec r x : ℕ) : ℕ :=
  num (shareRaw (pairEncode P (pairEncode (Nat.bits sec) (pairEncode (Nat.bits r) (Nat.bits x)))))
/-- reference: Shamir.scheme's share at k = 2 is `sec + x · q` with `q` the constant coin. -/
def shareRef (sec r x : ℕ) : ℕ := ((sec + x * r : ℕ) : ZMod 7).val
def recM (xs : List ℕ) (ys : List ℕ) : ℕ :=
  num (recombineRaw (pairEncode (Nat.bits 7) (BinArith.encWords
    ((xs.zip ys).map fun (x, y) => pairEncode (Nat.bits x) (Nat.bits y)))))
def pairs : List (ℕ × ℕ) := [(1, 2), (1, 3), (2, 3)]
#eval (List.range 7).map fun r => (r, (List.range 3).map fun i => shareM 5 r (i + 1))
#eval (List.range 7).all fun sec => (List.range 7).all fun r => [1, 2, 3].all fun x =>
  shareM sec r x == shareRef sec r x
#eval (List.range 7).all fun sec => (List.range 7).all fun r => pairs.all fun (a, b) =>
  recM [a, b] [shareM sec r a, shareM sec r b] == sec
#eval (List.range 7).all fun sec => (List.range 7).all fun r =>
  recM [1, 2, 3] [shareM sec r 1, shareM sec r 2, shareM sec r 3] == sec

/-! H11-P2: one BGW multiplication gate at p = 7, d = 1 (k = 2), three parties 1, 2, 3.
Inputs a = 3 (coin 4) and b = 5 (coin 2); party j's local product u_j = a_j · b_j; each party i
re-shares u_i with coin ρ_i; party j recombines the received shares (`recombineRaw`).
Reference: `degreeReduce R A u j = ∑_i λ_i · R.reshare i (u i) j` with the Lagrange coefficients
at 0 of the nodes 1, 2, 3 over ℤ_7: λ = (3, −3, 1) = (3, 4, 1). -/
def aSh (j : ℕ) : ℕ := shareM 3 4 j
def bSh (j : ℕ) : ℕ := shareM 5 2 j
def uSh (j : ℕ) : ℕ := ((aSh j * bSh j : ℕ) : ZMod 7).val
def ρ (i : ℕ) : ℕ := [0, 6, 1, 3].getD i 0
def reshareTo (i j : ℕ) : ℕ := shareM (uSh i) (ρ i) j
def reduceM (j : ℕ) : ℕ := recM [1, 2, 3] ((List.range 3).map fun i => reshareTo (i + 1) j)
def reduceRef (j : ℕ) : ℕ :=
  ((3 * reshareTo 1 j + 4 * reshareTo 2 j + 1 * reshareTo 3 j : ℕ) : ZMod 7).val
#eval ([1, 2, 3].map aSh, [1, 2, 3].map bSh, [1, 2, 3].map uSh)
#eval ([1, 2, 3].map reduceM, [1, 2, 3].map reduceRef)
#eval [1, 2, 3].all fun j => reduceM j == reduceRef j
-- the reduced vector is a degree-1 sharing of a · b = 15 = 1 (mod 7): any two parties recombine 1
#eval pairs.map fun (x, y) => recM [x, y] [reduceM x, reduceM y]
