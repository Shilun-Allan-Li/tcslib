import TCSlib.Complexity.CircuitComplexity.FormulaArith
import Mathlib.Algebra.BigOperators.Fin

/-!
# Probe P10b4 (part of P10, brief check 7)

F9 (with and without `lo ≤ hi`) by `TreeCircuit.eval`, exhaustively: `M = 3`, `q = 4`.

Closed Booleans computed by `#eval` (`TreeCircuit.eval`/`depth`/`maxFanin` and `Nat.clog` are
well-founded and not kernel-reducible); each entry prints `(failures, cases)`, failures expected
`0`.  No `native_decide`.
-/

open BoolCircuit BoolCircuit.FormulaArith

namespace P10b4

def assigns (n : ℕ) : List (Fin n → Bool) :=
  (List.range (2 ^ n)).map fun m i => m.testBit i
def tally (l : List Bool) : ℕ × ℕ := (l.countP (· = false), l.length)

/-- all coefficient vectors `a : Fin M → ℕ` with `a i < q`, numbered `m < q ^ M` -/
def coeffs (M q : ℕ) : List (Fin M → ℕ) :=
  (List.range (q ^ M)).map fun m i => m / q ^ i.val % q

/-- the coefficient vectors numbered `m ∈ [s, s + k)` -/
def coeffsPart (M q s k : ℕ) : List (Fin M → ℕ) :=
  (List.range' s k).map fun m i => m / q ^ i.val % q

/-- F9 by `TreeCircuit.eval`, for `lo ≤ hi ≤ q` (r3's hypotheses) -/
def checkF9 (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (hi + 1)).flatMap fun lo =>
      let F := modSumInterval a q lo hi
      (assigns M).map fun x =>
        F.eval x == decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)

/-- the same equation for `hi < lo ≤ q` (outside r3's hypothesis `lo ≤ hi`) -/
def checkF9rev (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun lo =>
    (List.range lo).flatMap fun hi =>
      let F := modSumInterval a q lo hi
      (assigns M).map fun x =>
        F.eval x == decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)

/-- F10 on every built formula (all `lo, hi ≤ q`): depth `≤ modSumDepth M q`, fan-in `≤ 2` -/
def checkF10 (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (q + 1)).map fun lo =>
      let F := modSumInterval a q lo hi
      decide (F.depth ≤ modSumDepth M q) && decide (F.maxFanin ≤ 2)

/-- bit-parallel evaluation on all `2 ^ M` assignments at once: bit `m` of the result is the
value under `fun i => m.testBit i` (the order of `assigns`).  Probe-only, cross-checked against
`TreeCircuit.eval` by `checkMask` in the same file. -/
partial def evalMask (M : ℕ) : TreeCircuit M → ℕ
  | .lit l =>
      let mk := ((List.range (2 ^ M)).filter fun m => m.testBit l.idx.val).foldl
        (fun acc m => acc ||| 2 ^ m) 0
      if l.sign then mk else (2 ^ 2 ^ M - 1) ^^^ mk
  | .node true cs => cs.foldl (fun acc c => acc &&& evalMask M c) (2 ^ 2 ^ M - 1)
  | .node false cs => cs.foldl (fun acc c => acc ||| evalMask M c) 0

/-- the expected value of F9's right side, as a mask over the assignments -/
def rhsMask (M q lo hi : ℕ) (a : Fin M → ℕ) : ℕ :=
  ((List.range (2 ^ M)).filter fun m =>
    decide (lo ≤ (∑ i, (m.testBit i.val).toNat * a i) % q ∧
      (∑ i, (m.testBit i.val).toNat * a i) % q < hi)).foldl (fun acc m => acc ||| 2 ^ m) 0

/-- F9 by the bit-parallel evaluator, for `lo ≤ hi ≤ q` -/
def checkF9mask (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (hi + 1)).map fun lo =>
      evalMask M (modSumInterval a q lo hi) == rhsMask M q lo hi a

/-- `evalMask` agrees with `TreeCircuit.eval` on the formulas of the given coefficients -/
def checkMask (M q : ℕ) (as : List (Fin M → ℕ)) : List Bool :=
  as.flatMap fun a => (List.range (q + 1)).flatMap fun hi =>
    (List.range (hi + 1)).flatMap fun lo =>
      let F := modSumInterval a q lo hi
      (List.range (2 ^ M)).map fun m =>
        (evalMask M F).testBit m == F.eval fun i => m.testBit i.val

#eval (3, 4, tally (checkF9 3 4 (coeffs 3 4)), tally (checkF9rev 3 4 (coeffs 3 4)))

end P10b4
