import TCSlib.Cryptography.Candidates.PrimesInP

/-! H1-P1 probes (evidence, not library): each string function of the bundle against the
machine composition its proof uses, by `#eval` on all pairs of words of length ≤ 4, all words
of length ≤ 6 (malformed pairs included), triples of words of length ≤ 3, and `xgcdStr` on
`⟦b⟧ ∈ {0, 1, 2, 4, 6, 9, 12}`; plus a few kernel `decide` checks. -/

open Complexity Turing TCSlib.Cryptography.NumberTheory TCSlib.Cryptography.Candidates
open TCSlib.Cryptography.Encoding.BinaryArith

def wordsUpTo : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => [[]] ++ ((wordsUpTo n).flatMap fun w => [false :: w, true :: w])
    |>.eraseDups

def W4 : List (List Bool) := (wordsUpTo 4).eraseDups
def W3 : List (List Bool) := (wordsUpTo 3).eraseDups
def W6 : List (List Bool) := (wordsUpTo 6).eraseDups
def pairs4 : List (List Bool) := W4.flatMap fun a => W4.map fun b => pairEncode a b
def inputs2 : List (List Bool) := pairs4 ++ W6
def triples3 : List (List Bool) :=
  W3.flatMap fun a => W3.flatMap fun x => W3.map fun N => pairEncode a (pairEncode x N)
def inputs3 : List (List Bool) := triples3 ++ W6 ++ pairs4

def le2 (z : List Bool) : List Bool := pairEncode (toLE (pairFstD z)) (toLE (pairSndD z))
def rp (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairSndD z)
def rp3 (z : List Bool) : List Bool :=
  pairEncode (pairFstD z) (pairEncode (pairFstD (pairSndD z)) (pairSndD (pairSndD z)))

def mulM (z : List Bool) := fromLEPoly .var (pairEncode (pairFstD z ++ pairSndD z) (BinArith.mul (le2 z)))
def addM (z : List Bool) := fromLEPoly .var (pairEncode (pairFstD z ++ pairSndD z) (BinArith.add (le2 z)))
def subM (z : List Bool) := fromLEPoly .var (pairEncode (pairFstD z) (BinArith.sub (le2 z)))
def divModM (z : List Bool) :=
  pairEncode (fromLEPoly .var (pairEncode (pairFstD z) (BinArith.div (le2 z))))
    (fromLEPoly .var (pairEncode (pairSndD z) (BinArith.mod (le2 z))))
def leM (z : List Bool) := [BinArith.le (le2 z)]
def modExpM (z : List Bool) :=
  fromLEPoly .var (pairEncode (pairSndD (pairSndD z)) (BinArith.powMod (pairEncode
    (toLE (pairFstD z)) (pairEncode (toLE (pairFstD (pairSndD z)))
      (modExpModulus (pairSndD (pairSndD z)))))))
def xgcdM (z : List Bool) :=
  pairEncode (fromLEPoly .var (pairEncode (pairSndD z) (BinArith.gcd (le2 z))))
    (fromLEPoly .var (pairEncode (pairSndD z) (xgcdInvWord z)))
def sizeM (w : List Bool) := List.replicate (toLE w).length true

/-- Mismatch counts: (re-paired form vs machine, raw form vs machine, number of inputs). -/
def check (F M : List Bool → List Bool) (R : List Bool → List Bool) (xs : List (List Bool)) :
    ℕ × ℕ × ℕ :=
  ((xs.filter fun z => F (R z) != M z).length, (xs.filter fun z => F z != M z).length, xs.length)

#eval s!"mulStr    {check mulStr mulM rp inputs2}"
#eval s!"addStr    {check addStr addM rp inputs2}"
#eval s!"subStr    {check subStr subM rp inputs2}"
#eval s!"divModStr {check divModStr divModM rp inputs2}"
#eval s!"leStr     {check leStr leM rp inputs2}"
#eval s!"xgcdStr   {check xgcdStr xgcdM rp inputs2}"
#eval s!"modExpStr {check modExpStr modExpM rp3 inputs3}"
#eval s!"sizeStr   {check sizeStr sizeM id (W6 ++ pairs4)}"
#eval s!"primeStr  {((W6 ++ pairs4).filter fun w =>
  primeStr w != [decide (LogProg.bitsVal (toLE w)).Prime]).length} \
  {((W6 ++ pairs4).filter fun x => [decide (LogProg.bitsVal x).Prime] !=
    primeStr (fromLEPoly .var (pairEncode x x))).length} {(W6 ++ pairs4).length}"

/-- `xgcdStr` on `⟦b⟧ ∈ {0, 1, 2, 4, 6, 9, 12}` (width 4, and the zero modulus also at widths
0 and 2), every `⟦a⟧ < 16`: `(a, b, |b|, ⟦gcd⟧, ⟦inv⟧, machine = bundle)`. -/
def xgcdTable : List (ℕ × ℕ × ℕ × ℕ × ℕ × Bool) :=
  ([(0, 0), (0, 2), (0, 4), (1, 4), (2, 4), (4, 4), (6, 4), (9, 4), (12, 4)] : List (ℕ × ℕ)).flatMap
    fun (b, k) => (List.range 16).map fun a =>
      let z := pairEncode (natToList 4 a) (natToList k b)
      let o := xgcdStr z
      (a, b, k, listToNat (pairFstD o), listToNat (pairSndD o), o == xgcdM z)

#eval (xgcdTable.filter fun t => t.2.1 = 0).map fun t => s!"{t}"
#eval (xgcdTable.filter fun t => t.2.1 = 1 ∨ t.2.1 = 2).map fun t => s!"{t}"
#eval (xgcdTable.filter fun t => t.2.1 = 4 ∨ t.2.1 = 6).map fun t => s!"{t}"
#eval (xgcdTable.filter fun t => t.2.1 = 9 ∨ t.2.1 = 12).map fun t => s!"{t}"
#eval s!"xgcd table mismatches: {(xgcdTable.filter fun t => !t.2.2.2.2.2).length} of {xgcdTable.length}"

/-! Kernel checks (small instances). -/
example : mulStr (pairEncode [true, true] [true, false, true]) = natToList 5 15 := by decide
-- (`xgcdStr` is not checked by `decide`: `Nat.gcd`/`ZMod.inv` use well-founded recursion, which
-- the kernel does not unfold; its values are in the `#eval` table above.)
example : leStr (pairEncode [false, true] [true]) = [true] := by decide
