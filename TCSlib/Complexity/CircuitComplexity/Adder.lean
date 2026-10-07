/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Digits.Defs
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.SpaceComplexity.Machines.Bin

/-!
# Ripple-carry addition circuits

The circuit behind the second half of [AB09, Ex 6.3]: the language `{⟨m, n, m + n⟩}` has
linear-size circuits implementing "the grade-school algorithm for addition", where a
constant-size circuit adds two bits and an incoming carry and the outgoing carry feeds the
next position.  We build that circuit in the book's model `BoolCircuit.DAGCircuit` (fan-in
two, size counting every vertex); each carry vertex is read by two gates of the next
position, which is exactly the sharing the DAG model permits and a formula would not.
The language and its `SIZE` / `P/poly` membership are in `AdderLanguage.lean`.

## Main definitions

* `BoolCircuit.bitsVal` — the number a little-endian bit list denotes,
  `Nat.ofDigits 2` of its `0/1` digits; `BoolCircuit.prefixVal` — the same for the low
  `i` bits of a bit sequence `ℕ → Bool`.
* `BoolCircuit.xorGates`, `BoolCircuit.fullAdderGates` — the XOR and full-adder gadgets
  (`4` and `9` gates, fan-in at most two).
* `BoolCircuit.bitBlock`, `BoolCircuit.adderGates` — one bit position (`15` gates), and
  the whole gate list.
* `BoolCircuit.adderCircuit n` — the ripple-carry checker on `n` inputs, reading three
  `⌊n / 3⌋`-bit blocks `a`, `b`, `c` and outputting `1` iff `c = a + b`.
* `BoolCircuit.carryBit`, `BoolCircuit.sumBit`, `BoolCircuit.agreeBit` — the
  grade-school carry, sum bits, and the running comparison with `c`.

## Main results

* `BoolCircuit.bitsVal_eq_logProg_bitsVal` — `bitsVal` is the recursive
  `Complexity.LogProg.bitsVal` of the space track (`SpaceComplexity/Machines/Bin.lean`).
* `BoolCircuit.runWith_fullAdderGates` — the full adder computes the sum bit
  `a ⊕ b ⊕ cin` and the carry `(a ∧ b) ∨ ((a ⊕ b) ∧ cin)`.
* `BoolCircuit.prefixVal_add` — grade-school addition is correct over `ℕ`.
* `BoolCircuit.adderCircuit_eval_append` — on `a ++ b ++ c` with `|a| = |b| = |c|` the
  circuit outputs `true` iff `bitsVal c = bitsVal a + bitsVal b`.
* `BoolCircuit.adderCircuit_isFaninTwo`, `BoolCircuit.adderCircuit_size` — fan-in two and
  size `n + 15 ⌊n / 3⌋ + 4`, i.e. `18 k + 4` on `3 k` inputs
  (`BoolCircuit.adderCircuit_size_three_mul`).

## Divergences from [AB09, Ex 6.3]

* **Input layout and final carry.**  [AB09] fixes neither.  The three numbers are
  concatenated (not interleaved) little-endian blocks of a common width `k`; since `c` has
  only `k` bits, the circuit also checks that the carry out of the top position is `0`
  (a sum that needs `k + 1` bits is encoded at width `k + 1`).
* **Explicit constants.**  "O(1) per bit" is `15` gates per bit position: the full adder
  (`9`), an XOR of the sum bit with `c`'s bit (`4`), a `¬` and an accumulating `∧`; plus
  `4` gates (constants `false`/`true` for the initial carry and accumulator, `¬carry` and
  the output `∧`).  The model's constants are fan-in-zero gates (see `DAGCircuit.lean`).
* For `n` not divisible by `3`, `adderCircuit n` simply ignores the last `n mod 3` inputs;
  the family in `AdderLanguage.lean` uses a constant-`false` circuit at those lengths.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Example 6.3.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-! ## Numbers denoted by bit strings -/

/-- The number denoted by a little-endian bit list: bit `j` has weight `2 ^ j`.  This is
Mathlib's `Nat.ofDigits 2` applied to the list's `0/1` digits. -/
def bitsVal (l : List Bool) : ℕ :=
  Nat.ofDigits 2 (l.map Bool.toNat)

/-- The number denoted by the low `i` bits of a bit sequence `f`: `∑_{j < i} f j · 2 ^ j`. -/
def prefixVal (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => prefixVal f i + (f i).toNat * 2 ^ i

/-- The value of zero bits is `0`. -/
@[simp] theorem prefixVal_zero (f : ℕ → Bool) : prefixVal f 0 = 0 := rfl

/-- Adding the top bit: `val (f 0 … f i) = val (f 0 … f (i-1)) + f i · 2 ^ i`. -/
theorem prefixVal_succ (f : ℕ → Bool) (i : ℕ) :
    prefixVal f (i + 1) = prefixVal f i + (f i).toNat * 2 ^ i := rfl

/-- Peeling off the lowest bit: `val (f 0, f 1, …) = f 0 + 2 · val (f 1, f 2, …)`. -/
theorem prefixVal_succ' (f : ℕ → Bool) (i : ℕ) :
    prefixVal f (i + 1) = (f 0).toNat + 2 * prefixVal (fun j => f (j + 1)) i := by
  induction i with
  | zero => simp [prefixVal_succ]
  | succ i ih => rw [prefixVal_succ, ih, prefixVal_succ, pow_succ]; ring

/-- An `i`-bit number is below `2 ^ i`. -/
theorem prefixVal_lt (f : ℕ → Bool) (i : ℕ) : prefixVal f i < 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := Bool.toNat_le (f i)
    rw [prefixVal_succ, pow_succ]
    nlinarith

/-- The value of the low `i` bits depends only on those bits. -/
theorem prefixVal_congr {f g : ℕ → Bool} {i : ℕ} (h : ∀ j < i, f j = g j) :
    prefixVal f i = prefixVal g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [prefixVal_succ, prefixVal_succ, ih fun j hj => h j (by omega), h i (by omega)]

/-- Binary representations of a fixed width are unique. -/
theorem prefixVal_inj {f g : ℕ → Bool} {i : ℕ} (h : prefixVal f i = prefixVal g i) :
    ∀ j < i, f j = g j := by
  induction i with
  | zero => intro j hj; omega
  | succ i ih =>
    rw [prefixVal_succ, prefixVal_succ] at h
    have hf := prefixVal_lt f i
    have hg := prefixVal_lt g i
    have htop : f i = g i := by
      cases hfi : f i <;> cases hgi : g i <;> (simp_all; try omega)
    rw [htop] at h
    have hlow := ih (by omega)
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hlow j hj
    · exact htop

/-- `bitsVal l` is the value of the `|l|` bits of `l`. -/
theorem bitsVal_eq_prefixVal (l : List Bool) :
    bitsVal l = prefixVal (fun j => l.getD j false) l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.length_cons, prefixVal_succ']
    simp only [bitsVal, List.map_cons, Nat.ofDigits_cons, List.getD_cons_zero,
      List.getD_cons_succ] at ih ⊢
    rw [ih]

/-- `bitsVal` agrees with the little-endian value `Complexity.LogProg.bitsVal` used by
the logspace counters of `SpaceComplexity/Machines/Bin.lean`. -/
theorem bitsVal_eq_logProg_bitsVal (l : List Bool) : bitsVal l = Complexity.LogProg.bitsVal l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [bitsVal, List.map_cons, Nat.ofDigits_cons, Complexity.LogProg.bitsVal] at ih ⊢
    rw [ih]

/-! ## Gadgets -/

/-- The XOR gadget, appended at vertex `L`: gates `x ∨ y`, `x ∧ y`, `¬(x ∧ y)` and
`(x ∨ y) ∧ ¬(x ∧ y) = x ⊕ y`, at vertices `L, …, L + 3`. -/
def xorGates (x y L : ℕ) : List DAGGate :=
  [⟨.or, [x, y]⟩, ⟨.and, [x, y]⟩, ⟨.not, [L + 1]⟩, ⟨.and, [L, L + 2]⟩]

/-- Running the XOR gadget on vertex values `vs` (with `L = |vs|`) appends the four gate
values, the last being `vs[x] ⊕ vs[y]`. -/
theorem runWith_xorGates (vs : List Bool) {x y L : ℕ} (hL : vs.length = L)
    (hx : x < L) (hy : y < L) :
    runWith DAGGate.eval (xorGates x y L) vs =
      vs ++ [vs.getD x false || vs.getD y false, vs.getD x false && vs.getD y false,
        !(vs.getD x false && vs.getD y false), vs.getD x false ^^ vs.getD y false] := by
  subst hL
  simp only [xorGates, runWith_cons, runWith_nil, DAGGate.eval]
  simp [List.getElem?_append_left hx, List.getElem?_append_left hy]
  cases vs[x]?.getD false <;> cases vs[y]?.getD false <;> simp

/-- The full-adder gadget, appended at vertex `L`, on bits `a`, `b` and carry-in `cin`:
an XOR `p = a ⊕ b` (vertices `L, …, L + 3`), an XOR `s = p ⊕ cin` (vertices
`L + 4, …, L + 7`, the sum bit at `L + 7`), and the carry-out
`(a ∧ b) ∨ (p ∧ cin)` at `L + 8`.  Nine gates, each of fan-in at most two; the carry-in
vertex is read twice, by different gates.  [AB09, Ex 6.3] -/
def fullAdderGates (a b cin L : ℕ) : List DAGGate :=
  xorGates a b L ++ xorGates (L + 3) cin (L + 4) ++ [⟨.or, [L + 1, L + 5]⟩]

/-- The full adder is correct: on vertex values `vs` with `L = |vs|` and bits
`A = vs[a]`, `B = vs[b]`, `Cin = vs[cin]`, it appends nine values, of which the eighth is
the sum bit `A ⊕ B ⊕ Cin` and the ninth the carry `(A ∧ B) ∨ ((A ⊕ B) ∧ Cin)`.
[AB09, Ex 6.3] -/
theorem runWith_fullAdderGates (vs : List Bool) {a b cin L : ℕ} (hL : vs.length = L)
    (ha : a < L) (hb : b < L) (hc : cin < L) :
    runWith DAGGate.eval (fullAdderGates a b cin L) vs =
      vs ++ [vs.getD a false || vs.getD b false, vs.getD a false && vs.getD b false,
        !(vs.getD a false && vs.getD b false), vs.getD a false ^^ vs.getD b false,
        (vs.getD a false ^^ vs.getD b false) || vs.getD cin false,
        (vs.getD a false ^^ vs.getD b false) && vs.getD cin false,
        !((vs.getD a false ^^ vs.getD b false) && vs.getD cin false),
        (vs.getD a false ^^ vs.getD b false) ^^ vs.getD cin false,
        (vs.getD a false && vs.getD b false) ||
          ((vs.getD a false ^^ vs.getD b false) && vs.getD cin false)] := by
  subst hL
  rw [fullAdderGates, runWith_append, runWith_append, runWith_xorGates vs rfl ha hb,
    runWith_xorGates (x := vs.length + 3) (L := vs.length + 4) _ ?hL (by omega) (by omega)]
  case hL => simp
  simp only [runWith_cons, runWith_nil, DAGGate.eval]
  simp [List.getElem?_append_left hc]

/-! ## The ripple-carry circuit -/

namespace RippleCarry

/-! Internal plumbing of the ripple-carry construction: per-position gate blocks and the
vertex numbering. -/

/-- The gates of bit position `i`, appended at vertex `L`: a full adder on input bits `a`,
`b` and carry-in `cin` (sum at `L + 7`, carry-out at `L + 8`), an XOR comparing the sum
with the input bit `c` (at `L + 12`), its negation `s = c` (at `L + 13`), and the running
conjunction `acc ∧ (s = c)` (at `L + 14`).  Fifteen gates. -/
def bitBlock (a b c cin acc L : ℕ) : List DAGGate :=
  fullAdderGates a b cin L ++ xorGates (L + 7) c (L + 9) ++
    [⟨.not, [L + 12]⟩, ⟨.and, [acc, L + 13]⟩]

/-- One bit position of the ripple-carry circuit is correct: on vertex values `vs` with
`L = |vs|` it appends `15` values, the carry-out `(A ∧ B) ∨ ((A ⊕ B) ∧ Cin)` at `L + 8` and
the updated accumulator `Acc ∧ ¬(A ⊕ B ⊕ Cin ⊕ C)` at `L + 14`. -/
theorem runWith_bitBlock (vs : List Bool) {a b c cin acc L : ℕ} (hL : vs.length = L)
    (ha : a < L) (hb : b < L) (hc : c < L) (hcin : cin < L) (hacc : acc < L) :
    (runWith DAGGate.eval (bitBlock a b c cin acc L) vs).length = L + 15 ∧
    (runWith DAGGate.eval (bitBlock a b c cin acc L) vs).getD (L + 8) false =
      ((vs.getD a false && vs.getD b false) ||
        ((vs.getD a false ^^ vs.getD b false) && vs.getD cin false)) ∧
    (runWith DAGGate.eval (bitBlock a b c cin acc L) vs).getD (L + 14) false =
      (vs.getD acc false &&
        !(((vs.getD a false ^^ vs.getD b false) ^^ vs.getD cin false) ^^ vs.getD c false)) := by
  subst hL
  rw [bitBlock, runWith_append, runWith_append, runWith_fullAdderGates vs rfl ha hb hcin,
    runWith_xorGates (x := vs.length + 7) (L := vs.length + 9) _ ?hL (by omega) (by omega)]
  case hL => simp
  simp only [runWith_cons, runWith_nil, DAGGate.eval]
  simp [List.getElem?_append_left hc, List.getElem?_append_left hacc]

/-- The carry vertex entering bit position `i` of the `n`-input circuit: the constant
`false` gate `n` for `i = 0`, else the carry-out of the previous block. -/
def cinIdx (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => n + 2 + 15 * i + 8

/-- The accumulator vertex entering bit position `i`: the constant `true` gate `n + 1` for
`i = 0`, else the running conjunction of the previous block. -/
def accIdx (n : ℕ) : ℕ → ℕ
  | 0 => n + 1
  | i + 1 => n + 2 + 15 * i + 14

/-- The gates of the first `i` bit positions of the ripple-carry circuit with `n` inputs
and block width `k`: the constants `false` (`∨` of nothing) and `true` (`∧` of nothing),
then one `bitBlock` per position, position `j` reading the inputs `j`, `k + j`, `2 k + j`. -/
def adderGatesUpTo (n k : ℕ) : ℕ → List DAGGate
  | 0 => [constGate false, constGate true]
  | i + 1 => adderGatesUpTo n k i ++
      bitBlock i (k + i) (2 * k + i) (cinIdx n i) (accIdx n i) (n + 2 + 15 * i)

/-- The first `i` bit positions of the ripple-carry circuit use `2 + 15 i` gates. -/
@[simp] theorem length_adderGatesUpTo (n k i : ℕ) :
    (adderGatesUpTo n k i).length = 2 + 15 * i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [adderGatesUpTo, ih, bitBlock, fullAdderGates, xorGates]; ring

end RippleCarry

open RippleCarry

/-- All gates of the ripple-carry circuit on `n` inputs, `k = ⌊n / 3⌋`: the `k` bit
positions, then `¬carry_k` and the output `acc_k ∧ ¬carry_k`. -/
def adderGates (n : ℕ) : List DAGGate :=
  adderGatesUpTo n (n / 3) (n / 3) ++
    [⟨.not, [cinIdx n (n / 3)]⟩, ⟨.and, [accIdx n (n / 3), n + 2 + 15 * (n / 3)]⟩]

/-! ### Acyclicity and fan-in

Stated with the model's gate-list predicates `GatesAcyclic` and `DAGGate.FaninTwo`
(`DAGCircuit.lean`). -/

/-- The carry vertex entering bit position `i` exists before that position's gates. -/
private theorem cinIdx_lt (n i : ℕ) : cinIdx n i < n + 2 + 15 * i := by
  cases i <;> simp only [cinIdx] <;> omega

/-- The accumulator vertex entering bit position `i` exists before that position's gates. -/
private theorem accIdx_lt (n i : ℕ) : accIdx n i < n + 2 + 15 * i := by
  cases i <;> simp only [accIdx] <;> omega

/-- A bit position, appended at vertex `L`, reads only earlier vertices. -/
private theorem gatesAcyclic_bitBlock {a b c cin acc L : ℕ} (ha : a < L) (hb : b < L) (hc : c < L)
    (hcin : cin < L) (hacc : acc < L) : GatesAcyclic L (bitBlock a b c cin acc L) := by
  simp [bitBlock, fullAdderGates, xorGates]
  omega

/-- Every gate of a bit position is admissible in a fan-in-two circuit, provided the two
summand bits are distinct vertices. -/
private theorem faninTwo_bitBlock {a b c cin acc L : ℕ} (hab : a ≠ b) (hc : c < L) (hcin : cin < L)
    (hacc : acc < L) : ∀ g ∈ bitBlock a b c cin acc L, g.FaninTwo := by
  simp [bitBlock, fullAdderGates, xorGates, DAGGate.FaninTwo, DAGGate.WellFormed]
  omega

/-- The first `i` bit positions read only earlier vertices, provided the three `k`-bit
input blocks fit in the `n` inputs. -/
private theorem gatesAcyclic_adderGatesUpTo {n k : ℕ} (hk : 3 * k ≤ n) (i : ℕ) :
    GatesAcyclic n (adderGatesUpTo n k i) := by
  induction i with
  | zero => simp [adderGatesUpTo]
  | succ i ih =>
    rw [adderGatesUpTo, gatesAcyclic_append, length_adderGatesUpTo,
      show n + (2 + 15 * i) = n + 2 + 15 * i by omega]
    exact ⟨ih, gatesAcyclic_bitBlock (by omega) (by omega) (by omega) (cinIdx_lt n i)
      (accIdx_lt n i)⟩

/-- Every gate of the first `i ≤ k` bit positions is admissible in a fan-in-two circuit;
`i ≤ k` makes the summand inputs `j` and `k + j` distinct. -/
private theorem faninTwo_adderGatesUpTo {n k : ℕ} (hk : 3 * k ≤ n) (i : ℕ) (hi : i ≤ k) :
    ∀ g ∈ adderGatesUpTo n k i, g.FaninTwo := by
  induction i with
  | zero => simp [adderGatesUpTo]
  | succ i ih =>
    intro g hg
    rw [adderGatesUpTo, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih (by omega) g hg
    · exact faninTwo_bitBlock (by omega) (by omega) (cinIdx_lt n i) (accIdx_lt n i) g hg

/-- The ripple-carry gate list reads only earlier vertices. -/
private theorem gatesAcyclic_adderGates (n : ℕ) : GatesAcyclic n (adderGates n) := by
  rw [adderGates, gatesAcyclic_append]
  refine ⟨gatesAcyclic_adderGatesUpTo (by omega) _, ?_⟩
  have := cinIdx_lt n (n / 3)
  have := accIdx_lt n (n / 3)
  simp
  omega

/-- Every gate of the ripple-carry circuit is admissible in a fan-in-two circuit. -/
private theorem faninTwo_adderGates (n : ℕ) : ∀ g ∈ adderGates n, g.FaninTwo := by
  intro g hg
  rw [adderGates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact faninTwo_adderGatesUpTo (by omega) _ le_rfl g hg
  · have := accIdx_lt n (n / 3)
    simp at hg
    rcases hg with rfl | rfl
    · simp [DAGGate.FaninTwo, DAGGate.WellFormed]
    · simp [DAGGate.FaninTwo, DAGGate.WellFormed]; omega

/-- The ripple-carry circuit on `n` inputs.  With `k = ⌊n / 3⌋` it reads the inputs as
little-endian `k`-bit numbers `a = x₀ … x_{k-1}`, `b = x_k … x_{2k-1}`,
`c = x_{2k} … x_{3k-1}`, adds `a` and `b` bit by bit with a chain of full adders (each
carry vertex read by the next position), and outputs `1` iff every sum bit equals the
corresponding bit of `c` and the final carry is `0`, that is iff `c = a + b`
(`adderCircuit_eval_append`).  [AB09, Ex 6.3] -/
def adderCircuit (n : ℕ) : DAGCircuit n where
  gates := adderGates n
  output := n + 15 * (n / 3) + 3
  args_lt := gatesAcyclic_adderGates n
  output_lt := by simp [adderGates]; omega

/-- The ripple-carry circuit has fan-in two.  [AB09, Ex 6.3] -/
theorem adderCircuit_isFaninTwo (n : ℕ) : (adderCircuit n).IsFaninTwo :=
  ⟨fun g hg => (faninTwo_adderGates n g hg).1, fun g hg => (faninTwo_adderGates n g hg).2⟩

/-- The ripple-carry circuit on `n` inputs has `n + 15 ⌊n / 3⌋ + 4` vertices: `15` gates
per bit position plus `4`.  [AB09, Ex 6.3] -/
theorem adderCircuit_size (n : ℕ) : (adderCircuit n).size = n + 15 * (n / 3) + 4 := by
  simp [DAGCircuit.size, adderCircuit, adderGates]; ring

/-- On `3 k` inputs (three `k`-bit numbers) the ripple-carry circuit has size `18 k + 4`,
linear in `k`.  [AB09, Ex 6.3] -/
theorem adderCircuit_size_three_mul (k : ℕ) : (adderCircuit (3 * k)).size = 18 * k + 4 := by
  rw [adderCircuit_size]; omega

/-! ### Correctness -/

/-- The carry entering bit position `i` when adding the bit sequences `A` and `B`:
`carry 0 = 0`, `carry (i + 1) = (A_i ∧ B_i) ∨ ((A_i ⊕ B_i) ∧ carry i)`. -/
def carryBit (A B : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => (A i && B i) || ((A i ^^ B i) && carryBit A B i)

/-- Bit `i` of the sum of `A` and `B`: `A_i ⊕ B_i ⊕ carry i`. -/
def sumBit (A B : ℕ → Bool) (i : ℕ) : Bool :=
  (A i ^^ B i) ^^ carryBit A B i

/-- The running check of the ripple-carry circuit: `agree i` holds iff the first `i` sum
bits of `A + B` equal the first `i` bits of `C`. -/
def agreeBit (A B C : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | i + 1 => agreeBit A B C i && !(sumBit A B i ^^ C i)

/-- Grade-school addition is correct: the low `i` bits of `A` and `B` add up to the low
`i` sum bits plus the carry out of position `i - 1`, weighted `2 ^ i`.

**Proof sketch.** Induction on `i`.  At position `i` the full adder satisfies
`A_i + B_i + carry_i = s_i + 2 · carry_{i+1}` (a check of the eight cases); multiplying by
`2 ^ i` and adding the induction hypothesis gives the claim at `i + 1`. -/
theorem prefixVal_add (A B : ℕ → Bool) (i : ℕ) :
    prefixVal A i + prefixVal B i =
      prefixVal (sumBit A B) i + 2 ^ i * (carryBit A B i).toNat := by
  induction i with
  | zero => simp [carryBit]
  | succ i ih =>
    -- one full-adder step: `A_i + B_i + carry_i = s_i + 2 · carry_{i+1}`
    have hstep : (A i).toNat + (B i).toNat + (carryBit A B i).toNat =
        (sumBit A B i).toNat + 2 * (carryBit A B (i + 1)).toNat := by
      simp only [sumBit, carryBit]
      cases A i <;> cases B i <;> cases carryBit A B i <;> rfl
    have h2 := congrArg (· * 2 ^ i) hstep
    simp only at h2
    rw [prefixVal_succ, prefixVal_succ, prefixVal_succ, pow_succ]
    nlinarith [ih, h2]

/-- The accumulator `agree i` holds iff the first `i` bits of `C` are the first `i` sum
bits of `A + B`. -/
theorem agreeBit_iff (A B C : ℕ → Bool) (i : ℕ) :
    agreeBit A B C i = true ↔ ∀ j < i, C j = sumBit A B j := by
  induction i with
  | zero => simp [agreeBit]
  | succ i ih =>
    have hxor : (!(sumBit A B i ^^ C i)) = true ↔ C i = sumBit A B i := by
      cases sumBit A B i <;> cases C i <;> simp
    simp only [agreeBit, Bool.and_eq_true, ih, hxor]
    constructor
    · rintro ⟨h, hi⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h j hj
      · exact hi
    · intro h
      exact ⟨fun j hj => h j (by omega), h i (by omega)⟩

/-- The ripple-carry check is exact: all `i` sum bits agree with `C` and the final carry
is `0` iff `C = A + B` as `i`-bit numbers.

**Proof sketch.** By `prefixVal_add`, `A + B = s + 2 ^ i · carry_i`.  If `C` agrees with
`s` and `carry_i = 0` then `C = s = A + B`.  Conversely, if `C = A + B` then
`carry_i = 0`, since otherwise `A + B ≥ 2 ^ i > C`; hence `C = s` as `i`-bit numbers,
and binary representations of a fixed width are unique (`prefixVal_inj`). -/
theorem agree_and_noCarry_iff (A B C : ℕ → Bool) (i : ℕ) :
    (agreeBit A B C i && !carryBit A B i) = true ↔
      prefixVal C i = prefixVal A i + prefixVal B i := by
  have hadd := prefixVal_add A B i
  rw [Bool.and_eq_true, agreeBit_iff, Bool.not_eq_true']
  constructor
  · rintro ⟨hagree, hcarry⟩
    rw [hadd, hcarry, prefixVal_congr hagree]
    simp
  · intro h
    -- the carry out is `0`: otherwise `A + B ≥ 2 ^ i > C`
    have hcarry : carryBit A B i = false := by
      have := prefixVal_lt C i
      cases hc : carryBit A B i
      · rfl
      · rw [hc] at hadd; simp at hadd; omega
    rw [hcarry] at hadd
    simp only [Bool.toNat_false, mul_zero, add_zero] at hadd
    exact ⟨prefixVal_inj (h.trans hadd), hcarry⟩

namespace RippleCarry

/-- The input bit at vertex `o + j`, as a function of `j`. -/
def inBits {n : ℕ} (x : Fin n → Bool) (o : ℕ) (j : ℕ) : Bool :=
  (List.ofFn x).getD (o + j) false

/-- On the input bits of a word `w`, `inBits` reads the letters of `w`. -/
theorem inBits_get (w : List Bool) (o j : ℕ) : inBits w.get o j = w.getD (o + j) false := by
  rw [inBits, List.ofFn_get]

/-- The invariant of the ripple-carry circuit: after the first `i ≤ k` bit positions
there are `n + 2 + 15 i` vertices, the carry vertex holds `carry i` and the accumulator
holds `agree i`, for `A`, `B`, `C` the three input blocks.

**Proof sketch.** Induction on `i`.  The two constant gates give `carry 0 = false` and
`agree 0 = true`.  Position `i` is a `bitBlock` appended at vertex `n + 2 + 15 i`; it
reads the input bits `i`, `k + i`, `2 k + i` (unchanged by running gates) and, by the
induction hypothesis, `carry i` and `agree i`, so `runWith_bitBlock` gives `carry (i + 1)`
at its vertex `8` and `agree (i + 1)` at its vertex `14`. -/
theorem adderGatesUpTo_spec {n : ℕ} (x : Fin n → Bool) {k : ℕ} (hk : 3 * k ≤ n) (i : ℕ)
    (hi : i ≤ k) :
    (runWith DAGGate.eval (adderGatesUpTo n k i) (List.ofFn x)).length = n + 2 + 15 * i ∧
    (runWith DAGGate.eval (adderGatesUpTo n k i) (List.ofFn x)).getD (cinIdx n i) false =
      carryBit (inBits x 0) (inBits x k) i ∧
    (runWith DAGGate.eval (adderGatesUpTo n k i) (List.ofFn x)).getD (accIdx n i) false =
      agreeBit (inBits x 0) (inBits x k) (inBits x (2 * k)) i := by
  induction i with
  | zero =>
    simp [adderGatesUpTo, runWith_cons, constGate, DAGGate.eval, cinIdx, accIdx, carryBit, agreeBit]
  | succ i ih =>
    obtain ⟨hlen, hcin, hacc⟩ := ih (by omega)
    rw [adderGatesUpTo, runWith_append]
    set vs := runWith DAGGate.eval (adderGatesUpTo n k i) (List.ofFn x) with hvs
    obtain ⟨l, h8, h14⟩ := runWith_bitBlock vs hlen (a := i) (b := k + i) (c := 2 * k + i)
      (by omega) (by omega) (by omega) (cinIdx_lt n i) (accIdx_lt n i)
    -- the block reads the input bits, which running gates never changes
    have hin : ∀ o, o + i < n → vs.getD (o + i) false = inBits x o i := fun o ho => by
      rw [hvs, runWith_getD_of_lt _ _ _ (by simpa using ho)]; rfl
    have hA := hin 0 (by omega)
    rw [Nat.zero_add] at hA
    refine ⟨by omega, ?_, ?_⟩
    · rw [show cinIdx n (i + 1) = n + 2 + 15 * i + 8 from rfl, h8, hA, hin k (by omega), hcin]
      rfl
    · rw [show accIdx n (i + 1) = n + 2 + 15 * i + 14 from rfl, h14, hA, hin k (by omega),
        hin (2 * k) (by omega), hcin, hacc]
      rfl

end RippleCarry

/-- The ripple-carry circuit outputs `agree k ∧ ¬carry k` on the three `k`-bit input
blocks, `k = ⌊n / 3⌋`. -/
theorem adderCircuit_eval {n : ℕ} (x : Fin n → Bool) :
    (adderCircuit n).eval x =
      (agreeBit (inBits x 0) (inBits x (n / 3)) (inBits x (2 * (n / 3))) (n / 3) &&
        !carryBit (inBits x 0) (inBits x (n / 3)) (n / 3)) := by
  obtain ⟨hlen, hcin, hacc⟩ := adderGatesUpTo_spec x (k := n / 3) (by omega) (n / 3) le_rfl
  have hacclt := accIdx_lt n (n / 3)
  simp only [DAGCircuit.eval, DAGCircuit.values, adderCircuit, adderGates]
  rw [runWith_append]
  set vs := runWith DAGGate.eval (adderGatesUpTo n (n / 3) (n / 3)) (List.ofFn x)
  rw [← hlen] at hacclt ⊢
  rw [show n + 15 * (n / 3) + 3 = vs.length + 1 by omega]
  simp only [runWith_cons, runWith_nil, DAGGate.eval]
  simp only [List.getD_eq_getElem?_getD] at hcin hacc
  simp [List.getElem?_append_left hacclt, hcin, hacc]

/-- The ripple-carry circuit is correct: on a word `a ++ b ++ c` of three equal-length
blocks it outputs `true` iff `val c = val a + val b`, the values read little-endian.
[AB09, Ex 6.3]

**Proof sketch.** With `k = |c|` the circuit reads blocks of width `⌊3k / 3⌋ = k`, and by
`adderCircuit_eval` and `agree_and_noCarry_iff` it accepts iff the `k`-bit values of the
blocks satisfy `C = A + B`.  The blocks at offsets `0`, `k`, `2k` of `a ++ b ++ c` are
`a`, `b`, `c` bit for bit, and `bitsVal` of a `k`-bit list is its `k`-bit value. -/
theorem adderCircuit_eval_append {a b c : List Bool} (ha : a.length = c.length)
    (hb : b.length = c.length) :
    (adderCircuit (a ++ b ++ c).length).eval (a ++ b ++ c).get = true ↔
      bitsVal c = bitsVal a + bitsVal b := by
  have hn : (a ++ b ++ c).length / 3 = c.length := by simp; omega
  rw [adderCircuit_eval, hn, agree_and_noCarry_iff, bitsVal_eq_prefixVal a,
    bitsVal_eq_prefixVal b, bitsVal_eq_prefixVal c, ha, hb]
  -- the three input blocks are `a`, `b` and `c`
  have hA : ∀ j < c.length, inBits (a ++ b ++ c).get 0 j = a.getD j false := fun j hj => by
    rw [inBits_get, List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by omega), Nat.zero_add]
  have hB : ∀ j < c.length, inBits (a ++ b ++ c).get c.length j = b.getD j false :=
    fun j hj => by
      rw [inBits_get, List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by omega)]
      congr 1; omega
  have hC : ∀ j < c.length, inBits (a ++ b ++ c).get (2 * c.length) j = c.getD j false :=
    fun j hj => by
      rw [inBits_get, List.getD_append_right _ _ _ _ (by simp; omega)]
      congr 1; simp; omega
  rw [prefixVal_congr hA, prefixVal_congr hB, prefixVal_congr hC]

end BoolCircuit
