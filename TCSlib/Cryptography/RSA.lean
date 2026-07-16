import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# TimeM: Time Complexity Monad

`TimeM T α` represents a computation that produces a value of type `α` and tracks its time cost.

`T` is usually instantiated as `ℕ` to count operations, but can be instantiated as `ℝ` to count
actual wall time, or as more complex types in order to model more general costs.

## Design Principles
1. **Pure inputs, timed outputs**: Functions take plain values and return `TimeM` results
2. **Time annotations are trusted**: The `time` field is NOT verified against actual cost.
   You must manually ensure annotations match the algorithm's complexity in your cost model.
3. **Separation of concerns**: Prove correctness properties on `.ret`, prove complexity on `.time`

## Cost Model
**Document your cost model explicitly.** Decide and be consistent about:
- **What costs 1 unit?** (comparison, arithmetic operation, etc.)
- **What is free?** (variable lookup, pattern matching, etc.)
- **Recursive calls:** Do you charge for the call itself?

## Notation
- **`✓`** : A tick of time, see `TimeM.tick`.
- **`⟪tm⟫`** : Extract the pure value from a `TimeM` computation (notation for `tm.ret`)

## References

See [Danielsson2008] for the discussion.
-/

/-- A monad for tracking time complexity of computations.
`TimeM T α` represents a computation that returns a value of type `α`
and accumulates a time cost (represented as a type `T`, typically `ℕ`). -/
@[ext]
structure TimeM (T : Type*) (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated time cost of the computation -/
  time : T

namespace TimeM

/-- Lifts a pure value into a `TimeM` computation with zero time cost.

Prefer to use `pure` instead of `TimeM.pure`. -/
protected def pure [Zero T] {α} (a : α) : TimeM T α :=
  ⟨a, 0⟩

instance [Zero T] : Pure (TimeM T) where
  pure := TimeM.pure

/-- Sequentially composes two `TimeM` computations, summing their time costs.

Prefer to use the `>>=` notation. -/
protected def bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) : TimeM T β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance [Add T] : Bind (TimeM T) where
  bind := TimeM.bind

instance : Functor (TimeM T) where
  map f x := ⟨f x.ret, x.time⟩

instance [Add T] : Seq (TimeM T) where
  seq f x := ⟨f.ret (x ()).ret, f.time + (x ()).time⟩

instance [Add T] : SeqLeft (TimeM T) where
  seqLeft x y := ⟨x.ret, x.time + (y ()).time⟩

instance [Add T] : SeqRight (TimeM T) where
  seqRight x y := ⟨(y ()).ret, x.time + (y ()).time⟩

instance [AddZero T] : Monad (TimeM T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

@[simp, grind =] theorem ret_pure {α} [Zero T] (a : α) : (pure a : TimeM T α).ret = a := rfl
@[simp, grind =] theorem ret_bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) :
    (m >>= f).ret = (f m.ret).ret := rfl
@[simp, grind =] theorem ret_map {α β} (f : α → β) (x : TimeM T α) : (f <$> x).ret = f x.ret := rfl
@[simp] theorem ret_seqRight {α} (x : TimeM T α) (y : Unit → TimeM T β) [Add T] :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl
@[simp] theorem ret_seqLeft {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqLeft.seqLeft x y).ret = x.ret := rfl
@[simp] theorem ret_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl

@[simp, grind =] theorem time_bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl
@[simp, grind =] theorem time_pure {α} [Zero T] (a : α) : (pure a : TimeM T α).time = 0 := rfl
@[simp, grind =] theorem time_map {α β} (f : α → β) (x : TimeM T α) : (f <$> x).time = x.time := rfl
@[simp] theorem time_seqRight {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqRight.seqRight x y).time = x.time + (y ()).time := rfl
@[simp] theorem time_seqLeft {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqLeft.seqLeft x y).time = x.time + (y ()).time := rfl
@[simp] theorem time_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).time = f.time + (x ()).time := rfl

/-- `TimeM` is lawful so long as addition in the cost is associative and absorbs zero. -/
instance [AddMonoid T] : LawfulMonad (TimeM T) := .mk'
  (id_map := fun x => rfl)
  (pure_bind := fun _ _ => by ext <;> simp)
  (bind_assoc := fun _ _ _ => by ext <;> simp [add_assoc])
  (seqLeft_eq := fun _ _ => by ext <;> simp)
  (bind_pure_comp := fun _ _ => by ext <;> simp)

/-- Creates a `TimeM` computation with a time cost. -/
def tick (c : T) : TimeM T PUnit := ⟨.unit, c⟩

@[simp, grind =] theorem ret_tick (c : T) : (tick c).ret = () := rfl
@[simp, grind =] theorem time_tick (c : T) : (tick c).time = c := rfl

/-- `✓[c] x` adds `c` ticks, then executes `x`. -/
macro "✓[" c:term "]" body:doElem : doElem => `(doElem| do TimeM.tick $c; $body:doElem)

/-- `✓ x` is a shorthand for `✓[1] x`, which adds one tick and executes `x`. -/
macro "✓" body:doElem : doElem => `(doElem| ✓[1] $body)

/-- Notation for extracting the return value from a `TimeM` computation: `⟪tm⟫` -/
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

end TimeM

open TimeM

/-!
# Algorithm Verification Examples

Small worked examples of using `TimeM` to track comparison counts alongside functional
correctness: computing a max/median, and insertion sort.
-/

section AlgorithmExamples

variable {α : Type} [LinearOrder α]

/-- Larger of two naturals, counting one comparison. -/
def max2 (x y : ℕ) : TimeM ℕ ℕ := do
  ✓
  if x ≤ y then
    return y
  else
    return x

/-- Median of three values, counting comparisons. -/
def median3 (a b c : α) : TimeM ℕ α := do
  ✓
  if a ≤ b then
    ✓
    if b ≤ c then
      return b
    else
      ✓
      if a ≤ c then
        return c
      else
        return a
  else
    ✓
    if a ≤ c then
      return a
    else
      ✓
      if b ≤ c then
        return c
      else
        return b

/-- `x` is a median of `a, b, c` if it lies between at least one pair of the other two. -/
def isMedian (x a b c : α) : Prop :=
  (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a) ∨
  (a ≤ x ∧ x ≤ c) ∨ (c ≤ x ∧ x ≤ a) ∨
  (b ≤ x ∧ x ≤ c) ∨ (c ≤ x ∧ x ≤ b)

theorem median3_correct (a b c : α) :
  isMedian (⟪median3 a b c⟫) a b c := by
  simp [median3, isMedian]
  by_cases h1 : a ≤ b
  · by_cases h2 : b ≤ c
    · simp [h1, h2]
    · by_cases h3 : a ≤ c
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]
  · by_cases h2 : a ≤ c
    · simp [h1, h2]
    · by_cases h3 : b ≤ c
      · simp [h1, h2, h3]
      · have hba : b ≤ a := le_of_not_ge h1
        have hcb : c ≤ b := le_of_not_ge h3
        simp [h1, h2, h3, hba, hcb]

theorem median3_time (a b c : α) :
  (median3 a b c).time ≤ 3 := by
  by_cases h1 : a ≤ b
  · by_cases h2 : b ≤ c
    · simp [median3, h1, h2]
    · by_cases h3 : a ≤ c
      · simp [median3, h1, h2, h3]
      · simp [median3, h1, h2, h3]
  · by_cases h2 : a ≤ c
    · simp [median3, h1, h2]
    · by_cases h3 : b ≤ c
      · simp [median3, h1, h2, h3]
      · simp [median3, h1, h2, h3]

/-!
## Insertion Sort

Cost model:
* one unit of time per comparison `x ≤ y`
* pattern matching / `return` / consing are free
* recursive calls themselves are not charged extra
-/

open List

/-- Insert `x` into an already-sorted list, counting comparisons. -/
def insert (x : α) : List α → TimeM ℕ (List α)
  | [] =>
      return [x]
  | y :: ys => do
      ✓
      if x ≤ y then
        return x :: y :: ys
      else
        let rest ← insert x ys
        return y :: rest

/-- Insertion sort, counting the comparisons performed by each insert step. -/
def insertionSort : List α → TimeM ℕ (List α)
  | [] =>
      return []
  | x :: xs => do
      let ys ← insertionSort xs
      insert x ys

section Correctness

abbrev IsSorted : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x ≤ y ∧ IsSorted (y :: rest)

/-- `IsSorted` is the same notion as `List.Sorted (· ≤ ·)`: both only require
adjacent elements to be ordered, which for a linear (transitive) order is
equivalent to full pairwise ordering. -/
theorem isSorted_iff_isChain (xs : List α) : IsSorted xs ↔ List.IsChain (· ≤ ·) xs := by
  induction xs with
  | nil => simp [IsSorted]
  | cons x xs ih =>
    cases xs with
    | nil => simp [IsSorted]
    | cons y ys =>
        simp only [IsSorted]
        constructor
        · rintro ⟨hxy, hrest⟩
          exact List.IsChain.cons_cons hxy (ih.mp hrest)
        · intro h
          cases h with
          | cons_cons hxy hrest => exact ⟨hxy, ih.mpr hrest⟩

theorem isSorted_iff_sorted (xs : List α) : IsSorted xs ↔ List.Sorted (· ≤ ·) xs :=
  (isSorted_iff_isChain xs).trans List.isChain_iff_pairwise

@[simp] theorem ret_insert (x : α) (xs : List α) :
    ⟪insert x xs⟫ = List.orderedInsert (· ≤ ·) x xs := by
  induction xs with
  | nil =>
      simp [_root_.insert]
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · simp [_root_.insert, hxy]
      · simp [_root_.insert, hxy, ih]

@[simp] theorem ret_insertionSort (xs : List α) :
    ⟪insertionSort xs⟫ = List.insertionSort (· ≤ ·) xs := by
  induction xs with
  | nil =>
      simp [_root_.insertionSort]
  | cons x xs ih =>
      simp [_root_.insertionSort, ih, List.insertionSort_cons, ret_insert]

@[simp] theorem length_ret_insert (x : α) (xs : List α) :
    ⟪insert x xs⟫.length = xs.length + 1 := by
  simpa [ret_insert] using (List.orderedInsert_length (r := (· ≤ ·)) xs x)

@[simp] theorem length_ret_insertionSort (xs : List α) :
    ⟪insertionSort xs⟫.length = xs.length := by
  simp [ret_insertionSort, List.length_insertionSort]

/-- The timed `insert` returns the usual pure ordered insert. -/
theorem insert_perm (x : α) (xs : List α) :
    ⟪insert x xs⟫ ~ x :: xs := by
  simpa [ret_insert] using (List.perm_orderedInsert (r := (· ≤ ·)) x xs)

/-- If the input is sorted, then the output of `insert` is sorted. -/
theorem insert_sorted (x : α) (xs : List α) (hxs : IsSorted xs) :
    IsSorted ⟪insert x xs⟫ := by
  rw [isSorted_iff_sorted, ret_insert]
  exact List.Sorted.orderedInsert (r := (· ≤ ·)) x xs ((isSorted_iff_sorted xs).1 hxs)

/-- The timed insertion sort permutes the input. -/
theorem insertionSort_perm (xs : List α) :
    ⟪insertionSort xs⟫ ~ xs := by
  simpa [ret_insertionSort] using (List.perm_insertionSort (r := (· ≤ ·)) xs)

/-- The timed insertion sort returns a sorted list. -/
theorem insertionSort_sorted (xs : List α) :
    IsSorted ⟪insertionSort xs⟫ := by
  rw [isSorted_iff_sorted, ret_insertionSort]
  exact List.sorted_insertionSort (r := (· ≤ ·)) xs

/-- Functional correctness of insertion sort. -/
theorem insertionSort_correct (xs : List α) :
    IsSorted ⟪insertionSort xs⟫ ∧ ⟪insertionSort xs⟫ ~ xs :=
  ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

end Correctness

section TimeComplexity

/-- Worst-case recurrence for insertion sort: `T(0)=0`, `T(n+1)=T(n)+n`. -/
def timeInsertionSortRec : Nat → Nat
  | 0 => 0
  | n + 1 => timeInsertionSortRec n + n

/-- Inserting into a list of length `n` uses at most `n` comparisons. -/
theorem time_insert_le (x : α) (xs : List α) :
    (_root_.insert x xs).time ≤ xs.length := by
  induction xs with
  | nil => simp [_root_.insert]
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · simp [_root_.insert, hxy]
      · simp [_root_.insert, hxy]
        omega

/-- The running time of insertion sort is bounded by the standard recurrence. -/
theorem time_insertionSort_le_rec (xs : List α) :
    (insertionSort xs).time ≤ timeInsertionSortRec xs.length := by
  induction xs with
  | nil =>
      simp [_root_.insertionSort, timeInsertionSortRec]
  | cons x xs ih =>
      simp [_root_.insertionSort, timeInsertionSortRec]
      have hins : (_root_.insert x ⟪insertionSort xs⟫).time ≤ xs.length := by
        simpa using time_insert_le (x := x) (xs := ⟪insertionSort xs⟫)
      rw [ret_insertionSort] at hins
      exact Nat.add_le_add ih hins

/-- A clean quadratic upper bound for the recurrence. -/
theorem timeInsertionSortRec_le_sq (n : Nat) :
    timeInsertionSortRec n ≤ n * n := by
  induction n with
  | zero => simp [timeInsertionSortRec]
  | succ n ih =>
      simp only [timeInsertionSortRec]
      nlinarith

/-- Hence insertion sort performs at most `n^2` comparisons on a list of length `n`. -/
theorem time_insertionSort_le_sq (xs : List α) :
    (insertionSort xs).time ≤ xs.length * xs.length :=
  le_trans (time_insertionSort_le_rec xs) (timeInsertionSortRec_le_sq xs.length)

end TimeComplexity

end AlgorithmExamples

/-!
# RSA Algorithm Correctness

This section formalizes the RSA cryptosystem.
For distinct primes `p` and `q`, and public/private exponents `e` and `d`
such that `e * d ≡ 1 [MOD (p - 1) * (q - 1)]`, the decryption of an
encrypted message `m` recovers `m` modulo `p * q`.

The proof proceeds in three steps:
1. `rsa_core`: Fermat's Little Theorem in `ZMod p` via induction on the exponent
2. `rsa_zmod_p` / `rsa_zmod_q`: lift the core lemma to both prime factors
3. `rsa_crt`: combine via the Chinese Remainder Theorem isomorphism
-/

namespace RSA

open Nat

/--
  Core algebraic lemma for RSA:
  In the finite field `ZMod p` (where `p` is prime), `x ^ (1 + c * (p - 1)) = x`.
  We prove this by induction on `c` to avoid separate handling of `x = 0`.
-/
lemma rsa_core (p : ℕ) [hp : Fact p.Prime] (c : ℕ) (x : ZMod p) :
    x ^ (1 + c * (p - 1)) = x := by
  induction c with
  | zero => simp
  | succ c ih =>
      have hexp : 1 + (c + 1) * (p - 1) = (1 + c * (p - 1)) + (p - 1) := by ring
      rw [hexp, pow_add, ih, ZMod.pow_card_sub_one]
      by_cases hx : x = 0 <;> simp [hx]

/-- If `ed = 1 + c*(p-1)`, then `m^ed = m` in `ZMod p`. -/
lemma rsa_zmod_of_factor (p : ℕ) [Fact p.Prime]
    (m ed c : ℕ) (h : ed = 1 + c * (p - 1)) :
    ((m ^ ed : ℕ) : ZMod p) = (m : ZMod p) := by
  -- prove the cleaner ZMod-power statement…
  have hpow : ((m : ZMod p) ^ ed) = (m : ZMod p) := by
    -- rewrite the exponent into the form used by `rsa_core`
    -- and then just apply it
    simpa [h] using (rsa_core p c (m : ZMod p))
  -- …then convert back to the casted-Nat-power statement
  simpa [Nat.cast_pow] using hpow

/--
  Applies the above helper lemma to the RSA exponent factorization modulo `p`.
-/
lemma rsa_zmod_p {p q m e d k : ℕ} [Fact p.Prime]
    (h_ed : e * d = 1 + k * (p - 1) * (q - 1)) :
    ((m ^ (e * d) : ℕ) : ZMod p) = (m : ZMod p) := by
  -- Put the RHS into the form `1 + (something)*(p-1)`
  have h' : e * d = 1 + (k * (q - 1)) * (p - 1) := by
    calc
      e * d = 1 + k * (p - 1) * (q - 1) := h_ed
      _ = 1 + k * (q - 1) * (p - 1) := by
        -- swaps the last two factors in `k*(p-1)*(q-1)`
        simp [Nat.mul_right_comm, Nat.mul_assoc]
  -- Now apply the generic lemma
  exact rsa_zmod_of_factor p m (e * d) (k * (q - 1)) h'

/-- Applies the above helper lemma to the RSA exponent factorization modulo `q`. -/
lemma rsa_zmod_q {p q m e d k : ℕ} [Fact q.Prime]
    (h_ed : e * d = 1 + k * (p - 1) * (q - 1)) :
    ((m ^ (e * d) : ℕ) : ZMod q) = (m : ZMod q) := by
  -- This is already of the form `1 + (k*(p-1))*(q-1)`
  exact rsa_zmod_of_factor q m (e * d) (k * (p - 1)) h_ed

/--
  Lifts the equivalences from `ZMod p` and `ZMod q` up to `ZMod (p * q)`
  using the Chinese Remainder Theorem isomorphism.
-/
lemma rsa_crt {p q m ed : ℕ} (hpq : p.Coprime q)
    (hp : ((m ^ ed : ℕ) : ZMod p) = (m : ZMod p))
    (hq : ((m ^ ed : ℕ) : ZMod q) = (m : ZMod q)) :
    ((m ^ ed : ℕ) : ZMod (p * q)) = (m : ZMod (p * q)) := by
  apply (ZMod.chineseRemainder hpq).injective
  -- push nat-casts through the ring equivalence
  simp only [map_natCast]
  -- equality in the product reduces to the two components
  ext <;> assumption

lemma rsa_crt_pow {p q m ed : ℕ} (hpq : p.Coprime q)
    (hp : ((m : ZMod p) ^ ed) = (m : ZMod p))
    (hq : ((m : ZMod q) ^ ed) = (m : ZMod q)) :
    ((m : ZMod (p * q)) ^ ed) = (m : ZMod (p * q)) := by
  -- convert hp/hq into the "casted Nat power" shape and reuse `rsa_crt`
  have hp' : ((m ^ ed : ℕ) : ZMod p) = (m : ZMod p) := by
    simpa [Nat.cast_pow] using hp
  have hq' : ((m ^ ed : ℕ) : ZMod q) = (m : ZMod q) := by
    simpa [Nat.cast_pow] using hq
  have h' : ((m ^ ed : ℕ) : ZMod (p * q)) = (m : ZMod (p * q)) :=
    rsa_crt hpq hp' hq'
  simpa [Nat.cast_pow] using h'

/-- Public key: modulus and public exponent. -/
structure PublicKey where
  n : ℕ
  e : ℕ

/--
Secret key: stores `p,q` (or enough to recover them), private exponent `d`,
and proofs tying it all to the public key.
-/
structure SecretKey where
  pub : PublicKey
  p   : ℕ
  q   : ℕ
  d   : ℕ
  k   : ℕ
  hp  : p.Prime
  hq  : q.Prime
  hpq_neq : p ≠ q
  hn  : pub.n = p * q
  h_ed : pub.e * d = 1 + k * (p - 1) * (q - 1)

/-- Encryption uses only the public key. -/
def encrypt (pub : PublicKey) (m : ℕ) : ZMod pub.n :=
  (m : ZMod pub.n) ^ pub.e

/-- Decryption uses the secret key (and ciphertext is modulo the public modulus). -/
def decrypt (sec : SecretKey) (c : ZMod sec.pub.n) : ZMod sec.pub.n :=
  c ^ sec.d

theorem rsa_correctness (sec : SecretKey) (m : ℕ) :
    decrypt sec (encrypt sec.pub m) = (m : ZMod sec.pub.n) := by
  dsimp [decrypt, encrypt]

  -- (m^e)^d = m^(e*d)
  rw [← pow_mul]

  -- Rewrite modulus to p*q immediately
  rw [sec.hn]

  -- provide Fact instances
  haveI : Fact sec.p.Prime := ⟨sec.hp⟩
  haveI : Fact sec.q.Prime := ⟨sec.hq⟩

  -- mod p
  have hp_eq :=
    rsa_zmod_p (m := m) sec.h_ed

  -- mod q
  have hq_eq :=
    rsa_zmod_q (m := m) sec.h_ed

  -- p and q are coprime
  have hpq_coprime : sec.p.Coprime sec.q := by
    apply (Nat.Prime.coprime_iff_not_dvd sec.hp).2
    intro h_dvd
    rcases sec.hq.eq_one_or_self_of_dvd sec.p h_dvd with h | h
    · exact sec.hp.ne_one h
    · exact sec.hpq_neq h

  have hp_eq' := hp_eq
  have hq_eq' := hq_eq
  push_cast at hp_eq'
  push_cast at hq_eq'
  -- now hp_eq' : (m : ZMod sec.p) ^ ed = (m : ZMod sec.p)
  -- and  hq_eq' : (m : ZMod sec.q) ^ ed = (m : ZMod sec.q)

  exact rsa_crt_pow hpq_coprime hp_eq' hq_eq'
  -- Lift via CRT

end RSA
