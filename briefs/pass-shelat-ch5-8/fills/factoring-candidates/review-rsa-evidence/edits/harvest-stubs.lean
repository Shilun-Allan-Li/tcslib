/-! REVIEW STUBS (delivery review rsa, conditional edit E4): the shared lemmas proposed for the
harvest PR, each at its proposed home, with the proofs moved from the `rsa_`/`dla_` copies. In the
harvest PR they live in the files named; here they only check that `RSA.lean` cites them. -/

namespace Complexity

/-- (`ClassNP/PolyTime.lean`) Composition in applied form, `x ↦ g (f x)` (no `Function.comp`
for unification to unfold). -/
theorem PolyTimeComputable.comp' {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x) :=
  hg.comp hf

/-- (`ClassNP/PolyTime.lean`) Polynomial time transfers along pointwise equality. -/
theorem PolyTimeComputable.congr {f g : List Bool → List Bool} (h : PolyTimeComputable f)
    (e : ∀ x, f x = g x) : PolyTimeComputable g := by
  rw [show g = f from (funext e).symm]
  exact h

/-- (`Randomized/Build/IterateFind.lean`) A search over `[0, L)` whose test also demands
`i < N` is the search over `[0, N)`, for `N ≤ L`. -/
theorem IterateFind.find?_range_and_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
  have hcongr : ∀ l : List ℕ, (∀ i ∈ l, i < N) →
      l.find? (fun i => decide (i < N) && p i) = l.find? p := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      rw [List.find?_cons, List.find?_cons, ih (fun i hi => hl i (List.mem_cons_of_mem a hi)),
        decide_eq_true (hl a List.mem_cons_self), Bool.true_and]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
  rw [List.range_add, List.find?_append, hcongr _ (fun i hi => List.mem_range.1 hi)]
  have hnone : (List.map (fun x => N + x) (List.range d)).find?
      (fun i => decide (i < N) && p i) = none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    simp
  rw [hnone, Option.or_none]

end Complexity

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory

/-- (`Candidates/Arithmetic.lean`) The empty numeral reads as `0`. -/
theorem listToNat_nil : listToNat [] = 0 := by
  rw [listToNat_eq]
  rfl

/-- (`Candidates/Arithmetic.lean`) The numeral `[true]` reads as `1`. -/
theorem listToNat_singleton_true : listToNat [true] = 1 := by
  rw [listToNat_eq]
  rfl

/-- (`Candidates/Arithmetic.lean`) `⟦a ++ b⟧ = ⟦a⟧ · 2^{|b|} + ⟦b⟧` (most significant bit first;
the private `foldl_bits_eq` of `Asymptotic/Sampling.lean`). -/
theorem listToNat_append (a b : List Bool) :
    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b := by
  have key : ∀ (l : List Bool) (acc : ℕ),
      l.foldl (fun a c => 2 * a + if c = true then 1 else 0) acc =
        acc * 2 ^ l.length + l.foldl (fun a c => 2 * a + if c = true then 1 else 0) 0 := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons c l ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, ih (2 * 0 + _), List.length_cons, pow_succ]
      ring
  rw [listToNat_eq, listToNat_eq, listToNat_eq, List.foldl_append, key]

/-- (`Candidates/Arithmetic.lean`) The all-ones numeral `1^k` reads as `2^k − 1`. -/
theorem listToNat_replicate_true (k : ℕ) : listToNat (List.replicate k true) = 2 ^ k - 1 := by
  induction k with
  | zero => rw [List.replicate_zero, listToNat_nil]; rfl
  | succ k ih =>
    rw [List.replicate_succ', listToNat_eq, List.foldl_append, ← listToNat_eq, ih]
    have := Nat.one_le_two_pow (n := k)
    simp only [List.foldl_cons, List.foldl_nil, if_true, pow_succ]
    omega

/-- (`Candidates/Arithmetic.lean`) Leading zeros do not change the number read. -/
theorem listToNat_natToList_zero_append (k : ℕ) (w : List Bool) :
    listToNat (natToList k 0 ++ w) = listToNat w := by
  rw [listToNat_append, listToNat_natToList (Nat.two_pow_pos k), zero_mul, zero_add]

/-- (`Candidates/Arithmetic.lean`) **Width normalization by truncation**:
`(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W`, the low `W` bits. -/
theorem natToList_zero_append_drop (W : ℕ) (b : List Bool) :
    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b) := by
  set w := natToList W 0 ++ b with hw
  have hlen : (w.drop b.length).length = W := by
    rw [List.length_drop, hw, List.length_append, length_natToList]
    omega
  have hval : listToNat w = listToNat b := listToNat_natToList_zero_append W b
  have hsplit : listToNat w = listToNat (w.take b.length) * 2 ^ W + listToNat (w.drop b.length) := by
    conv_lhs => rw [← List.take_append_drop b.length w]
    rw [listToNat_append, hlen]
  have hlt := listToNat_lt_two_pow (w.drop b.length)
  rw [hlen] at hlt
  have hmod : listToNat b % 2 ^ W = listToNat (w.drop b.length) := by
    rw [← hval, hsplit, Nat.mul_add_mod_of_lt hlt]
  have hnum : ∀ N : ℕ, natToList W N = natToList W (N % 2 ^ W) := fun N => by
    have h := natToList_length_listToNat (natToList W N)
    rw [length_natToList, listToNat_natToList_eq_mod] at h
    exact h.symm
  rw [hnum, hmod, ← hlen, natToList_length_listToNat]

/-- (`Candidates/Arithmetic.lean`) `subStr ⟨a, a⟩` is the `|a|`-bit numeral of `0`. -/
theorem subStr_self (a : List Bool) : subStr (pairEncode a a) = natToList a.length 0 := by
  rw [subStr_pairEncode, Nat.sub_self]

/-- (`Candidates/Arithmetic.lean`) The product numeral reads as the product. -/
theorem listToNat_mulStr (a b : List Bool) :
    listToNat (mulStr (pairEncode a b)) = listToNat a * listToNat b := by
  rw [mulStr_pairEncode, listToNat_natToList]
  rw [pow_add]
  exact Nat.mul_lt_mul'' (listToNat_lt_two_pow a) (listToNat_lt_two_pow b)

/-- (`Candidates/Concrete.lean`, beside `rejectBlocksL_eq`) Block rejection sampling as a search
followed by the read value: the first accepted trial `t < T`, mapped to its value. -/
theorem rejectBlocksL_eq_find? (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r =
      ((List.range T).find? fun t => decide (E (listToNat ((r.drop (t * B)).take k)))).map
        fun t => listToNat ((r.drop (t * B)).take k) := by
  rw [rejectBlocksL_eq, ← List.findSome?_guard, List.map_findSome?]
  congr 1
  funext t
  by_cases ht : E (listToNat ((r.drop (t * B)).take k)) <;> simp [Option.guard, ht]

end TCSlib.Cryptography.Candidates
