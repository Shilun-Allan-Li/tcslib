/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract-register-machine fragments for the codec checkers

Bounded loops of abstract register machines (`Complexity.LogProg.ARM`) used by the logspace
checkers of the configuration codec, stated like the shared fragments of
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess` (`registerCopy_loop`,
`registerScale_loop`, …): over any machine whose instructions at the given labels have the
given shape, as runs `Complexity.LogProg.AReach` through configurations meeting the syntactic
preconditions with all registers bounded by `B`.

* `Complexity.Codec.incChain`, `Complexity.Codec.decChain` — straight chains of increments
  and decrements of one register.
* `Complexity.Codec.scan_loop` — **the scan engine**: walk two pointers through the input in
  lockstep (any stride), read the input bit under each through a bit oracle, and feed the
  pair of bits to a finite-state step; the run ends in the label of the fold of the step
  over the zipped words read.
* `Complexity.Codec.decodeStride_loop` — decode a binary field laid out at any stride
  (most significant letter last), `boundedDecodeStride_loop`.
* `Complexity.Codec.halvCount_loop` — count the binary digits of a register by halving.
* `Complexity.Codec.le_loop` — compare two registers by counting.

Logspace machine infrastructure ([AB09, §4.1: logspace algorithms keep a constant number of
`O(log n)`-bit counters]); not a result of [AB09].

The chains and the stride decoder are those of
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess`: `incChain` and `decChain` are the two
directions of `Complexity.LogProg.arm_chain`, and `decodeStride_loop` is
`Complexity.LogProg.boundedDecodeStride_loop` (the codec's fields are doubled in the virtual
input, so it reads at stride two), all stated here through the guard `GuardLe`.

## Main definitions

* none (run theorems for bounded loops of `Complexity.LogProg.ARM`).

## Main results

* `Complexity.Codec.incChain`, `Complexity.Codec.decChain`.
* `Complexity.Codec.scan_loop`, `Complexity.Codec.decodeStride_loop`,
  `Complexity.Codec.halvCount_loop`, `Complexity.Codec.le_loop`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {m d : ℕ} {Λ : Type}

/-- **A chain of increments** of register `r` along the labels `labels 0, …, labels k`.

**Proof sketch.** `Complexity.LogProg.arm_chain` with `up = true`. -/
theorem incChain (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (y : List Bool)
    (r : Fin m) (labels : ℕ → Λ) (k B : ℕ)
    (hcode : ∀ i < k, A (labels i) = .inc r (labels (i + 1)))
    (v : Fin m → ℕ) (hv : ∀ s, v s ≤ B) (hk : v r + k ≤ B) :
    AReach A oracle y (GuardLe A y B) (some (labels 0), v, none)
      (some (labels k), Function.update v r (v r + k), none) :=
  arm_chain A oracle y r true labels k B hcode v hv hk

/-- **A chain of decrements** of register `r` along the labels `labels 0, …, labels k`
(with `k ≤ v r`, so no decrement truncates).

**Proof sketch.** `Complexity.LogProg.arm_chain` with `up = false`. -/
theorem decChain (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (y : List Bool)
    (r : Fin m) (labels : ℕ → Λ) (k B : ℕ)
    (hcode : ∀ i < k, A (labels i) = .dec r (labels (i + 1)))
    (v : Fin m → ℕ) (hv : ∀ s, v s ≤ B) (hk : k ≤ v r) :
    AReach A oracle y (GuardLe A y B) (some (labels 0), v, none)
      (some (labels k), Function.update v r (v r - k), none) :=
  arm_chain A oracle y r false labels k B hcode v hv hk

/-- **The scan engine.** Two pointer registers `p`, `q` walk in lockstep with stride
`stride` until `p` reaches `lim`; at each position the bits `u_i`, `u'_i` under the pointers
are read through the oracle `j` and the finite-state step `δ` consumes the pair. The run from
`test st₀` ends in `done` of the fold of `δ` over the zipped words, with both pointers
advanced by `stride · |u|`.

**Proof sketch.** Induction on `u` (with `u'` of the same length). If `p = lim` the run
exits; otherwise the two reads take the bits `u_0`, `u'_0`, the step applies `δ`, and two
increment chains (`incChain`) advance the pointers to the rest of the words. Pointer values
stay below `lim` (for `p`) and the supplied bound (for `q`). -/
theorem scan_loop {σ : Type} (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (y : List Bool) (p q lim : Fin m) (hpq : p ≠ q) (hpl : p ≠ lim) (hql : q ≠ lim) (j : Fin d)
    (δ : σ → Bool × Bool → σ) (test rd1 : σ → Λ) (rd2 : σ → Bool → Λ) (adv1 adv2 : σ → ℕ → Λ)
    (done : σ → Λ) (stride : ℕ) (hs : 0 < stride)
    (htest : ∀ st, A (test st) = .jeq p lim (done st) (rd1 st))
    (hrd1 : ∀ st, A (rd1 st) = .call j .whole [p] (rd2 st true) (rd2 st false))
    (hrd2 : ∀ st b, A (rd2 st b) =
      .call j .whole [q] (adv1 (δ st (b, true)) 0) (adv1 (δ st (b, false)) 0))
    (hadv1 : ∀ st i, i < stride → A (adv1 st i) = .inc p (adv1 st (i + 1)))
    (hend1 : ∀ st, adv1 st stride = adv2 st 0)
    (hadv2 : ∀ st i, i < stride → A (adv2 st i) = .inc q (adv2 st (i + 1)))
    (hend2 : ∀ st, adv2 st stride = test st)
    (B : ℕ) (u u' : List Bool) (hlen : u'.length = u.length) (st₀ : σ) (v : Fin m → ℕ)
    (hv : ∀ r, v r ≤ B) (hlim : v lim = v p + stride * u.length)
    (hq : v q + stride * u.length ≤ B)
    (ho1 : ∀ i < u.length, oracle j (pairEncode y (Nat.bits (v p + stride * i))) = u.getD i false)
    (ho2 : ∀ i < u.length, oracle j (pairEncode y (Nat.bits (v q + stride * i))) =
      u'.getD i false) :
    AReach A oracle y (GuardLe A y B) (some (test st₀), v, none)
      (some (done ((List.zip u u').foldl δ st₀)),
        Function.update (Function.update v p (v p + stride * u.length)) q
          (v q + stride * u.length), none) := by
  induction u generalizing u' st₀ v with
  | nil =>
    have e : v p = v lim := by simpa using hlim.symm
    have hu' : u' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hu'
    simp only [List.zip_nil_left, List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.add_zero,
      Function.update_eq_self]
    simpa [astep, htest, e] using
      (AReach.single (A := A) (oracle := oracle) (x := y) (G := GuardLe A y B)
        (a := (some (test st₀), v, none)) ⟨by simp [PreS, htest, hpl], hv⟩)
  | cons b u ih =>
    obtain ⟨b', u'', rfl⟩ : ∃ b' u'', u' = b' :: u'' := by
      cases u' with
      | nil => simp at hlen
      | cons b' u'' => exact ⟨b', u'', rfl⟩
    simp only [List.length_cons] at hlen hlim hq
    have hstep : stride ≤ stride * (u.length + 1) :=
      Nat.le_mul_of_pos_right stride (by omega)
    have hne : v p ≠ v lim := by omega
    have hb := ho1 0 (by simp)
    have hb' := ho2 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at hb hb'
    set st₁ := δ st₀ (b, b') with hst₁
    -- the test and the two reads
    have reads : AReach A oracle y (GuardLe A y B) (some (test st₀), v, none)
        (some (adv1 st₁ 0), v, none) := by
      apply AReach.step ⟨by simp [PreS, htest, hpl], hv⟩
      simp only [astep, htest, if_neg hne]
      apply AReach.step ⟨by simp [PreS, hrd1], hv⟩
      simp only [astep, hrd1, vword_whole₁, hb]
      have e1 : (if b = true then rd2 st₀ true else rd2 st₀ false) = rd2 st₀ b := by
        cases b <;> rfl
      rw [e1]
      apply AReach.step ⟨by simp [PreS, hrd2], hv⟩
      simp only [astep, hrd2, vword_whole₁, hb']
      have e2 : (if b' = true then adv1 (δ st₀ (b, true)) 0 else adv1 (δ st₀ (b, false)) 0) =
          adv1 st₁ 0 := by cases b' <;> rfl
      rw [e2]
      exact AReach.refl _
    -- the two increment chains
    set v₁ := Function.update v p (v p + stride) with hv₁
    set v₂ := Function.update v₁ q (v q + stride) with hv₂
    have bd₁ : ∀ r, v₁ r ≤ B := register_update_le v p B _ hv (by have := hv lim; omega)
    have bd₂ : ∀ r, v₂ r ≤ B := register_update_le v₁ q B _ bd₁ (by omega)
    have c1 := incChain A oracle y p (adv1 st₁) stride B (hadv1 st₁) v hv
      (by have := hv lim; omega)
    rw [hend1] at c1
    have c2 := incChain A oracle y q (adv2 st₁) stride B (hadv2 st₁) v₁ bd₁
      (by rw [hv₁, Function.update_of_ne hpq.symm]; omega)
    rw [hend2, hv₁, Function.update_of_ne hpq.symm] at c2
    -- the rest of the words
    have v₂p : v₂ p = v p + stride := by
      rw [hv₂, Function.update_of_ne hpq, hv₁, Function.update_self]
    have v₂q : v₂ q = v q + stride := by rw [hv₂, Function.update_self]
    have v₂l : v₂ lim = v lim := by
      rw [hv₂, Function.update_of_ne hql.symm, hv₁, Function.update_of_ne hpl.symm]
    have rest := ih u'' (by simpa using hlen) st₁ v₂ bd₂
      (by rw [v₂l, v₂p, hlim]; ring)
      (by rw [v₂q]; rw [Nat.mul_add, Nat.mul_one] at hq; omega)
      (fun i hi => by
        have := ho1 (i + 1) (by simp; omega)
        rw [v₂p, show v p + stride + stride * i = v p + stride * (i + 1) by ring, this]
        rfl)
      (fun i hi => by
        have := ho2 (i + 1) (by simp; omega)
        rw [v₂q, show v q + stride + stride * i = v q + stride * (i + 1) by ring, this]
        rfl)
    have fin : Function.update (Function.update v₂ p (v₂ p + stride * u.length)) q
        (v₂ q + stride * u.length) =
        Function.update (Function.update v p (v p + stride * (u.length + 1))) q
          (v q + stride * (u.length + 1)) := by
      rw [v₂p, v₂q]
      funext r
      by_cases hrq : r = q
      · subst hrq; simp only [Function.update_self]; ring
      · by_cases hrp : r = p
        · subst hrp
          simp only [Function.update_of_ne hrq, Function.update_self]; ring
        · simp [Function.update_of_ne hrq, Function.update_of_ne hrp, hv₂, hv₁]
    rw [fin] at rest
    simp only [List.zip_cons_cons, List.foldl_cons, List.length_cons]
    exact reads.trans (c1.trans (c2.trans rest))

/-- **A strided reverse scan decodes a bounded binary field** laid out at positions
`base + stride · i` (least significant letter first): from the pointer at
`base + stride · k`, with the suffix value from letter `k` in the accumulator, the run
reaches `done` with the value of the whole field.

**Proof sketch.** The stride decoder `Complexity.LogProg.boundedDecodeStride_loop` of
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess`, whose guard is `GuardLe`. -/
theorem decodeStride_loop (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (y : List Bool) (ptr base acc tmp : Fin m)
    (hpb : ptr ≠ base) (hpa : ptr ≠ acc) (hpt : ptr ≠ tmp)
    (hba : base ≠ acc) (hbt : base ≠ tmp) (hat : acc ≠ tmp)
    (j : Fin d) (test read done : Λ) (downs : ℕ → Λ)
    (copy bump clear scale take add : Bool → Λ) (incs : Bool → ℕ → Λ) (stride : ℕ)
    (htest : A test = .jeq ptr base done (downs 0))
    (hdowns : ∀ i < stride, A (downs i) = .dec ptr (downs (i + 1)))
    (hdend : downs stride = read)
    (hread : A read = .call j .whole [ptr] (copy true) (copy false))
    (hcopy : ∀ b, A (copy b) = .jeq tmp acc (clear b) (bump b))
    (hbump : ∀ b, A (bump b) = .inc tmp (copy b))
    (hclear : ∀ b, A (clear b) = .clr acc (scale b))
    (hscale : ∀ b, A (scale b) = .jz tmp (add b) (take b))
    (htake : ∀ b, A (take b) = .dec tmp (incs b 0))
    (hincs : ∀ b i, i < 2 → A (incs b i) = .inc acc (incs b (i + 1)))
    (hend : ∀ b, incs b 2 = scale b)
    (hadd : ∀ b, A (add b) = if b then .inc acc test else .jz tmp test test)
    (w : List Bool) (B : ℕ) (values : ∀ i ≤ w.length, bitsVal (w.drop i) ≤ B)
    (k : ℕ) (hk : k ≤ w.length) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hs : 0 < stride)
    (hp : v ptr = v base + stride * k) (ha : v acc = bitsVal (w.drop k)) (ht : v tmp = 0)
    (ho : ∀ i < w.length,
      oracle j (pairEncode y (Nat.bits (v base + stride * i))) = w.getD i false) :
    ∃ v', (∀ r, v' r ≤ B) ∧ v' ptr = v base ∧ v' acc = bitsVal w ∧ v' tmp = 0 ∧
      (∀ r, r ≠ ptr → r ≠ acc → r ≠ tmp → v' r = v r) ∧
      AReach A oracle y (GuardLe A y B) (some test, v, none) (some done, v', none) :=
  boundedDecodeStride_loop A oracle y ptr base acc tmp hpb hpa hpt hba hbt hat j test read done
    downs copy bump clear scale take add incs stride htest hdowns hdend hread hcopy hbump hclear
    hscale htake hincs hend hadd w B values k hk v hv hs hp ha ht ho

/-- **Counting binary digits by halving**: halving `t` until it is zero while incrementing
`c` adds `|bits t|` to `c` and clears `t`.

**Proof sketch.** Strong induction on the value of `t`: a nonzero value loses exactly one
binary digit when halved (`Complexity.LogProg.access_width_half`). -/
theorem halvCount_loop (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (y : List Bool)
    (t c : Fin m) (htc : t ≠ c) (test halve bump done : Λ)
    (htest : A test = .jz t done halve) (hhalve : A halve = .half t bump)
    (hbump : A bump = .inc c test) (B : ℕ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B)
    (hc : v c + (Nat.bits (v t)).length ≤ B) :
    AReach A oracle y (GuardLe A y B) (some test, v, none)
      (some done, Function.update (Function.update v t 0) c (v c + (Nat.bits (v t)).length),
        none) := by
  generalize hn : v t = n
  induction n using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have e : Function.update (Function.update v t 0) c (v c + (Nat.bits 0).length) = v := by
        funext r
        by_cases hrc : r = c
        · subst hrc; simp
        · by_cases hrt : r = t
          · subst hrt; simp [hrc, hn]
          · simp [hrc, hrt]
      rw [e]
      simpa [astep, htest, hn] using
        (AReach.single (A := A) (oracle := oracle) (x := y) (G := GuardLe A y B)
          (a := (some test, v, none)) ⟨by simp [PreS, htest], hv⟩)
    · rw [hn] at hc
      have hlen : (Nat.bits (n / 2)).length + 1 = (Nat.bits n).length :=
        access_width_half n (Nat.pos_iff_ne_zero.mp hpos)
      set v₁ := Function.update v t (n / 2)
      set v₂ := Function.update v₁ c (v c + 1)
      have b₁ : ∀ r, v₁ r ≤ B := register_update_le v t B _ hv (by have := hv t; omega)
      have b₂ : ∀ r, v₂ r ≤ B := register_update_le v₁ c B _ b₁ (by omega)
      have v₂t : v₂ t = n / 2 := by simp [v₂, v₁, htc]
      have v₂c : v₂ c = v c + 1 := by simp [v₂]
      have rest := ih (n / 2) (by omega) v₂ b₂ (by rw [v₂c, v₂t]; omega) v₂t
      have e : Function.update (Function.update v₂ t 0) c (v₂ c + (Nat.bits (n / 2)).length) =
          Function.update (Function.update v t 0) c (v c + (Nat.bits n).length) := by
        rw [v₂c]
        funext r
        by_cases hrc : r = c
        · subst hrc; simp; omega
        · by_cases hrt : r = t
          · subst hrt; simp [hrc]
          · simp [hrc, hrt, v₂, v₁]
      rw [e] at rest
      apply AReach.step ⟨by simp [PreS, htest], hv⟩
      simp only [astep, htest, hn, show n ≠ 0 by omega, ↓reduceIte]
      apply AReach.step ⟨by simp [PreS, hhalve], hv⟩
      simp only [astep, hhalve, hn]
      apply AReach.step ⟨by simp [PreS, hbump], b₁⟩
      simp only [astep, hbump]
      have : Function.update v₁ c (v₁ c + 1) = v₂ := by simp [v₂, v₁, htc.symm]
      rw [this]
      exact rest

/-- **Comparing two registers by counting**: stepping `t` up from below both `a` and `b`
reaches `a` first (or simultaneously) iff `a ≤ b`; the run ends in `yes` or `no`
accordingly, with `t = min a b`.

**Proof sketch.** Induction on `min a b - t`: at `t = a` answer yes, else at `t = b`
answer no, else increment `t`. -/
theorem le_loop (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (y : List Bool)
    (t a b : Fin m) (hta : t ≠ a) (htb : t ≠ b) (test₁ test₂ bump yes no : Λ)
    (htest₁ : A test₁ = .jeq t a yes test₂) (htest₂ : A test₂ = .jeq t b no bump)
    (hbump : A bump = .inc t test₁) (B : ℕ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B)
    (ha : v t ≤ v a) (hb : v t ≤ v b) :
    AReach A oracle y (GuardLe A y B) (some test₁, v, none)
      (some (if v a ≤ v b then yes else no), Function.update v t (min (v a) (v b)), none) := by
  generalize hn : min (v a) (v b) - v t = n
  induction n generalizing v with
  | zero =>
    have hm : v t = min (v a) (v b) := by omega
    by_cases hab : v a ≤ v b
    · have eq : v t = v a := by omega
      rw [if_pos hab, ← hm, Function.update_eq_self]
      simpa [astep, htest₁, eq] using
        (AReach.single (A := A) (oracle := oracle) (x := y) (G := GuardLe A y B)
          (a := (some test₁, v, none)) ⟨by simp [PreS, htest₁, hta], hv⟩)
    · have ne : v t ≠ v a := by omega
      have eq : v t = v b := by omega
      rw [if_neg hab, ← hm, Function.update_eq_self]
      apply AReach.step ⟨by simp [PreS, htest₁, hta], hv⟩
      simp only [astep, htest₁, if_neg ne]
      simpa [astep, htest₂, eq] using
        (AReach.single (A := A) (oracle := oracle) (x := y) (G := GuardLe A y B)
          (a := (some test₂, v, none)) ⟨by simp [PreS, htest₂, htb], hv⟩)
  | succ n ih =>
    have ne₁ : v t ≠ v a := by omega
    have ne₂ : v t ≠ v b := by omega
    set v₁ := Function.update v t (v t + 1)
    have b₁ : ∀ r, v₁ r ≤ B := register_update_le v t B _ hv (by have := hv a; omega)
    have va : v₁ a = v a := by simp [v₁, hta.symm]
    have vb : v₁ b = v b := by simp [v₁, htb.symm]
    have vt : v₁ t = v t + 1 := by simp [v₁]
    have rest := ih v₁ b₁ (by omega) (by omega) (by rw [va, vb, vt]; omega)
    rw [va, vb, show Function.update v₁ t (min (v a) (v b)) = Function.update v t (min (v a) (v b))
      by simp [v₁]] at rest
    apply AReach.step ⟨by simp [PreS, htest₁, hta], hv⟩
    simp only [astep, htest₁, if_neg ne₁]
    apply AReach.step ⟨by simp [PreS, htest₂, htb], hv⟩
    simp only [astep, htest₂, if_neg ne₂]
    apply AReach.step ⟨by simp [PreS, hbump], hv⟩
    simp only [astep, hbump]
    exact rest

end Complexity.Codec
