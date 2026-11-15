/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: the shape of the simulators of Proposition 161.5

The simulators `S_A` and `S_B` of [PS10, Proposition 161.5] restated for the helper modules
(which cannot import `SecureComputation/ObliviousTransfer.lean`, the owned file that imports them):
the coin segments, the simulated index and samples, and the two simulated views, with the
predicates `OT.IsSimA` and `OT.IsSimB` that the owned file proves for `otSimA` and `otSimB`.
On a tape assembled from typed coin blocks (`OT.splitLen`), the simulated views are computed
explicitly (`OT.simAView_layout`, `OT.simBView_layout`).

## Main definitions

* `OT.splitLen`: a coin string of length `c = a + b` as an `a`-bit and a `b`-bit string.
* `OT.simSeg`, `OT.simIndex`, `OT.simSampled`: a coin segment, the simulated index and a
  simulated sample (the bodies of `coinSeg`, `simIdx`, `simSample`).
* `OT.simAView`, `OT.simZbit`, `OT.simZpair`, `OT.simBView`: the simulators' raw functions (the
  bodies of `otSimAFun`, `otSimZb`, `otSimZ`, `otSimBFun`).
* `OT.IsSimA`, `OT.IsSimB`: machines of the simulators' shape.

## Main results

* `OT.splitLen_symm_ofFn`: the assembled tape is the concatenation of the blocks.
* `OT.simSeg_layout`, `OT.simIndex_layout`, `OT.simSampled_layout`: the pieces on such a tape.
* `OT.simAView_layout`, `OT.simBView_layout`: the simulated views on such a tape.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5 (book pp. 160–162).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-! ### Splitting coin strings -/

/-- **A coin string of length `c = a + b` split** into its first `a` and last `b` bits:
`splitCoins a b` after the length cast `Fin c ≃ Fin (a + b)`. -/
def splitLen {a b c : ℕ} (h : c = a + b) : (Fin c → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans (splitCoins a b)

/-- The tape assembled from two blocks is their concatenation:
`ofFn ((splitLen h).symm (r₁, r₂)) = ofFn r₁ ++ ofFn r₂` (`ofFn_splitCoins_symm`). -/
theorem splitLen_symm_ofFn {a b c : ℕ} (h : c = a + b) (p : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn ((splitLen h).symm p) = List.ofFn p.1 ++ List.ofFn p.2 := by
  rw [← ofFn_splitCoins_symm]
  exact (List.ofFn_congr h _).trans rfl

/-! ### The simulators restated -/

/-- The coin segment of length `q(n)` after the first `p(n)` coins of a raw layout `z` (the body
of `coinSeg`): `(inCoins z).drop p(|inParam z|) |>.take q(|inParam z|)`. -/
def simSeg (p q : PolyExpr) (z : List Bool) : List Bool :=
  ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take (q.eval (NUPPT.inParam z).length)

/-- The defining equation of `simSeg`: `simSeg p q z =
((inCoins z).drop p(|inParam z|)).take q(|inParam z|)`. -/
theorem simSeg_eq (p q : PolyExpr) (z : List Bool) :
    simSeg p q z =
      ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take
        (q.eval (NUPPT.inParam z).length) := rfl

/-- The simulated index (the body of `simIdx`):
`simIndex T z = fst Gen(inParam z; simSeg 0 coins_Gen z)`. -/
def simIndex (z : List Bool) : List Bool :=
  pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    (simSeg (.const 0) T.gen.coins z)))

/-- The defining equation of `simIndex`: `simIndex T z =
fst Gen.output (layout (inParam z) [] [] (simSeg 0 coins_Gen z))`. -/
theorem simIndex_eq (z : List Bool) :
    simIndex T z = pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      (simSeg (.const 0) T.gen.coins z))) := rfl

/-- A simulated sample after `p(n)` coins (the body of `simSample`):
`simSampled T p z = Sample(inParam z, simIndex z; simSeg p coins_Sample z)`. -/
def simSampled (p : PolyExpr) (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIndex T z) [] (simSeg p T.sample.coins z))

/-- The defining equation of `simSampled`: `simSampled T p z =
Sample.output (layout (inParam z) (simIndex T z) [] (simSeg p coins_Sample z))`. -/
theorem simSampled_eq (p : PolyExpr) (z : List Bool) :
    simSampled T p z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIndex T z) []
        (simSeg p T.sample.coins z)) := rfl

/-- **`S_A`'s raw function** [PS10, Proposition 161.5] (the body of `otSimAFun`):
`simAView T z = ⟨⟨1^n, ⟨a₁, a₂⟩⟩, ⟨r_Gen, [⟨y₁, y₂⟩, []]⟩⟩` with two simulated samples
`y₁, y₂`. -/
def simAView (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (simSeg (.const 0) T.gen.coins z)
      (pairEncode (pairEncode (simSampled T T.gen.coins z)
          (simSampled T (.add T.gen.coins T.sample.coins) z))
        (pairEncode [] [])))

/-- The defining equation of `simAView`: `simAView T z = ⟨⟨inParam z, fst (inArg z)⟩,
⟨simSeg 0 coins_Gen z, [⟨y₁, y₂⟩, []]⟩⟩` with the two simulated samples `y₁, y₂`. -/
theorem simAView_eq (z : List Bool) :
    simAView T z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (simSeg (.const 0) T.gen.coins z)
          (pairEncode (pairEncode (simSampled T T.gen.coins z)
              (simSampled T (.add T.gen.coins T.sample.coins) z))
            (pairEncode [] []))) := rfl

/-- `S_B`'s mask `z_b = h(x) ⊕ a_b` (the body of `otSimZb`). -/
def simZbit (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (simIndex T z) (simSampled T T.gen.coins z)))
    (pairSndD (NUPPT.inArg z))

/-- The defining equation of `simZbit`: `simZbit T H z =
zipWith xor (H ⟨simIndex T z, simSampled T coins_Gen z⟩) (snd (inArg z))`. -/
theorem simZbit_eq (z : List Bool) :
    simZbit T H z =
      List.zipWith xor (H (pairEncode (simIndex T z) (simSampled T T.gen.coins z)))
        (pairSndD (NUPPT.inArg z)) := rfl

/-- `S_B`'s pair `(z₁, z₂)` (the body of `otSimZ`): `z_b` from `simZbit`, `z_{1−b}` one coin,
`simZpair T H z = ⟨c, z_b⟩` if the choice bit is set, else `⟨z_b, c⟩`. -/
def simZpair (z : List Bool) : List Bool :=
  if (pairFstD (NUPPT.inArg z)).headD false then
    pairEncode (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
      (simZbit T H z)
  else
    pairEncode (simZbit T H z)
      (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)

/-- The defining equation of `simZpair`: `⟨c, z_b⟩` if the choice bit is set, else `⟨z_b, c⟩`,
with `c` the last coin segment and `z_b = simZbit T H z`. -/
theorem simZpair_eq (z : List Bool) :
    simZpair T H z =
      if (pairFstD (NUPPT.inArg z)).headD false then
        pairEncode (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
          (simZbit T H z)
      else
        pairEncode (simZbit T H z)
          (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z) := rfl

/-- **`S_B`'s raw function** [PS10, Proposition 161.5] (the body of `otSimBFun`):
`simBView T H z = ⟨⟨1^n, [b]⟩, ⟨r_B, [i, ⟨z₁, z₂⟩, []]⟩⟩`. -/
def simBView (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (simSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
      (pairEncode (simIndex T z) (pairEncode (simZpair T H z) (pairEncode [] []))))

/-- The defining equation of `simBView`: `simBView T H z = ⟨⟨inParam z, fst (inArg z)⟩,
⟨simSeg coins_Gen (2 coins_Sample) z, [simIndex T z, simZpair T H z, []]⟩⟩`. -/
theorem simBView_eq (z : List Bool) :
    simBView T H z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (simSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
          (pairEncode (simIndex T z) (pairEncode (simZpair T H z) (pairEncode [] [])))) := rfl

/-- **A machine of `S_A`'s shape**: coins `coins_Gen + (coins_Sample + coins_Sample)`, and
`S(1^n, y; r) = simAView T (layout 1^n y [] r)`. -/
def IsSimA (S : NUPPT) : Prop :=
  S.coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) ∧
    ∀ n y (r : S.Coins n),
      S.runAt n y r = simAView T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r))

/-- The defining property of `IsSimA`: `IsSimA T S` iff `S.coins = coins_Gen + (coins_Sample +
coins_Sample)` and `S(1^n, y; r) = simAView T (layout 1^n y [] r)`. -/
theorem isSimA_iff (S : NUPPT) :
    IsSimA T S ↔
      S.coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) ∧
        ∀ n y (r : S.Coins n),
          S.runAt n y r = simAView T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) :=
  Iff.rfl

/-- **A machine of `S_B`'s shape**: coins `coins_Gen + (coins_Sample + (coins_Sample + 1))`, and
`S(1^n, y; r) = simBView T H (layout 1^n y [] r)`. -/
def IsSimB (S : NUPPT) : Prop :=
  S.coins = .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) ∧
    ∀ n y (r : S.Coins n),
      S.runAt n y r = simBView T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r))

/-- The defining property of `IsSimB`: `IsSimB T H S` iff its coins are `coins_Gen +
(coins_Sample + (coins_Sample + 1))` and `S(1^n, y; r) = simBView T H (layout 1^n y [] r)`. -/
theorem isSimB_iff (S : NUPPT) :
    IsSimB T H S ↔
      S.coins = .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) ∧
        ∀ n y (r : S.Coins n),
          S.runAt n y r = simBView T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) :=
  Iff.rfl

/-! ### The simulators on assembled tapes -/

/-- A coin segment of a tape `A ++ (B ++ C)` with `|A| = p(|u|)` and `|B| = q(|u|)` is `B`. -/
theorem simSeg_layout {p q : PolyExpr} (u y α : List Bool) {A B : List Bool} (C : List Bool)
    (hA : A.length = p.eval u.length) (hB : B.length = q.eval u.length) :
    simSeg p q (NUPPT.layout u y α (A ++ (B ++ C))) = B := by
  rw [simSeg_eq, NUPPT.inCoins_layout, NUPPT.inParam_layout, List.drop_left' hA,
    List.take_left' hB]

/-- The typed tape of a machine as a list has the coin length: `|ofFn r| = coins_A(n)`. -/
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]

/-- On a tape starting with `Gen`'s coins `r`, the simulated index is `index n r`:
`simIndex T (layout 1^n y [] (ofFn r ++ B)) = T.index n r`. -/
theorem simIndex_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n) (B : List Bool) :
    simIndex T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r ++ B)) = T.index n r := by
  have h := simSeg_layout (p := .const 0) (q := T.gen.coins) (List.replicate n true) y [] B
    (A := []) (B := List.ofFn r) (by rw [PolyExpr.eval_const, List.length_nil])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.nil_append] at h
  rw [simIndex_eq, h, NUPPT.inParam_layout, Collection.index_eq, NUPPT.runAt_eq,
    NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.gen_uniform]

/-- On a tape `r ++ (A ++ (s ++ C))` with `|A| = p(n) - coins_Gen(n)`, the simulated sample
after `p(n)` coins is `Sample(1^n, index n r; s)`. -/
theorem simSampled_layout {p : PolyExpr} (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (A : List Bool) (s : T.sample.Coins n) (C : List Bool)
    (hA : (List.ofFn r ++ A).length = p.eval n) :
    simSampled T p
        (NUPPT.layout (List.replicate n true) y [] (List.ofFn r ++ (A ++ (List.ofFn s ++ C)))) =
      T.sample.runAt n (T.index n r) s := by
  have h := simSeg_layout (p := p) (q := T.sample.coins) (List.replicate n true) y []
    (A := List.ofFn r ++ A) (B := List.ofFn s) C (by rw [hA, List.length_replicate])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.append_assoc] at h
  rw [simSampled_eq, h, NUPPT.inParam_layout, simIndex_layout,
    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.sample_uniform]

/-- **`S_A`'s view on the tape `r ++ (s₁ ++ s₂)`**:
`⟨⟨1^n, fst y⟩, ⟨r, [⟨Sample(i; s₁), Sample(i; s₂)⟩, []]⟩⟩` with `i = index n r`. -/
theorem simAView_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (s₁ s₂ : T.sample.Coins n) :
    simAView T (NUPPT.layout (List.replicate n true) y []
        (List.ofFn r ++ (List.ofFn s₁ ++ List.ofFn s₂))) =
      pairEncode (pairEncode (List.replicate n true) (pairFstD y))
        (pairEncode (List.ofFn r)
          (pairEncode (pairEncode (T.sample.runAt n (T.index n r) s₁)
              (T.sample.runAt n (T.index n r) s₂))
            (pairEncode [] []))) := by
  have h₀ := simSeg_layout (p := .const 0) (q := T.gen.coins) (List.replicate n true) y []
    (A := []) (B := List.ofFn r) (List.ofFn s₁ ++ List.ofFn s₂)
    (by rw [PolyExpr.eval_const, List.length_nil])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.nil_append] at h₀
  have h₁ := simSampled_layout T (p := T.gen.coins) n y r [] s₁ (List.ofFn s₂)
    (by rw [List.append_nil, length_ofFn_coins])
  have h₂ := simSampled_layout T (p := .add T.gen.coins T.sample.coins) n y r
    (List.ofFn s₁) s₂ [] (by rw [List.length_append, length_ofFn_coins, length_ofFn_coins,
      PolyExpr.eval_add])
  rw [List.nil_append] at h₁
  rw [List.append_nil] at h₂
  rw [simAView_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, h₀, h₁, h₂]

/-- **`S_B`'s view on the tape `r ++ (s₁ ++ (s₂ ++ c))`**:
`⟨⟨1^n, fst y⟩, ⟨s₁ ++ s₂, [i, Z, []]⟩⟩` with `i = index n r`, `z_b = H ⟨i, Sample(i; s₁)⟩ ⊕ snd y`
and `Z = ⟨c, z_b⟩` if `(fst y).headD false`, else `⟨z_b, c⟩`.

**Proof sketch.** The coin segments of the tape are `s₁ ++ s₂` and `c` (`simSeg_layout`), the
simulated index is `index n r` (`simIndex_layout`) and the first simulated sample is
`Sample(i; s₁)` (`simSampled_layout`); rewrite `simBView`, `simZpair` and `simZbit` with them. -/
theorem simBView_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (s₁ s₂ : T.sample.Coins n) (c : Fin 1 → Bool) :
    simBView T H (NUPPT.layout (List.replicate n true) y []
        (List.ofFn r ++ (List.ofFn s₁ ++ (List.ofFn s₂ ++ List.ofFn c)))) =
      pairEncode (pairEncode (List.replicate n true) (pairFstD y))
        (pairEncode (List.ofFn s₁ ++ List.ofFn s₂)
          (pairEncode (T.index n r)
            (pairEncode
              (if (pairFstD y).headD false then
                pairEncode (List.ofFn c)
                  (List.zipWith xor (H (pairEncode (T.index n r)
                    (T.sample.runAt n (T.index n r) s₁))) (pairSndD y))
              else
                pairEncode (List.zipWith xor (H (pairEncode (T.index n r)
                    (T.sample.runAt n (T.index n r) s₁))) (pairSndD y))
                  (List.ofFn c))
              (pairEncode [] [])))) := by
  have hs := simSeg_layout (p := T.gen.coins) (q := .add T.sample.coins T.sample.coins)
    (List.replicate n true) y [] (A := List.ofFn r) (B := List.ofFn s₁ ++ List.ofFn s₂)
    (List.ofFn c) (by rw [length_ofFn_coins, List.length_replicate])
    (by rw [List.length_append, length_ofFn_coins, length_ofFn_coins, PolyExpr.eval_add,
      List.length_replicate])
  rw [List.append_assoc] at hs
  have hc := simSeg_layout (p := .add T.gen.coins (.add T.sample.coins T.sample.coins))
    (q := .const 1) (List.replicate n true) y []
    (A := List.ofFn r ++ (List.ofFn s₁ ++ List.ofFn s₂)) (B := List.ofFn c) []
    (by rw [List.length_append, List.length_append, length_ofFn_coins, length_ofFn_coins,
      length_ofFn_coins, PolyExpr.eval_add, PolyExpr.eval_add, List.length_replicate])
    (by rw [List.length_ofFn, PolyExpr.eval_const])
  rw [List.append_nil, List.append_assoc, List.append_assoc] at hc
  have hi := simIndex_layout T n y r (List.ofFn s₁ ++ (List.ofFn s₂ ++ List.ofFn c))
  have h₁ := simSampled_layout T (p := T.gen.coins) n y r [] s₁ (List.ofFn s₂ ++ List.ofFn c)
    (by rw [List.append_nil, length_ofFn_coins])
  rw [List.nil_append] at h₁
  rw [simBView_eq, simZpair_eq, simZbit_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, hs, hc,
    hi, h₁]

/-! ### The coin spaces -/

/-- **The real coins of a protocol of the shape of Protocol 160.4**: Alice's tape is `Gen`'s
coins and Bob's two sampler blocks, `ExecCoins ≃ Coins_Gen × (Coins_Sample × Coins_Sample)`. -/
def realCoins {π : Protocol} (hπ : IsOT T H π) (n : ℕ) :
    π.ExecCoins π.P (List.replicate n true) ≃
      T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n) :=
  Equiv.prodCongr
    (Equiv.arrowCongr (finCongr (by
      rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.1, List.length_replicate,
        NUPPT.coinLen_eq])) (Equiv.refl Bool))
    (splitLen (by
      rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.2.1, List.length_replicate,
        PolyExpr.eval_add, NUPPT.coinLen_eq]))

/-- Alice's real tape is `Gen`'s coins: `ofFn ((realCoins hπ n).symm p).1 = ofFn p.1`. -/
theorem realCoins_symm_fst_ofFn {π : Protocol} (hπ : IsOT T H π) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((realCoins T H hπ n).symm p).1 = List.ofFn p.1 :=
  (List.ofFn_congr (by rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.1,
    List.length_replicate, NUPPT.coinLen_eq]) _).trans rfl

/-- Bob's real tape is the two sampler blocks:
`ofFn ((realCoins hπ n).symm p).2 = ofFn p.2.1 ++ ofFn p.2.2`. -/
theorem realCoins_symm_snd_ofFn {π : Protocol} (hπ : IsOT T H π) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((realCoins T H hπ n).symm p).2 = List.ofFn p.2.1 ++ List.ofFn p.2.2 :=
  splitLen_symm_ofFn _ p.2

/-- **`S_A`'s coins**: `Coins_S ≃ Coins_Gen × (Coins_Sample × Coins_Sample)` for a machine of
`S_A`'s shape. -/
def simACoins {S : NUPPT} (hS : IsSimA T S) (n : ℕ) :
    S.Coins n ≃ T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n) :=
  (splitLen (by rw [NUPPT.coinLen_eq, ((isSimA_iff T S).1 hS).1, PolyExpr.eval_add,
    NUPPT.coinLen_eq])).trans
    (Equiv.prodCongr (Equiv.refl _) (splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq])))

/-- `S_A`'s tape from blocks: `ofFn ((simACoins hS n).symm p) = ofFn p.1 ++ (ofFn p.2.1 ++
ofFn p.2.2)`. -/
theorem simACoins_symm_ofFn {S : NUPPT} (hS : IsSimA T S) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((simACoins T hS n).symm p) =
      List.ofFn p.1 ++ (List.ofFn p.2.1 ++ List.ofFn p.2.2) := by
  rw [simACoins, Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
    splitLen_symm_ofFn]

/-- **`S_B`'s coins**: `Coins_S ≃ Coins_Gen × (Coins_Sample × (Coins_Sample × {0,1}))` for a
machine of `S_B`'s shape. -/
def simBCoins {S : NUPPT} (hS : IsSimB T H S) (n : ℕ) :
    S.Coins n ≃ T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool))) :=
  (splitLen (by rw [NUPPT.coinLen_eq, ((isSimB_iff T H S).1 hS).1, PolyExpr.eval_add,
    NUPPT.coinLen_eq])).trans
    (Equiv.prodCongr (Equiv.refl _) ((splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq])).trans
      (Equiv.prodCongr (Equiv.refl _)
        (splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq, PolyExpr.eval_const])))))

/-- `S_B`'s tape from blocks: `ofFn ((simBCoins hS n).symm p) =
ofFn p.1 ++ (ofFn p.2.1 ++ (ofFn p.2.2.1 ++ ofFn p.2.2.2))`. -/
theorem simBCoins_symm_ofFn {S : NUPPT} (hS : IsSimB T H S) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) :
    List.ofFn ((simBCoins T H hS n).symm p) =
      List.ofFn p.1 ++ (List.ofFn p.2.1 ++ (List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2)) := by
  rw [simBCoins, Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply, splitLen_symm_ofFn]

/-! ### The OT inputs and outputs -/

/-- Alice's OT input length is `2`, `otFunctionality.inA.eval n = 2` (`otFunctionality_inA`). -/
theorem inA_eval (n : ℕ) : otFunctionality.inA.eval n = 2 := by
  rw [otFunctionality_inA, PolyExpr.eval_const]

/-- Bob's OT input length is `1`, `otFunctionality.inB.eval n = 1` (`otFunctionality_inB`). -/
theorem inB_eval (n : ℕ) : otFunctionality.inB.eval n = 1 := by
  rw [otFunctionality_inB, PolyExpr.eval_const]

/-- Alice's OT input read as two bits: `inA2 a j = a (cast j)`. -/
def inA2 {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) : Fin 2 → Bool :=
  fun j => a (Fin.cast (inA_eval n).symm j)

/-- The defining equation of `inA2`: `inA2 a j = a (Fin.cast (inA_eval n).symm j)`. -/
theorem inA2_apply {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) (j : Fin 2) :
    inA2 a j = a (Fin.cast (inA_eval n).symm j) := rfl

/-- Reading the input as two bits keeps its string: `ofFn (inA2 a) = ofFn a`. -/
theorem ofFn_inA2 {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) :
    List.ofFn (inA2 a) = List.ofFn a :=
  ((List.ofFn_congr (inA_eval n) a).trans rfl).symm

/-- Bob's OT input read as one bit: `inB1 b j = b (cast j)`. -/
def inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) : Fin 1 → Bool :=
  fun j => b (Fin.cast (inB_eval n).symm j)

/-- The defining equation of `inB1`: `inB1 b j = b (Fin.cast (inB_eval n).symm j)`. -/
theorem inB1_apply {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) (j : Fin 1) :
    inB1 b j = b (Fin.cast (inB_eval n).symm j) := rfl

/-- Reading the input as one bit keeps its string: `ofFn (inB1 b) = ofFn b`. -/
theorem ofFn_inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (inB1 b) = List.ofFn b :=
  ((List.ofFn_congr (inB_eval n) b).trans rfl).symm

/-- Bob's choice string is the one-bit list `[inB1 b 0]`: `List.ofFn b = [inB1 b 0]`. -/
theorem ofFn_eq_inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn b = [inB1 b 0] := by
  rw [← ofFn_inB1, List.ofFn_succ, List.ofFn_zero]

/-- Alice's OT output is empty: `ofFn (f n a b).1 = []`. -/
theorem ofFn_f_fst (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (otFunctionality.f n a b).1 = [] :=
  List.eq_nil_of_length_eq_zero
    (by rw [List.length_ofFn, otFunctionality_outA, PolyExpr.eval_const])

/-- Bob's OT output is the chosen bit: `ofFn (f n a b).2 = [a_b]` with
`a_b = inA2 a (if inB1 b 0 then 1 else 0)` (`otFunctionality_f_snd_apply`). -/
theorem ofFn_f_snd (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (otFunctionality.f n a b).2 = [inA2 a (if inB1 b 0 then 1 else 0)] := by
  have h : otFunctionality.outB.eval n = 1 := by
    rw [otFunctionality_outB, PolyExpr.eval_const]
  rw [List.ofFn_congr h, List.ofFn_succ, List.ofFn_zero, otFunctionality_f_snd_apply]
  rfl

end TCSlib.Cryptography.SecureComputation.OT
