/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance of machines with split coins

The bookkeeping between the distinguishers and simulators of the composition theorem
[Gol04, §7.3.1, proof of Theorem 7.3.3] and the samplers they act on:
* coins as two strings (`appendCoins`) or as blocks (`blocksCoins`), read back by `take`, `drop`
  and `coinBlock`;
* a distinguisher `B` that pre-processes its sample with `p(n)` of its coins and hands the rest
  to `D` accepts a sampler `X` as often as `D` accepts the pre-processed sampler on the seed
  extended by those coins (`acceptProb_pre`);
* a simulator that post-processes another machine's output, against a distinguisher that
  pre-processes with the same map, is accepted as the other machine against the distinguisher
  (`acceptProb_post_pre`);
* a test machine with output `[P w]` accepts with the probability of `P` (`acceptProb_test`);
  the comparison of the second component of a sample with an advice string is such a machine
  (`exists_test`).

## Main definitions

* `ComposeProb.appendCoins`, `ComposeProb.blocksCoins`.

## Main results

* `ComposeProb.acceptProb_pre`, `ComposeProb.acceptProb_post_pre`, `ComposeProb.acceptProb_test`,
  `ComposeProb.exists_test`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform PPT machines, Definition 26.8) and §6.2 (Definition 155.1).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeProb

open Complexity Turing TCSlib.Cryptography

/-! ### Coins as strings -/

/-- **Two coin strings as one**: `{0,1}^a × {0,1}^b ≃ {0,1}^c` for `c = a + b`, the first string
followed by the second (`Fin.appendEquiv`). -/
def appendCoins {a b c : ℕ} (h : c = a + b) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin c → Bool) :=
  (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))

/-- The defining equation of `appendCoins` (see `appendCoins`).
`appendCoins h = (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl
Bool))`. -/
theorem appendCoins_eq {a b c : ℕ} (h : c = a + b) :
    appendCoins h =
      (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)) := rfl

/-- `⟦appendCoins h (u, v)⟧ = ⟦u⟧ ++ ⟦v⟧`. -/
theorem ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
    List.ofFn (appendCoins h (u, v)) = List.ofFn u ++ List.ofFn v := by
  rw [appendCoins_eq, Equiv.trans_apply, ofFn_arrowCongr_finCongr]
  exact List.ofFn_fin_append u v

/-- The first `a` bits of `appendCoins h (u, v)` are `u`.
`(List.ofFn (appendCoins h (u, v))).take a = List.ofFn u`. -/
theorem take_ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
    (List.ofFn (appendCoins h (u, v))).take a = List.ofFn u := by
  rw [ofFn_appendCoins, List.take_left' List.length_ofFn]

/-- The bits of `appendCoins h (u, v)` after the first `a` are `v`.
`(List.ofFn (appendCoins h (u, v))).drop a = List.ofFn v`. -/
theorem drop_ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
    (List.ofFn (appendCoins h (u, v))).drop a = List.ofFn v := by
  rw [ofFn_appendCoins, List.drop_left' List.length_ofFn]

/-- **Blocks of coins as one string**: `({0,1}^b)^q ≃ {0,1}^m` for `m = q·b`, the blocks in order
(`FunFamily.blocks`). -/
def blocksCoins {m q b : ℕ} (h : m = q * b) : (Fin q → Fin b → Bool) ≃ (Fin m → Bool) :=
  (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))

/-- The defining equation of `blocksCoins` (see `blocksCoins`).
`blocksCoins h = (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl
Bool))`. -/
theorem blocksCoins_eq {m q b : ℕ} (h : m = q * b) :
    blocksCoins h =
      (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)) :=
  rfl

/-- `⟦blocksCoins h t⟧ = ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧` (`ComposeSim.ofFn_blocks_symm`). -/
theorem ofFn_blocksCoins {m q b : ℕ} (h : m = q * b) (t : Fin q → Fin b → Bool) :
    List.ofFn (blocksCoins h t) = (List.ofFn fun j => List.ofFn (t j)).flatten := by
  rw [blocksCoins_eq, Equiv.trans_apply, ofFn_arrowCongr_finCongr, ComposeSim.ofFn_blocks_symm]

/-- Block `j` of `blocksCoins h t` is `t j`: `coinBlock b j ⟦blocksCoins h t⟧ = ⟦t j⟧`
(`coinBlock_flatten`). -/
theorem coinBlock_blocksCoins {m q b : ℕ} (h : m = q * b) (t : Fin q → Fin b → Bool) (j : Fin q) :
    coinBlock b j (List.ofFn (blocksCoins h t)) = List.ofFn (t j) := by
  rw [ofFn_blocksCoins, coinBlock_flatten (List.ofFn fun j => List.ofFn (t j))
    (fun c hc => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact j.2), List.getElem_ofFn]

/-! ### Acceptance -/

/-- **A distinguisher with pre-processing and extra coins**: if `B` has coins `p + D.coins` and
`B(1^n, w; r) = D(1^n, Ψ w r_{<p(n)}; r_{≥p(n)})`, then
`acceptProb X (B.distinguisherL n) = acceptProb (fun (s, e) => Ψ (X s) ⟦e⟧) (D.distinguisherL n)`
over `e ∈ {0,1}^{p(n)}`.

**Proof sketch.** Split `B`'s coins as `{0,1}^{p(n)} × D.Coins n` (`appendCoins`,
`uprob_comp_equiv`); the cut coins are the two halves (`take_ofFn_appendCoins`,
`drop_ofFn_appendCoins`); reassociate the seed (`Equiv.prodAssoc`). -/
theorem acceptProb_pre {σ : Type*} [Fintype σ] (X : σ → List Bool) (B D : NUPPT) (p : PolyExpr)
    (n : ℕ) (Ψ : List Bool → List Bool → List Bool) (hc : B.coins = .add p D.coins)
    (hB : ∀ w r, B.runAtL n w r = D.runAtL n (Ψ w (r.take (p.eval n))) (r.drop (p.eval n))) :
    acceptProb X (B.distinguisherL n) =
      acceptProb (fun z : σ × (Fin (p.eval n) → Bool) => Ψ (X z.1) (List.ofFn z.2))
        (D.distinguisherL n) := by
  have hlen : B.coinLen n = p.eval n + D.coinLen n := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hc, PolyExpr.eval_add]
  let e : (Fin (p.eval n) → Bool) × D.Coins n ≃ B.Coins n := appendCoins hlen
  rw [acceptProb_def, acceptProb_def]
  calc uprob (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true)
      = uprob (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
          B.distinguisherL n (X z.1) (e z.2) = true) :=
        (uprob_comp_equiv ((Equiv.refl σ).prodCongr e)
          (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true)).symm
    _ = uprob (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
          D.distinguisherL n (Ψ (X z.1) (List.ofFn z.2.1)) z.2.2 = true) := by
        congr 1
        funext z
        rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAt_eq, hB,
          take_ofFn_appendCoins, drop_ofFn_appendCoins]
    _ = uprob (fun z : (σ × (Fin (p.eval n) → Bool)) × D.Coins n =>
          D.distinguisherL n (Ψ (X z.1.1) (List.ofFn z.1.2)) z.2 = true) :=
        (uprob_comp_equiv (Equiv.prodAssoc σ (Fin (p.eval n) → Bool) (D.Coins n))
          (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
            D.distinguisherL n (Ψ (X z.1) (List.ofFn z.2.1)) z.2.2 = true)).symm

/-- **A simulator with post-processing against a distinguisher with pre-processing**: let
`S(1^n, w; r) = Ψ (S'(1^n, w; r_{<S'.coins(n)})) r_{≥S'.coins(n)}` with coins `S'.coins + p`, and
`B(1^n, v; r) = D(1^n, Ψd v r_{<p(n)}; r_{≥p(n)})` with coins `p + D.coins`, where
`Ψd ⟨hv, o⟩ e = ⟨Ψ hv e, o⟩`. Then `D` accepts `⟨S(1^n, w), o⟩` as often as `B` accepts
`⟨S'(1^n, w), o⟩`.

**Proof sketch.** Split `S`'s coins as `S'.Coins n × {0,1}^{p(n)}` (`appendCoins`,
`acceptProb_comp_equiv`; `take_ofFn_appendCoins`, `drop_ofFn_appendCoins`), and unfold `B` by
`acceptProb_pre`; the two samplers on `S'.Coins n × {0,1}^{p(n)}` agree by `hΨ`. -/
theorem acceptProb_post_pre (S S' B D : NUPPT) (p : PolyExpr) (n : ℕ)
    (Ψ Ψd : List Bool → List Bool → List Bool) (w o : List Bool)
    (hSc : S.coins = .add S'.coins p)
    (hS : ∀ r, S.runAtL n w r =
      Ψ (S'.runAtL n w (r.take (S'.coinLen n))) (r.drop (S'.coinLen n)))
    (hBc : B.coins = .add p D.coins)
    (hB : ∀ v r, B.runAtL n v r = D.runAtL n (Ψd v (r.take (p.eval n))) (r.drop (p.eval n)))
    (hΨ : ∀ hv e, Ψd (pairEncode hv o) e = pairEncode (Ψ hv e) o) :
    acceptProb (fun s : S.Coins n => pairEncode (S.runAt n w s) o) (D.distinguisherL n) =
      acceptProb (fun s : S'.Coins n => pairEncode (S'.runAt n w s) o) (B.distinguisherL n) := by
  have hlen : S.coinLen n = S'.coinLen n + p.eval n := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hSc, PolyExpr.eval_add]
  rw [acceptProb_pre _ B D p n Ψd hBc hB]
  refine (acceptProb_comp_equiv (appendCoins hlen)
    (fun s : S.Coins n => pairEncode (S.runAt n w s) o) (D.distinguisherL n)).symm.trans ?_
  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
  rw [hΨ, NUPPT.runAt_eq, NUPPT.runAt_eq, hS, take_ofFn_appendCoins, drop_ofFn_appendCoins]

/-- **A test machine**: if `B(1^n, w; r) = [P w]` for all `w`, `r`, then `B` accepts the sampler
`X` with probability `Pr_s[P (X s)]`:
`acceptProb X (B.distinguisherL n) = uprob (fun s => P (X s) = true)` (`uprob_fst`). -/
theorem acceptProb_test {σ : Type*} [Fintype σ] (X : σ → List Bool) (B : NUPPT) (n : ℕ)
    (P : List Bool → Bool) (hB : ∀ w r, B.runAtL n w r = [P w]) :
    acceptProb X (B.distinguisherL n) = uprob fun s => P (X s) = true := by
  have h : (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true) =
      fun z => P (X z.1) = true := by
    funext z
    rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hB]
    simp
  rw [acceptProb_def, h]
  exact uprob_fst fun s => P (X s) = true

/-- **The comparison with an advice string**: for a polynomially bounded advice family `α` there
is an `NUPPT` `B` with `B(1^n, w; r) = [eqW ⟨pairSndD w, α n⟩]`, which accepts exactly when the
second component of the sample is `α n` (`BinArith.eqW_pairEncode`). -/
theorem exists_test (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) :
    ∃ B : NUPPT, ∀ n w r, B.runAtL n w r = [BinArith.eqW (pairEncode (pairSndD w) (α n))] := by
  have hf : PolyTimeComputable fun z =>
      [BinArith.eqW (pairEncode (pairSndD (NUPPT.inArg z)) (NUPPT.inAdvice z))] :=
    BinArith.polyTimeComputable_eqW.comp' ((polyTimeComputable_pairSndD.comp'
      NUPPT.polyTimeComputable_inArg).pairEncode NUPPT.polyTimeComputable_inAdvice)
  refine ⟨NUPPT.ofPolyTime hf (.const 0) a α hα, fun n w r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp only [NUPPT.advInput_eq, ← NUPPT.layout_eq, NUPPT.inArg_layout, NUPPT.inAdvice_layout]

end TCSlib.Cryptography.SecureComputation.ComposeProb
