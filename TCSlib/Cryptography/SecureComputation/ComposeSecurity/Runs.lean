/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposePhases
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The real samples of the composed protocol, run by run

Step 2 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]: the coins
of an honest execution of `H.compose ρ` on `1^n` are the `main`-tapes `m` and one pair of
`ρ`-tapes `t j` per call (`composeCoins`), and when every run's outputs are the ideal answers
(`GoodRuns`), the real sample of either side is the assembled view (`ComposeSim.asmView`) of the
real views of the runs (`realViewA`, `realViewB`), with the main phase and the other party's output
those of the hybrid execution on the `main`-tapes (`realA_compose_eq`, `realB_compose_eq`, using
`hM`).

## Main definitions

* `ComposeSim.splitCoins`: `{0,1}^a × ({0,1}^b)^q ≃ {0,1}^m` for `m = a + q·b`.
* `HybridProtocol.composeCoins`: the coins of `H.compose ρ` as `main`-tapes and run tapes.
* `HybridProtocol.inA`, `inB`: the call inputs as strings.
* `HybridProtocol.realViewA`, `realViewB`: the encoded views of a party in the honest runs.
* `HybridProtocol.GoodRuns`: every run's outputs are the ideal answers.

## Main results

* `ComposeSim.ofFn_splitCoins`, `HybridProtocol.ofFn_composeCoins_fst`, `_snd`.
* `HybridProtocol.answersRealA_eq_answersA`, `answersRealB_eq_answersB`: under `GoodRuns` the honest
  answers are the ideal ones.
* `HybridProtocol.realA_compose_eq`, `realB_compose_eq`: the real samples under `GoodRuns`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim Compose

namespace ComposeSim

/-- **A tape and `q` blocks as one string**: `{0,1}^a × ({0,1}^b)^q ≃ {0,1}^m` for
`m = a + q·b`, the tape followed by the blocks in order (`Fin.appendEquiv`, `FunFamily.blocks`). -/
def splitCoins {m a q b : ℕ} (h : m = a + q * b) :
    (Fin a → Bool) × (Fin q → Fin b → Bool) ≃ (Fin m → Bool) :=
  ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
    ((Fin.appendEquiv a (q * b)).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)))

/-- The defining equation of `splitCoins` (see `splitCoins`).
`splitCoins h = ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
((Fin.appendEquiv a (q * b)).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)))`. -/
theorem splitCoins_eq {m a q b : ℕ} (h : m = a + q * b) :
    splitCoins h = ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
      ((Fin.appendEquiv a (q * b)).trans
        (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))) := rfl

/-- The blocks as one string: `⟦(blocks q b).symm t⟧ = ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧`.

**Proof sketch.** `List.ofFn_mul` writes `⟦v⟧` for `v : Fin (q·b) → Bool` as the concatenation
of `q` blocks of `b` bits, entry `j` of block `i` being `v (i·b + j)`; by
`FunFamily.blocks_symm_apply` that is `t i j`, since `(i·b + j) / b = i` and
`(i·b + j) % b = j` for `j < b`. -/
theorem ofFn_blocks_symm (q b : ℕ) (t : Fin q → Fin b → Bool) :
    List.ofFn ((FunFamily.blocks q b).symm t) = (List.ofFn fun j => List.ofFn (t j)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => List.ofFn_inj.2 (funext fun j => ?_))
  rw [FunFamily.blocks_symm_apply]
  have hj := j.2
  have hb : 0 < b := by omega
  congr 1
  · refine Fin.ext ?_
    rw [Fin.coe_divNat]
    show ((i : ℕ) * b + j) / b = i
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]
  · refine Fin.ext ?_
    rw [Fin.coe_modNat]
    show ((i : ℕ) * b + j) % b = j
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **The split coins as a string**: `⟦splitCoins h (u, t)⟧ = ⟦u⟧ ++ ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧`. -/
theorem ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) :
    List.ofFn (splitCoins h (u, t)) =
      List.ofFn u ++ (List.ofFn fun j => List.ofFn (t j)).flatten := by
  rw [splitCoins_eq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr]
  show List.ofFn (Fin.append u ((FunFamily.blocks q b).symm t)) = _
  rw [List.ofFn_fin_append, ofFn_blocks_symm]

/-- The first `a` bits of `splitCoins h (u, t)` are `u`.
`(List.ofFn (splitCoins h (u, t))).take a = List.ofFn u`. -/
theorem take_ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) : (List.ofFn (splitCoins h (u, t))).take a = List.ofFn u := by
  rw [ofFn_splitCoins, List.take_left' List.length_ofFn]

/-- Block `j < q` of `splitCoins h (u, t)` is `t j`:
`runTape a b j ⟦splitCoins h (u, t)⟧ = ⟦t j⟧` (`Compose.runTape_eq`). -/
theorem runTape_ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) (j : Fin q) :
    runTape a b j (List.ofFn (splitCoins h (u, t))) = List.ofFn (t j) := by
  rw [runTape_eq, ofFn_splitCoins, ← List.drop_drop, List.drop_left' List.length_ofFn]
  have hblk := coinBlock_flatten (B := b) (List.ofFn fun j => List.ofFn (t j))
    (fun c hc => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact j.2)
  rw [coinBlock_eq] at hblk
  rw [hblk, List.getElem_ofFn]

/-- **A concatenation over `L·R` indices in `L` blocks of `R`**:
`(range (L·R)).flatMap f = (range L).flatMap fun j => (range R).flatMap fun p => f (R·j + p)`. -/
theorem flatMap_range_mul (f : ℕ → List Bool) (R : ℕ) : ∀ L,
    (List.range (L * R)).flatMap f =
      (List.range L).flatMap fun j => (List.range R).flatMap fun p => f (R * j + p)
  | 0 => by rw [Nat.zero_mul, List.range_zero, List.flatMap_nil, List.flatMap_nil]
  | L + 1 => by
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, flatMap_range_mul f R L,
      List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_map,
      Nat.mul_comm L R]

end ComposeSim

namespace HybridProtocol

/-! ### Coins of the composed protocol -/

section Coins

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- Alice's composed coin length at `1^n` is `main.P.coins + calls(n)·ρ.P.coins`.
`(H.compose ρ).P.coinLen (List.replicate n true).length = H.main.P.coinLen (List.replicate n
true).length + H.calls.eval n * ρ.P.coinLen (List.replicate n true).length`. -/
theorem composeP_coinLen_eq (n : ℕ) :
    (H.compose ρ).P.coinLen (List.replicate n true).length =
      H.main.P.coinLen (List.replicate n true).length +
        H.calls.eval n * ρ.P.coinLen (List.replicate n true).length := by
  rw [compose_P_coinLen, List.length_replicate]

/-- Bob's composed coin length at `1^n` is `main.V.coins + calls(n)·ρ.V.coins`.
`(H.compose ρ).V.coinLen (List.replicate n true).length = H.main.V.coinLen (List.replicate n
true).length + H.calls.eval n * ρ.V.coinLen (List.replicate n true).length`. -/
theorem composeV_coinLen_eq (n : ℕ) :
    (H.compose ρ).V.coinLen (List.replicate n true).length =
      H.main.V.coinLen (List.replicate n true).length +
        H.calls.eval n * ρ.V.coinLen (List.replicate n true).length := by
  rw [compose_V_coinLen, List.length_replicate]

/-- **The coins of `H.compose ρ` at `1^n`** as the `main`-tapes and one pair of `ρ`-tapes per
call: Alice's tape is her `main`-tape followed by her `ρ`-tapes, Bob's likewise.
`H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) ≃ (H.compose
ρ).ExecCoins (H.compose ρ).P (List.replicate n true)`. -/
def composeCoins (n : ℕ) :
    H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) ≃
      (H.compose ρ).ExecCoins (H.compose ρ).P (List.replicate n true) :=
  ((Equiv.refl (H.Coins n)).prodCongr (Equiv.arrowProdEquivProdArrow _ _ _)).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans
      ((ComposeSim.splitCoins (H.composeP_coinLen_eq ρ n)).prodCongr
        (ComposeSim.splitCoins (H.composeV_coinLen_eq ρ n))))

/-- Alice's composed tape is `splitCoins` of her `main`-tape and her run tapes.
`(H.composeCoins ρ n (m, t)).1 = splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1)`. -/
theorem composeCoins_fst (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    (H.composeCoins ρ n (m, t)).1 =
      ComposeSim.splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1) :=
  rfl

/-- Bob's composed tape is `splitCoins` of his `main`-tape and his run tapes.
`(H.composeCoins ρ n (m, t)).2 = splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2)`. -/
theorem composeCoins_snd (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    (H.composeCoins ρ n (m, t)).2 =
      ComposeSim.splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2) :=
  rfl

/-- Alice's composed tape: `⟦(composeCoins (m, t)).1⟧ = ⟦m.1⟧ ++ ⟦(t 0).1⟧ ++ ⋯`. -/
theorem ofFn_composeCoins_fst (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    List.ofFn (H.composeCoins ρ n (m, t)).1 =
      List.ofFn m.1 ++ (List.ofFn fun j => List.ofFn (t j).1).flatten :=
  ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 fun j => (t j).1

/-- Bob's composed tape: `⟦(composeCoins (m, t)).2⟧ = ⟦m.2⟧ ++ ⟦(t 0).2⟧ ++ ⋯`. -/
theorem ofFn_composeCoins_snd (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    List.ofFn (H.composeCoins ρ n (m, t)).2 =
      List.ofFn m.2 ++ (List.ofFn fun j => List.ofFn (t j).2).flatten :=
  ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 fun j => (t j).2

end Coins

/-! ### The runs of an honest execution -/

section Runs

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Alice's input to call `j`** as a string: `⟦callA(n, zA, rA, j)⟧` for `j < calls(n)`, `[]`
otherwise. -/
def inA (n : ℕ) (zA rA : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else []

/-- The defining equation of `inA`: `inA n zA rA j = ⟦callA(n, zA, rA, j)⟧` for `j < calls(n)`,
`[]` otherwise. -/
theorem inA_eq (n : ℕ) (zA rA : List Bool) (j : ℕ) :
    H.inA n zA rA j =
      if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else [] := rfl

/-- **Bob's input to call `j`** as a string: `⟦callB(n, zB, rB, j)⟧` for `j < calls(n)`, `[]`
otherwise. -/
def inB (n : ℕ) (zB rB : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then List.ofFn (H.callB n zB rB ⟨j, h⟩) else []

/-- The defining equation of `inB`: `inB n zB rB j = ⟦callB(n, zB, rB, j)⟧` for `j < calls(n)`,
`[]` otherwise. -/
theorem inB_eq (n : ℕ) (zB rB : List Bool) (j : ℕ) :
    H.inB n zB rB j =
      if h : j < H.calls.eval n then List.ofFn (H.callB n zB rB ⟨j, h⟩) else [] := rfl

/-- The call inputs do not depend on how the parameter is written:
`N = n → ⟦callA(N, zA, rA, j)⟧ = ⟦callA(n, zA, rA, j)⟧`. -/
theorem ofFn_callA_congr {N n : ℕ} (hN : N = n) (zA rA : List Bool) (j : ℕ)
    (h₁ : j < H.calls.eval N) (h₂ : j < H.calls.eval n) :
    List.ofFn (H.callA N zA rA ⟨j, h₁⟩) = List.ofFn (H.callA n zA rA ⟨j, h₂⟩) := by
  subst hN
  rfl

/-- The call inputs do not depend on how the parameter is written:
`N = n → ⟦callB(N, zB, rB, j)⟧ = ⟦callB(n, zB, rB, j)⟧`. -/
theorem ofFn_callB_congr {N n : ℕ} (hN : N = n) (zB rB : List Bool) (j : ℕ)
    (h₁ : j < H.calls.eval N) (h₂ : j < H.calls.eval n) :
    List.ofFn (H.callB N zB rB ⟨j, h₁⟩) = List.ofFn (H.callB n zB rB ⟨j, h₂⟩) := by
  subst hN
  rfl

/-- **The run inputs of `H.compose ρ` at `1^n` are the call inputs**: for `j < calls(n)`,
`runInputA 1^n zA ⟦(composeCoins (m, t)).1⟧ j = inA n zA ⟦m.1⟧ j`
(`runInputA_of_lt`, `take_ofFn_splitCoins`). -/
theorem runInputA_composeCoins (n : ℕ) (zA : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.runInputA (List.replicate n true) zA (List.ofFn (H.composeCoins ρ n (m, t)).1) j =
      H.inA n zA (List.ofFn m.1) j := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [inA_eq]
  by_cases hj : j < H.calls.eval n
  · have hj' : j < H.calls.eval (List.replicate n true).length := by rw [hN]; exact hj
    rw [dif_pos hj, H.runInputA_of_lt _ _ _ hj', ← Strategy.coinLen_eq,
      composeCoins_fst, take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n)]
    exact H.ofFn_callA_congr hN _ _ j hj' hj
  · rw [dif_neg hj, H.runInputA_of_ge _ _ _ (by rw [hN]; omega)]

/-- Bob's run inputs at `1^n` are his call inputs (as `runInputA_composeCoins`).
`H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j = H.inB n zB
(List.ofFn m.2) j`. -/
theorem runInputB_composeCoins (n : ℕ) (zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j =
      H.inB n zB (List.ofFn m.2) j := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [inB_eq]
  by_cases hj : j < H.calls.eval n
  · have hj' : j < H.calls.eval (List.replicate n true).length := by rw [hN]; exact hj
    rw [dif_pos hj, H.runInputB_of_lt _ _ _ hj', ← Strategy.coinLen_eq,
      composeCoins_snd, take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n)]
    exact H.ofFn_callB_congr hN _ _ j hj' hj
  · rw [dif_neg hj, H.runInputB_of_ge _ _ _ (by rw [hN]; omega)]

/-- **The honest run `j` at `1^n` is `ρ`'s execution on the call inputs and the run tapes**:
`runExec 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ j k = exec ρ.P ρ.V vF 1^n (inA j) (inB j) ⟦(t j).1⟧ ⟦(t j).2⟧ k`
for `c = composeCoins (m, t)` (`runExec_eq`, `runTape_ofFn_splitCoins`). -/
theorem runExec_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : Fin (H.calls.eval n))
    (k : ℕ) :
    H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) j k =
      exec ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2) k := by
  rw [runExec_eq, runInputA_composeCoins, runInputB_composeCoins, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, composeCoins_fst,
    composeCoins_snd,
    runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1) j,
    runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2) j]

/-- The message of `ρ`'s move `p` in the honest run `j` at `1^n` is the move of `ρ`'s execution on
the call inputs and the run tapes (`runMsg_eq`, as `runExec_composeCoins`).
`H.runMsg ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn
(H.composeCoins ρ n (m, t)).2) j p = moveMsg ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA
n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2)
p`. -/
theorem runMsg_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : Fin (H.calls.eval n))
    (p : ℕ) :
    H.runMsg ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) j p =
      moveMsg ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2) p := by
  rw [runMsg_eq, runInputA_composeCoins, runInputB_composeCoins, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, composeCoins_fst,
    composeCoins_snd,
    runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1) j,
    runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2) j]

/-- **Every run gives the ideal answers**: for every call `j`, Alice's and Bob's `ρ`-outputs in
the run on the call inputs and the tapes `t j` are `⟦f_A(callA_j, callB_j)⟧` and
`⟦f_B(callA_j, callB_j)⟧`.
`H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n), ρ.outP (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧ ρ.outV ρ.P (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) j)).2`. -/
def GoodRuns (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) : Prop :=
  ∀ j : Fin (H.calls.eval n),
    ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j)
        (t j) =
      List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧
    ρ.outV ρ.P (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (t j) =
      List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2

/-- The defining property of `GoodRuns` (see `GoodRuns`).
`H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n), ρ.outP (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧ ρ.outV ρ.P (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) j)).2`. -/
theorem goodRuns_iff (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n),
      ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t j) =
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧
      ρ.outV ρ.P (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t j) =
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2 :=
  Iff.rfl

/-- **Under `GoodRuns`, Alice's honest answers are the ideal ones**:
`answersRealA 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ = answersA n zA zB ⟦m.1⟧ ⟦m.2⟧` for `c = composeCoins (m, t)`.

**Proof sketch.** Both are concatenations over the calls `j < L` (`flatten_ofFn_eq_flatMap_range`;
`1^n` has length `n`). Block `j` of the honest answers is `padFin` of Alice's output of the run
on the call inputs and the run tapes (`runInputA_composeCoins`, `runExec_composeCoins`), which is
`ρ.outP` of that run (`Protocol.outP_eq`, `Protocol.transcriptWith_eq`), i.e. `⟦f_A(…)⟧` by
`GoodRuns`; padding a word of the right length is the identity (`ofFn_padFin`,
`padTo_of_length`). -/
theorem answersRealA_eq_answersA (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) :
    H.answersRealA ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) =
      H.answersA n zA zB (List.ofFn m.1) (List.ofFn m.2) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [answersRealA_eq, answersA_eq, flatten_ofFn_eq_flatMap_range (fun j =>
      List.ofFn (padFin (G.outA.eval (List.replicate n true).length)
        (ρ.P.next (List.replicate n true)
          (H.runInputA (List.replicate n true) zA (List.ofFn (H.composeCoins ρ n (m, t)).1) j)
          (runTape (H.main.P.coins.eval (List.replicate n true).length)
            (ρ.P.coins.eval (List.replicate n true).length) j
            (List.ofFn (H.composeCoins ρ n (m, t)).1))
          (H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
            (List.ofFn (H.composeCoins ρ n (m, t)).2) j
            (ρ.rounds.eval (List.replicate n true).length)).1))),
    show (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1
        ).flatten = (List.range (H.calls.eval n)).flatMap fun i => if h : i < H.calls.eval n then
          List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) ⟨i, h⟩)
            (H.callB n zB (List.ofFn m.2) ⟨i, h⟩)).1 else [] by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2])),
    flatMap_range_congr (by rw [hN])]
  refine List.flatMap_congr fun j hj => ?_
  have hjn : j < H.calls.eval n := List.mem_range.1 hj
  rw [dif_pos hjn, runInputA_composeCoins, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq,
    composeCoins_fst, runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1)
      ⟨j, hjn⟩, ← composeCoins_fst, runExec_composeCoins H ρ n zA zB m t ⟨j, hjn⟩,
    ← Protocol.transcriptWith_eq, ← Protocol.outP_eq, (hg ⟨j, hjn⟩).1, ofFn_padFin,
    padTo_of_length (by rw [List.length_ofFn, hN])]

/-- **Under `GoodRuns`, Bob's honest answers are the ideal ones**:
`answersRealB 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ = answersB n zA zB ⟦m.1⟧ ⟦m.2⟧` for `c = composeCoins (m, t)`.

**Proof sketch.** As `answersRealA_eq_answersA`: block `j` of Bob's honest answers is `padFin` of
his output in run `j` on the call inputs and the run tapes (`runInputB_composeCoins`,
`runExec_composeCoins`), which is `ρ.outV` of that run (`Protocol.outV_eq`), i.e. `⟦f_B(…)⟧` by
`GoodRuns`; padding a word of the right length is the identity (`ofFn_padFin`,
`padTo_of_length`). -/
theorem answersRealB_eq_answersB (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) :
    H.answersRealB ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) =
      H.answersB n zA zB (List.ofFn m.1) (List.ofFn m.2) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [answersRealB_eq, answersB_eq, flatten_ofFn_eq_flatMap_range (fun j =>
      List.ofFn (padFin (G.outB.eval (List.replicate n true).length)
        (ρ.V.next (List.replicate n true)
          (H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j)
          (runTape (H.main.V.coins.eval (List.replicate n true).length)
            (ρ.V.coins.eval (List.replicate n true).length) j
            (List.ofFn (H.composeCoins ρ n (m, t)).2))
          (H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
            (List.ofFn (H.composeCoins ρ n (m, t)).2) j
            (ρ.rounds.eval (List.replicate n true).length)).2))),
    show (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2
        ).flatten = (List.range (H.calls.eval n)).flatMap fun i => if h : i < H.calls.eval n then
          List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) ⟨i, h⟩)
            (H.callB n zB (List.ofFn m.2) ⟨i, h⟩)).2 else [] by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2])),
    flatMap_range_congr (by rw [hN])]
  refine List.flatMap_congr fun j hj => ?_
  have hjn : j < H.calls.eval n := List.mem_range.1 hj
  rw [dif_pos hjn, runInputB_composeCoins, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq,
    composeCoins_snd, runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2)
      ⟨j, hjn⟩, ← composeCoins_snd, runExec_composeCoins H ρ n zA zB m t ⟨j, hjn⟩,
    ← Protocol.transcriptWith_eq (π := ρ) (P' := ρ.P), ← Protocol.outV_eq, (hg ⟨j, hjn⟩).2,
    ofFn_padFin, padTo_of_length (by rw [List.length_ofFn, hN])]

/-- **Under `GoodRuns`, the main phase is the hybrid execution on the `main`-tapes**:
`mainExec 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ k = exec main.P main.V vF 1^n (privA n zA zB ⟦m.1⟧ ⟦m.2⟧)
(privB …) ⟦m.1⟧ ⟦m.2⟧ k` (`mainExec_eq`, the answers, `take_ofFn_splitCoins`). -/
theorem mainExec_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) (k : ℕ) :
    H.mainExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) k =
      exec H.main.P H.main.V H.main.verifierFirst (List.replicate n true)
        (H.privA n zA zB (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n zA zB (List.ofFn m.1) (List.ofFn m.2)) (List.ofFn m.1) (List.ofFn m.2) k := by
  rw [mainExec_eq, H.answersRealA_eq_answersA ρ n zA zB m t hg,
    H.answersRealB_eq_answersB ρ n zA zB m t hg, privA_eq, privB_eq, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, composeCoins_fst, composeCoins_snd,
    take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n),
    take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n)]

/-- **Alice's encoded views of the honest runs**: for `j < calls(n)`, her view of `ρ` on the call
inputs `inA j`, `inB j` and the tapes `t j`; `[]` otherwise. -/
def realViewA (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then
    (ρ.viewP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
      (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
  else []

/-- The defining equation of `realViewA` (see `realViewA`).
`H.realViewA ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewP (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
theorem realViewA_eq (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.realViewA ρ n zA zB m t j =
      if h : j < H.calls.eval n then
        (ρ.viewP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
      else [] := rfl

/-- **Bob's encoded views of the honest runs** (as `realViewA`, with `ρ.viewV`).
`H.realViewB ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewV (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
def realViewB (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then
    (ρ.viewV (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
      (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
  else []

/-- The defining equation of `realViewB` (see `realViewB`).
`H.realViewB ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewV (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
theorem realViewB_eq (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.realViewB ρ n zA zB m t j =
      if h : j < H.calls.eval n then
        (ρ.viewV (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
      else [] := rfl

/-- **The real sample of Alice's side under `GoodRuns`**: with `c = composeCoins (m, t)`,
`F.realA (H.compose ρ) n x y c` is the assembled view (`ComposeSim.asmView` with `ρ.P`'s coins,
Bob's moves read, no leading filler) of Alice's real run views, her input, her `main`-tape and
the hybrid main phase, paired with Bob's output in the hybrid execution on the `main`-tapes.

**Proof sketch.** `compose_viewP` and `compose_outV` (with `hM`) give the view and Bob's output.
Her tape is her `main`-tape followed by the run tapes (`ofFn_composeCoins_fst`), which are the
tapes of the run views, of exact length (`padTo_of_length`). Her messages are Bob's run messages
at the pairs, `L` blocks of `R` (`encodeMsgs_eq_flatMap`, `flatMap_range_mul`, `slotFromB_mul_add`),
which are the chunks `segW` of the received messages of the run views (`runExec_composeCoins`,
`exec_eq_map`, `segW_encodeMsgs`), followed by the main phase, the hybrid one under `GoodRuns`
(`mainExec_composeCoins`). -/
theorem realA_compose_eq {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realA (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
          (List.replicate n true) (List.ofFn x) (List.ofFn m.1)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1)
          (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  have hL : H.calls.eval (List.replicate n true).length = H.calls.eval n := by rw [hN]
  -- the tape: the `main`-tape followed by the run tapes
  have htape : List.ofFn (H.composeCoins ρ n (m, t)).1 = List.ofFn m.1 ++
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        padTo (ρ.P.coins.eval (List.replicate n true).length)
          (pairFstD (pairSndD (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    have hT0 : (List.ofFn fun j => List.ofFn (t j).1).flatten =
        (List.range (H.calls.eval n)).flatMap fun j =>
          if h : j < H.calls.eval n then List.ofFn (t ⟨j, h⟩).1 else [] := by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2]))
    rw [ofFn_composeCoins_fst, hT0, flatMap_range_congr hL.symm]
    congr 1
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [dif_pos hjn, realViewA_eq, dif_pos hjn, Protocol.viewP_eq, View.encode_mk,
      pairSndD_pairEncode, pairFstD_pairEncode, padTo_of_length (by
        rw [List.length_ofFn, Strategy.coinLen_eq])]
  -- Bob's run messages at the pairs: the chunks of the received messages of Alice's run views
  have hmsgs : Strategy.encodeMsgs ((List.range (H.calls.eval (List.replicate n true).length *
      ρ.rounds.eval (List.replicate n true).length)).map
        (H.slotFromB ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
          (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn (H.composeCoins ρ n (m, t)).2))) =
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        segW ρ.verifierFirst true (ρ.rounds.eval (List.replicate n true).length)
          (pairSndD (pairSndD (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    rw [encodeMsgs_eq_flatMap, List.flatMap_map, flatMap_range_mul]
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [realViewA_eq, dif_pos hjn, Protocol.viewP_eq, View.encode_mk, pairSndD_pairEncode,
      pairSndD_pairEncode, Protocol.transcriptWith_eq, exec_eq_map,
      show (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (moverIsV ρ.verifierFirst) =
        (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun q => moverIsV ρ.verifierFirst q == true) from
        List.filter_congr fun q _ => (beq_true _).symm, segW_encodeMsgs]
    refine List.flatMap_congr fun p hp => ?_
    rw [slotFromB_mul_add H ρ _ _ _ _ _ (List.mem_range.1 hp), beq_true,
      runMsg_composeCoins H ρ n _ _ m t ⟨j, hjn⟩ p]
  have hmain := H.mainExec_composeCoins ρ n (List.ofFn x) (List.ofFn y) m t hg
    (H.main.rounds.eval (List.replicate n true).length)
  rw [Functionality.realA_eq, compose_viewP, compose_outV H ρ _ _ _ _ (hM _), View.encode_mk,
    asmView_eq, encodeMsgs_append, hmsgs, hmain, H.answersRealB_eq_answersB ρ n _ _ m t hg, htape,
    List.replicate_zero, Strategy.encodeMsgs_nil, List.append_nil,
    Protocol.transcript_eq_transcriptWith, Protocol.transcriptWith_eq, Protocol.outV_eq,
    Protocol.transcriptWith_eq, privB_eq, ← Strategy.coinLen_eq H.main.V, composeCoins_snd,
    take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n), ← privB_eq]

/-- **The real sample of Bob's side under `GoodRuns`**: with `c = composeCoins (m, t)`,
`F.realB (H.compose ρ) n x y c` is the assembled view (`ComposeSim.asmView` with `ρ.V`'s coins,
Alice's moves read, `lead` leading fillers) of Bob's real run views, his input, his `main`-tape
and the hybrid main phase, paired with Alice's output in the hybrid execution.

**Proof sketch.** As `realA_compose_eq`, with `compose_viewV`, `compose_outP`, the second
components, `slotFromA_mul_add` and the leading fillers between the runs and the main phase. -/
theorem realB_compose_eq {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realB (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
          (List.replicate n true) (List.ofFn y) (List.ofFn m.2)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2)
          (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  have hL : H.calls.eval (List.replicate n true).length = H.calls.eval n := by rw [hN]
  -- the tape: the `main`-tape followed by the run tapes
  have htape : List.ofFn (H.composeCoins ρ n (m, t)).2 = List.ofFn m.2 ++
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        padTo (ρ.V.coins.eval (List.replicate n true).length)
          (pairFstD (pairSndD (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    have hT0 : (List.ofFn fun j => List.ofFn (t j).2).flatten =
        (List.range (H.calls.eval n)).flatMap fun j =>
          if h : j < H.calls.eval n then List.ofFn (t ⟨j, h⟩).2 else [] := by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2]))
    rw [ofFn_composeCoins_snd, hT0, flatMap_range_congr hL.symm]
    congr 1
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [dif_pos hjn, realViewB_eq, dif_pos hjn, Protocol.viewV_eq, View.encode_mk,
      pairSndD_pairEncode, pairFstD_pairEncode, padTo_of_length (by
        rw [List.length_ofFn, Strategy.coinLen_eq])]
  -- Alice's run messages at the pairs: the chunks of the received messages of Bob's run views
  have hmsgs : Strategy.encodeMsgs ((List.range (H.calls.eval (List.replicate n true).length *
      ρ.rounds.eval (List.replicate n true).length)).map
        (H.slotFromA ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
          (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn (H.composeCoins ρ n (m, t)).2))) =
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        segW ρ.verifierFirst false (ρ.rounds.eval (List.replicate n true).length)
          (pairSndD (pairSndD (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    rw [encodeMsgs_eq_flatMap, List.flatMap_map, flatMap_range_mul]
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [realViewB_eq, dif_pos hjn, Protocol.viewV_eq, View.encode_mk, pairSndD_pairEncode,
      pairSndD_pairEncode, Protocol.transcriptWith_eq, exec_eq_map,
      show (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun i => !moverIsV ρ.verifierFirst i) =
        (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun q => moverIsV ρ.verifierFirst q == false) from
        List.filter_congr fun q _ => (beq_false _).symm, segW_encodeMsgs]
    refine List.flatMap_congr fun p hp => ?_
    rw [slotFromA_mul_add H ρ _ _ _ _ _ (List.mem_range.1 hp),
      runMsg_composeCoins H ρ n _ _ m t ⟨j, hjn⟩ p]
    cases moverIsV ρ.verifierFirst p <;> rfl
  have hmain := H.mainExec_composeCoins ρ n (List.ofFn x) (List.ofFn y) m t hg
    (H.main.rounds.eval (List.replicate n true).length)
  rw [Functionality.realB_eq, compose_viewV, compose_outP H ρ _ _ _ _ (hM _), View.encode_mk,
    asmView_eq, encodeMsgs_append, encodeMsgs_append, hmsgs, hmain,
    H.answersRealA_eq_answersA ρ n _ _ m t hg, htape, Protocol.transcript_eq_transcriptWith,
    Protocol.transcriptWith_eq, Protocol.outP_eq, Protocol.transcriptWith_eq, privA_eq,
    ← Strategy.coinLen_eq H.main.P, composeCoins_fst,
    take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n), ← privA_eq]

end Runs

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
