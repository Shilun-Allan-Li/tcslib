/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.MachineSpec
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Nonabort
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Realizing the planted Lamport experiment as a machine

## Main definitions

* `machineForger`: a machine forger on a typed public-key table, with budget one.

## Main results

* `exists_realization_machine`: T1 realizes every nonaborting successful planted transcript
  by an actual machine output, with an explicit uniform coin equivalence.

The generator, signer, evaluator, and fixed-width block reader are parameters. Their
functional contracts are assumptions about algorithms, rather than additional hardness
assumptions. The owned Lamport module discharges them from its published readers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity Turing TCSlib.Cryptography.Games
open TCSlib.Cryptography

/-- Run a machine forger on the serialized typed public table, using the canonical
message/signature codec and a budget of one signing query. -/
def machineForger (L : PolyExpr) (A : NUPPT) (n : ℕ)
    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))
      (Fin (n + n * n) → Bool) :=
  A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
    n 1 (publicWord Y) r

/-- The typed machine forger is `A.toCompOn` on the serialized public table. -/
theorem machineForger_eq (L : PolyExpr) (A : NUPPT) (n : ℕ)
    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
    machineForger L A n Y r =
      A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
        n 1 (publicWord Y) r := rfl

/-- Every typed machine-forger tree has unit-query cost at most one. -/
theorem machineForger_cost (L : PolyExpr) (A : NUPPT) (n : ℕ)
    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
    (machineForger L A n Y r).CostBoundedBy (fun _ => 1) 1 := by
  rw [machineForger_eq]
  exact A.toCompOn_costBoundedBy _ _ _ _ _

/-- The planted experiment's successful nonaborting outputs are actual inverter outputs.
The machine uses one fair seed bit, one random table, and the forger's own random tape.
[PS10, machine-realization step in the proof of Theorem 137.2].

**Proof sketch.** T1 gives a machine for the polynomial-time planting handler. Reindex its
seed by the public seed/table equivalence. On a successful planted transcript the final
abort flag is false, so its sole query was safe. A return needs no oracle call; a safe query
has the ordinary sampled-table signature and leaves the false handler state unchanged.
The remaining tree has cost zero and is a return. Thus the handler simulation and the
typed planted simulation have the same output. T1's output equation and the public
nonabort-extraction contract identify the actual machine output with that signature block. -/
theorem exists_realization_machine
    (L W : PolyExpr)
    (f : ∀ n, (Fin n → Bool) → Fin (L.eval n) → Bool)
    (E G S : List Bool → List Bool)
    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S)
    (hW : ∀ n, W.eval n = 6 * L.eval n + 6)
    (hEval : ∀ n (x : Fin n → Bool),
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x))
    (hGen : ∀ n (T : Table n),
      G (NUPPT.layout (List.replicate n true) [] [] (secretWord T)) =
        pairEncode (publicWord (tablePublic (f n) T)) (secretWord T))
    (hSign : ∀ n (T : Table n) (m : Fin n → Bool),
      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (tableSignature T m))
    (hcoin : ∀ {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
      (i : Fin q), coinBlock B i (List.ofFn g).flatten = g i)
    (A : NUPPT) :
    ∃ B : NUPPT, ∀ n,
      ∃ φ : ((Bool × Table n) × A.Coins n) ≃ B.Coins n,
        ∀ (i : Fin n) (y : Fin (L.eval n) → Bool) (T : Table n) (c : Bool) (r : A.Coins n),
          RedSuccess (f n) (machineForger L A n) y T r (i, c) →
            ∃ x' : Fin n → Bool,
              B.runAt n (pairEncode (List.ofFn y) (List.replicate i.val true))
                  (φ ((c, T), r)) = List.ofFn x' ∧
                f n x' = y := by
  let H := LamportMachine.handler W E G S hE hG hS
  obtain ⟨B, hB⟩ := exists_handlerMachine A (.const 1)
    (fun _ : Fin 1 => PolyExpr.var) (fun _ => PolyExpr.mul .var .var)
    (.add .var (.mul .var .var)) H
  refine ⟨B, fun n => ?_⟩
  obtain ⟨ψ, hψ⟩ := hB n
  have hseed : H.seedLen.eval n = 1 + 2 * n * n := by
    simp only [H, LamportMachine.handler_seedLen, PolyExpr.eval_add, PolyExpr.eval_const,
      PolyExpr.eval_mul, PolyExpr.eval_var]
  have hstate : H.stateLen.eval n = 1 := by
    simp only [H, LamportMachine.handler_stateLen, PolyExpr.eval_const]
  let toSeed : (Bool × Table n) ≃ (Fin (H.seedLen.eval n) → Bool) :=
    (seedCoins n).symm.trans
      (Equiv.arrowCongr (finCongr hseed.symm) (Equiv.refl Bool))
  let φ : ((Bool × Table n) × A.Coins n) ≃ B.Coins n :=
    (toSeed.prodCongr (Equiv.refl (A.Coins n))).trans ψ
  refine ⟨φ, fun i y T c r hred => ?_⟩
  let z := pairEncode (List.ofFn y) (List.replicate i.val true)
  let ω := toSeed (c, T)
  have hω : List.ofFn ω = c :: secretWord T := by
    change List.ofFn ((Equiv.arrowCongr (finCongr hseed.symm) (Equiv.refl Bool))
      ((seedCoins n).symm (c, T))) = c :: secretWord T
    rw [ofFn_arrowCongr_finCongr, ofFn_seedCoins_symm]
  have hinit : H.init n = fun _ => false := by
    funext j
    exact LamportMachine.handler_init W E G S hE hG hS n j
  have hinitWord : List.ofFn (H.init n) = [false] := by
    rw [hinit, List.ofFn_const, hstate]
    rfl
  have hadv : H.advInput n z ω = publicWord (plantedPublic (f n) T i c y) := by
    simp only [PolyHandler.advInput_eq, H, LamportMachine.handler_advIn, hω, z]
    exact advIn_context hcoin W (hW n) (f n) E G (hEval n) (hGen n) T i c y
  let tree := machineForger L A n (plantedPublic (f n) T i c y) r
  have hcost : tree.CostBoundedBy (fun _ => 1) 1 := machineForger_cost L A n _ r
  obtain ⟨a₀, habort, hinverts⟩ := (redSuccess_iff (f n) (machineForger L A n) y T r (i, c)).1 hred
  change simulate (abortingImpl T i c) tree false = .pure (a₀, false) at habort
  have hsafe : Safe tree i c := safe_of_nonabort T i c tree hcost a₀ habort
  have hrunread : H.run = LamportMachine.run S :=
    LamportMachine.handler_run W E G S hE hG hS
  have hcall : ∀ (j : Fin 1) (m : Fin n → Bool), m i ≠ c →
      H.impl n z ω j m (H.init n) = .pure (tableSignature T m, H.init n) := by
    intro j m hm
    rw [PolyHandler.impl_apply]
    apply congrArg OracleComp.pure
    apply PolyHandler.answer_of_run_eq H
    simp only [hrunread, hω, hinitWord]
    simpa only [z] using run_safe S (hSign n) T i c (List.ofFn y) j m hm
  have hsim : simulate (H.impl n z ω) tree (H.init n) = .pure (a₀, H.init n) := by
    cases tree with
    | pure a =>
      have hp : (a, false) = (a₀, false) :=
        OracleComp.pure.inj (by simpa only [simulate_pure] using habort)
      rw [simulate_pure, congrArg Prod.fst hp]
    | query j m k =>
      have hm : m i ≠ c := (safe_iff _ i c).1 hsafe m (firstQuery_query j m k)
      have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
      obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (tableSignature T m))
        (by simpa only [Nat.sub_self] using hk.2 (tableSignature T m))
      have hp : (a, false) = (a₀, false) := OracleComp.pure.inj (by
        simpa only [simulate_query, abortingImpl_apply, abortingAnswer_eq, if_neg hm,
          hm, decide_false, Bool.false_or, OracleComp.pure_bind, ha, simulate_pure] using habort)
      rw [simulate_query, hcall j m hm, OracleComp.pure_bind, ha, simulate_pure,
        congrArg Prod.fst hp]
  obtain ⟨a, s, hsimulation, houtput⟩ := hψ z ω r
  have hsimulation' : simulate (H.impl n z ω) tree (H.init n) = .pure (a, s) := by
    simpa only [PolyExpr.eval_const, PolyExpr.eval_var, PolyExpr.eval_mul, PolyExpr.eval_add,
      hadv, tree, machineForger_eq] using hsimulation
  have hp : (a, s) = (a₀, H.init n) :=
    OracleComp.pure.inj (hsimulation'.symm.trans hsim)
  have ha : a = a₀ := congrArg Prod.fst hp
  have hs : s = H.init n := congrArg Prod.snd hp
  rw [ha, hs] at houtput
  have hresult : H.result n z ω (H.init n) a₀ =
      List.ofFn (signatureBlock (splitBits a₀).2 i) := by
    rw [PolyHandler.result_eq, show H.out = LamportMachine.out from
      LamportMachine.handler_out W E G S hE hG hS, hω, hinitWord]
    apply out_nonabort i z (c :: secretWord T) a₀
    simpa only [z] using LamportMachine.pos_seedIn n (List.ofFn y)
      (List.replicate i.val true) (c :: secretWord T)
  refine ⟨signatureBlock (splitBits a₀).2 i, ?_, hinverts⟩
  change B.runAt n z (ψ (ω, r)) = List.ofFn (signatureBlock (splitBits a₀).2 i)
  exact houtput.trans hresult

end TCSlib.Cryptography.Authentication.LamportFill
