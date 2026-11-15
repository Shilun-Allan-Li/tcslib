/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The distinguisher of the PRF-MAC reduction

Steps 2, 3 and 6 of the proof of [PS10, Theorem 135.4], for a forger with `ℓ(n)`-bit messages and
`t(n)`-bit tags: T2 (`Games.exists_interactiveHandlerMachine`) applied to the handler `macHandler`
(through the input-free companion `Games.exists_toCompOn_of_toComp`), then T4
(`Games.exists_toOracleAdversary_of_bitCodec`), give a next-query machine `D` whose acceptance
probability against any function `f` is the probability that the forger forges against the
tagging oracle `f`: its output `(m, σ)` has `f m = σ` and `m` was never queried
(`exists_macReduction`).

The proof answers the handler's outer queries by `f` (`fnImpl`, `simulate_ofComp_pure`) and composes
the two implementations (`simulate_comp`). From the encoded state of the queried messages, newest
first (`queried`), each composed call is the logged call of `fnImpl f` with the new state abstracted
(`macHandler_impl`); the forger asks at most `q(n)` queries, so this holds along every run
(`Games.simulate_eq_of_abs_bounded`), and the log of every run has at most `q(n)` entries
(`allOutputs_simulate_withLog_length`). The finalization then tests exactly the forgery
(`macHandler_finish`).

## Main definitions

* `PRFMAC.fnImpl f`: the tagging oracle of the function `f`.
* `PRFMAC.FnForge f a log`: the output `a = (m, σ)` is a forgery against `f` given the log.
* `PRFMAC.queried log`: the queried messages of a log, newest first.
* `PRFMAC.macBudget q`: the distinguisher's query budget `q · 1 + 1`.

## Main results

* `PRFMAC.allOutputs_simulate_withLog_length`: the log of a run grows by at most its query count.
* `PRFMAC.exists_macReduction`: the distinguisher (checkpoint 1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 135.4 (book p. 135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
open TCSlib.Cryptography.Composability.ChallengeSim (expect_sample_prod)

/-! ### The tagging oracle of a function and forgeries against it -/

section Fn

variable {a b : ℕ}

/-- **The tagging oracle of the function `f`**: each query `m` is answered `f m`, the state kept:
`fnImpl f = QueryImpl.ofComp fun _ m => pure (f m)`. -/
def fnImpl (f : (Fin a → Bool) → (Fin b → Bool)) :
    QueryImpl (bitSpec (fun _ : Fin 1 => a) (fun _ => b)) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => .pure (f m)

/-- `fnImpl f = QueryImpl.ofComp fun _ m => pure (f m)`. -/
theorem fnImpl_eq (f : (Fin a → Bool) → (Fin b → Bool)) :
    fnImpl f = QueryImpl.ofComp fun _ m => .pure (f m) :=
  rfl

/-- The tagging oracle of `f` answers `f x`: `fnImpl f i x s = pure (f x, s)`. -/
theorem fnImpl_apply (f : (Fin a → Bool) → (Fin b → Bool)) (i : Fin 1) (x : Fin a → Bool)
    (s : Unit) : fnImpl f i x s = .pure (f x, s) := by
  rw [fnImpl_eq, QueryImpl.ofComp_apply, OracleComp.pure_bind]

/-- **A forgery against `f`** [PS10, Definition 134.2]: the output `w = (m, σ)` (`splitBits`) has
`f m = σ` and `m` is the message of no entry of the log:
`FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1`. -/
def FnForge (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : Prop :=
  f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1

/-- `FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1`.
-/
theorem fnForge_iff (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
    FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1 :=
  Iff.rfl

/-- Forgeries are decidable, as the conjunction they unfold to (`fnForge_iff`):
`Decidable (FnForge f w log)` from `f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, …`. -/
instance (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : Decidable (FnForge f w log) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The queried messages of a log**, newest first: `queried log = (log.map (·.2.1)).reverse`. -/
def queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : List (Fin a → Bool) :=
  (log.map fun e => e.2.1).reverse

/-- `queried log = (log.map (·.2.1)).reverse`. -/
theorem queried_eq (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
    queried log = (log.map fun e => e.2.1).reverse :=
  rfl

/-- `queried [] = []`. -/
theorem queried_nil : queried ([] : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) = [] :=
  rfl

/-- A new entry is the newest message: `queried (log ++ [e]) = e.2.1 :: queried log`. -/
theorem queried_append (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
    (e : Σ i, (bitSpec (fun _ : Fin 1 => a) (fun _ => b)).dom i ×
      (bitSpec (fun _ : Fin 1 => a) (fun _ => b)).rng i) :
    queried (log ++ [e]) = e.2.1 :: queried log := by
  rw [queried_eq, queried_eq, List.map_append, List.reverse_append, List.map_singleton,
    List.reverse_singleton, List.singleton_append]

/-- `|queried log| = |log|`. -/
theorem length_queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
    (queried log).length = log.length := by
  rw [queried_eq, List.length_reverse, List.length_map]

/-- `m ∈ queried log ↔ ∃ e ∈ log, e.2.1 = m`. -/
theorem mem_queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
    (m : Fin a → Bool) : m ∈ queried log ↔ ∃ e ∈ log, e.2.1 = m := by
  rw [queried_eq, List.mem_reverse, List.mem_map]

/-- **A forgery read on lists:** for an output `w` of `a + b` bits, the list test of the
finalization is the forgery: `(decide (⟦f (padFin a (⟦w⟧.take a))⟧ = ⟦w⟧.drop a) &&
decide (∀ m ∈ queried log, ⟦m⟧ ≠ ⟦w⟧.take a)) = decide (FnForge f w log)`.

**Proof sketch.** `⟦w⟧ = ⟦m⟧ ++ ⟦σ⟧` for `(m, σ) = splitBits w` (`Fin.append_castAdd_natAdd`,
`List.ofFn_fin_append`), so the first `a` bits are `⟦m⟧` and the rest `⟦σ⟧`; `List.ofFn` is
injective, and `queried` lists the logged messages (`mem_queried`). -/
theorem decide_fnForge (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
    (decide (List.ofFn (f (padFin a ((List.ofFn w).take a))) = (List.ofFn w).drop a) &&
      decide (∀ m ∈ queried log, List.ofFn m ≠ (List.ofFn w).take a)) =
      decide (FnForge f w log) := by
  have hw : List.ofFn w = List.ofFn (splitBits w).1 ++ List.ofFn (splitBits w).2 := by
    rw [← List.ofFn_fin_append,
      show (splitBits w).1 = fun i => w (Fin.castAdd b i) from funext (splitBits_fst w),
      show (splitBits w).2 = fun j => w (Fin.natAdd a j) from funext (splitBits_snd w),
      Fin.append_castAdd_natAdd]
  have htake : (List.ofFn w).take a = List.ofFn (splitBits w).1 := by
    rw [hw, List.take_left' List.length_ofFn]
  have hdrop : (List.ofFn w).drop a = List.ofFn (splitBits w).2 := by
    rw [hw, List.drop_left' List.length_ofFn]
  rw [htake, hdrop, padFin_ofFn, ← Bool.decide_and]
  refine decide_eq_decide.2 ?_
  rw [fnForge_iff]
  refine and_congr List.ofFn_inj ⟨fun h e he hm => h e.2.1 ((mem_queried log _).2 ⟨e, he, rfl⟩)
    (by rw [hm]), fun h m hm hl => ?_⟩
  obtain ⟨e, he, rfl⟩ := (mem_queried log m).1 hm
  exact h e he (List.ofFn_inj.1 hl)

end Fn

/-- **The log of a run grows by at most its query count:** for a computation making at most `m`
queries, every output of the logged simulation from `(s, log)` has a log of at most `|log| + m`
entries: `(simulate impl.withLog c (s, log)).AllOutputs fun p => |p.2.2| ≤ |log| + m`.

**Proof sketch.** Induction on `c`: a return keeps the log; a query appends one entry
(`QueryImpl.withLog_apply`) and leaves at most `m - 1` queries (`OracleComp.costBoundedBy_query`).
-/
theorem allOutputs_simulate_withLog_length {ι ι' : Type} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} {σ α : Type} (impl : QueryImpl spec σ spec') (c : OracleComp spec α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ) (log : QueryLog spec) :
    (simulate impl.withLog c (s, log)).AllOutputs fun p => p.2.2.length ≤ log.length + m := by
  induction c generalizing m s log with
  | pure a =>
    rw [simulate_pure, OracleComp.allOutputs_pure]
    exact Nat.le_add_right _ _
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    rw [simulate_query, QueryImpl.withLog_apply, OracleComp.bind_assoc]
    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun ys _ => ?_
    rw [OracleComp.pure_bind]
    refine OracleComp.AllOutputs.mono (fun p hp => ?_) (ih ys.1 (m - 1) (hk ys.1) ys.2 _)
    dsimp only at hp
    rw [List.length_append, List.length_singleton] at hp
    omega

/-- The distinguisher's query budget, `q` forwarded queries and one final query:
`macBudget q = q · 1 + 1`. -/
def macBudget (q : PolyExpr) : PolyExpr := .add (.mul q (.const 1)) (.const 1)

/-- `(macBudget q).eval n = q(n) · 1 + 1`, with the constants read by `PolyExpr.eval`. -/
theorem macBudget_eval (q : PolyExpr) (n : ℕ) :
    (macBudget q).eval n = q.eval n * (PolyExpr.const 1).eval n + (PolyExpr.const 1).eval n := by
  rw [macBudget, PolyExpr.eval_add, PolyExpr.eval_mul]

/-! ### The reduction -/

/-- **The PRF-MAC distinguisher** [PS10, Theorem 135.4, proof, steps 2–3]: for a forger `A` with
budget `q`, `ℓ(n)`-bit messages and `t(n)`-bit tags, there is a next-query machine `D` such that
at every `n` and for every function `f : {0,1}^ℓ(n) → {0,1}^t(n)`, `D` with budget `q · 1 + 1`
accepts against `f` with the probability that `A` forges against the tagging oracle `f`:
`𝔼_c [D^f(c) = 1] = 𝔼_r Pr[FnForge f | simulate (fnImpl f).withLog (A.toComp … r) ((), [])]`.

**Proof sketch.** `D` is T4 applied to T2's machine `B` for `macHandler q ℓ t` and the input-free
companion `A'` of `A`. Its coins are, through the bijections of T4, T2 and the companion, an empty
seed `ω` and `A`'s coins `r` (`expect_sample_equiv`, `ChallengeSim.expect_sample_prod`,
`expect_sample_comm`); the run does not read `ω` (`expect_const`). For fixed `ω` and `r`, T4 and
T2 turn `D`'s run against `f` into the evaluation of the reduction with `f`
(`PRFGame.ofFn_evalFn_toCompOn`), which is its simulation with `fnImpl f`
(`simulate_ofComp_pure`), composed with the handler (`simulate_bind`, `simulate_comp`). Along
`A`'s run (at most `q(n)` queries) the composite is the logged `fnImpl f` with the state
abstracted to the encoded queried messages (`simulate_eq_of_abs_bounded`, `macHandler_impl`). Every
final log has at most `q(n)` entries (`allOutputs_simulate_withLog_length`), so the finalization
asks `f` at `m*` and tests `f m* = σ*` and freshness (`macHandler_finish`), which is `FnForge` on
lists (`decide_fnForge`) after transporting the output width (`expect_toCompOn_outLen`). -/
theorem exists_macReduction (ℓ t q : PolyExpr) (A : NUPPT) :
    ∃ D : NUPPT, ∀ (n : ℕ) (f : (Fin (ℓ.eval n) → Bool) → (Fin (t.eval n) → Bool)),
      expect (ProbComp.sample (D.Coins n))
          (fun c => if (D.toOracleAdversary n (ℓ.eval n) (t.eval n) ((macBudget q).eval n) c).eval
            f = true then (1 : ℝ) else 0) =
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (simulate (fnImpl f).withLog
              (A.toComp (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
                (ℓ.eval n + t.eval n)) n (q.eval n) r) ((), []))
            (fun res => if FnForge f res.1 res.2.2 then (1 : ℝ) else 0) := by
  obtain ⟨A', -, hA'⟩ := exists_toCompOn_of_toComp A
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A' q (fun _ => ℓ) (fun _ => t)
    (fun _ => ℓ) (fun _ => t) (.add ℓ t) (macHandler q ℓ t)
  obtain ⟨D, -, hD⟩ := exists_toOracleAdversary_of_bitCodec B ℓ t
  refine ⟨D, fun n f => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA' n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  obtain ⟨φ₄, hφ₄⟩ := hD n
  have hQ : q.eval n * (macHandler q ℓ t).perCall.eval n + (macHandler q ℓ t).finCall.eval n =
      (macBudget q).eval n := by
    rw [macHandler_perCall, macHandler_finCall, macBudget_eval]
  have hout : (macHandler q ℓ t).outLen.eval n = 1 := by
    rw [macHandler_outLen, PolyExpr.eval_const]
  have hd : (PolyExpr.add ℓ t).eval n = ℓ.eval n + t.eval n := PolyExpr.eval_add ℓ t n
  -- `D`'s coins are a seed and `A`'s coins.
  rw [← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂, expect_sample_prod,
    expect_sample_comm, ← expect_sample_equiv φ₀]
  refine congrArg _ (funext fun r => ?_)
  have key : ∀ g : Fin 1 → Bool, (if g 0 = true then (1 : ℝ) else 0) =
      if (List.ofFn g).headD false = true then 1 else 0 := fun g => by rw [headD_ofFn_one]
  -- One run of `D` is the forgery test of `A`'s run against `fnImpl f`.
  have hrun : ∀ ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool,
      (if (D.toOracleAdversary n (ℓ.eval n) (t.eval n) ((macBudget q).eval n)
          (φ₄ (φ₂ (ω, φ₀ r)))).eval f = true then (1 : ℝ) else 0) =
        expect (simulate (fnImpl f).withLog
            (A.toComp (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
              (ℓ.eval n + t.eval n)) n (q.eval n) r) ((), []))
          (fun res => if FnForge f res.1 res.2.2 then (1 : ℝ) else 0) := by
    intro ω
    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
        ((macHandler q ℓ t).outLen.eval n)) n
        (q.eval n * (macHandler q ℓ t).perCall.eval n + (macHandler q ℓ t).finCall.eval n)
        [] (φ₂ (ω, φ₀ r)) := hφ₂ [] ω (φ₀ r)
    rw [hφ₄, ← hQ, key, Composability.PRFGame.ofFn_evalFn_toCompOn hout.symm B n _ []
      (φ₂ (ω, φ₀ r)), ← h2]
    set c' := A'.toCompOn (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
      ((PolyExpr.add ℓ t).eval n)) n (q.eval n) ((macHandler q ℓ t).advInput n [] ω) (φ₀ r)
      with hc'
    -- The evaluation with `f` is the simulation with `fnImpl f`.
    have hev := simulate_ofComp_pure (σ := Unit) (spec' := unifSpec)
      (fun (_ : Fin 1) (x : Fin (ℓ.eval n) → Bool) => f x)
      ((simulate ((macHandler q ℓ t).impl n [] ω) c' ((macHandler q ℓ t).init n)).bind
        (fun res => (macHandler q ℓ t).finish n [] ω res.2 res.1)) ()
    rw [← fnImpl_eq] at hev
    have h1 := congrArg (fun c => expect c
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
    simp only [expect_pure] at h1
    refine h1.symm.trans ?_
    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind]
    -- The composed calls are the logged calls of `fnImpl f`, the state abstracted.
    have hstep : ∀ (i : Fin 1) (x : Fin (ℓ.eval n) → Bool)
        (s : Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n))),
        s.2.length < q.eval n →
        ∃ (y : Fin (t.eval n) → Bool)
          (s' : Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n))),
          (fnImpl f).withLog i x s = .pure (y, s') ∧ s'.2.length ≤ s.2.length + 1 ∧
          (fnImpl f).comp ((macHandler q ℓ t).impl n [] ω) i x
              (macState q ℓ t n (queried s.2), ()) =
            .pure (y, (macState q ℓ t n (queried s'.2), ())) := by
      intro i x s hs
      refine ⟨f x, ((), s.2 ++ [⟨i, x, f x⟩]), ?_, by
        rw [List.length_append, List.length_singleton], ?_⟩
      · rw [QueryImpl.withLog_apply, fnImpl_apply, OracleComp.pure_bind]
      · rw [QueryImpl.comp_apply]
        dsimp only
        rw [macHandler_impl q ℓ t n [] ω i x _ (by rwa [length_queried])]
        simp only [simulate_query, fnImpl_apply, OracleComp.pure_bind, simulate_pure,
          queried_append]
    have hinit : (macHandler q ℓ t).init n = macState q ℓ t n
        (queried ([] : QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)))) := by
      rw [macHandler_init_eq, queried_nil]
    have hcost := A'.toCompOn_costBoundedBy (bitCodec (fun _ : Fin 1 => ℓ.eval n)
      (fun _ => t.eval n) ((PolyExpr.add ℓ t).eval n)) n (q.eval n)
      ((macHandler q ℓ t).advInput n [] ω) (φ₀ r)
    rw [hinit, simulate_eq_of_abs_bounded ((fnImpl f).comp ((macHandler q ℓ t).impl n [] ω))
      (fnImpl f).withLog (fun s => (macState q ℓ t n (queried s.2), ())) (fun s => s.2.length)
      (q.eval n) hstep c' (q.eval n) hcost ((), []) (Nat.zero_add _).le,
      expect_bind]
    simp only [expect_pure]
    -- The finalization tests the forgery, on lists.
    let G : List Bool × (Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n)
        (fun _ => t.eval n))) → ℝ := fun p =>
      if (decide (List.ofFn (f (padFin (ℓ.eval n) (p.1.take (ℓ.eval n)))) =
          p.1.drop (ℓ.eval n)) &&
        decide (∀ m ∈ queried p.2.2, List.ofFn m ≠ p.1.take (ℓ.eval n))) = true
      then (1 : ℝ) else 0
    have hall := allOutputs_simulate_withLog_length (fnImpl f) c' (q.eval n) hcost () []
    rw [expect_congr_of_allOutputs hall (g := fun p => G (List.ofFn p.1, p.2)) fun p hp => ?_]
    · rw [expect_toCompOn_outLen (fnImpl f).withLog A' n (q.eval n) _ (φ₀ r) ((), []) hd G, hφ₀]
      refine congrArg _ (funext fun p => ?_)
      show (if _ = true then (1 : ℝ) else 0) = _
      rw [decide_fnForge]
      exact if_congr decide_eq_true_iff rfl rfl
    · rw [List.length_nil, Nat.zero_add] at hp
      rw [macHandler_finish q ℓ t n [] ω (queried p.2.2) (by rwa [length_queried]) p.1
        (by rw [hd]; omega)]
      simp only [simulate_query, fnImpl_apply, OracleComp.pure_bind, simulate_pure, expect_pure]
      rw [ofFn_padFin_of_length (by rw [List.length_singleton, hout]), List.headD_cons]
  simp only [hrun]
  exact expect_const _ _

end TCSlib.Cryptography.Authentication.PRFMAC
