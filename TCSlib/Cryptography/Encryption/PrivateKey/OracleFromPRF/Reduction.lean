/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The PRF reduction for the §3.9 scheme

The reduction of [PS10, Theorem 168.2], step 1, as a next-query oracle machine: T2
(`Games.exists_interactiveHandlerMachine`) applied to the handler `pkHandler` (through the
input-free companion `Games.exists_toCompOn_of_toComp`), then T4
(`Games.exists_toOracleAdversary_of_bitCodec`). Its acceptance probability against any function
`f` is the acceptance probability of the IND experiment with `f` in place of `f_k`
(`exists_prfReduction`).

The proof answers the handler's outer queries by `f` (`fOuter`) and composes the two
implementations (`QueryImpl.comp`). Each composed call, from the encoded state `pkState j o`, is
the call of `eImpl` from `(j, o)` with the handler's tapes in advance (`comp_pkAbs`), as long as
`j` is below the number `q(n)` of tapes; the adversary asks at most `q(n)` queries, so this holds
along every run (`simulate_eq_of_abs_bounded`). Drawing the seed uniformly then gives fresh
nonces (`PRFGame.expect_eImpl`).

## Main definitions

* `PRFGame.fOuter`: the outer oracle answering with `f`.
* `PRFGame.atkOf`: the attack of the attack bit.
* `PRFGame.qRed`: the reduction's query budget.

## Main results

* `PRFGame.simulate_eq_of_abs_bounded`: simulation through a state abstraction along runs with a
  query budget.
* `PRFGame.exists_prfReduction`: the reduction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 168.2 (book p. 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-! ### Simulation through a state abstraction along bounded runs -/

/-- **Simulation through a state abstraction, along runs with a query budget:** let every call of
`impl₂` from a state `s` with `cnt s < κ` be a deterministic answer `(y, s')` with
`cnt s' ≤ cnt s + 1`, and the call of `impl₁` from `f s` be `(y, f s')`. Then for a computation
`c` with at most `m` queries and `cnt s + m ≤ κ`,
`simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.

**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
`cnt s < κ`; both calls return the same answer, and the continuation runs from `s'` with one unit
less, where `cnt s' + (m - 1) ≤ κ`. -/
theorem simulate_eq_of_abs_bounded {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
    (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, cnt s < κ → ∃ (y : spec.rng i) (s' : σ₂), impl₂ i x s = .pure (y, s') ∧
      cnt s' ≤ cnt s + 1 ∧ impl₁ i x (f s) = .pure (y, f s'))
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
    (hs : cnt s + m ≤ κ) :
    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    obtain ⟨y, s', h₂, hcnt, h₁⟩ := h i x s (by omega)
    rw [simulate_query, simulate_query, h₁, h₂, OracleComp.pure_bind, OracleComp.pure_bind]
    exact ih y (m - 1) (hk y) s' (by omega)

/-! ### The outer oracle and the composed calls -/

/-- **The outer oracle answering with `f`:** a query `x` is answered `f x`, lengths adjusted. -/
noncomputable def fOuter (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) :
    QueryImpl (bitSpecAt pkOut pkOut n) Unit unifSpec :=
  QueryImpl.ofComp fun _ x => .pure (padFin _ (List.ofFn (f (padFin n (List.ofFn x)))))

/-- `fOuter n f i x s = pure (padFin _ ⟦f (padFin n ⟦x⟧)⟧, s)`. -/
theorem fOuter_apply (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (i : Fin 1)
    (x : (bitSpecAt pkOut pkOut n).dom i) (s : Unit) :
    fOuter n f i x s = .pure (padFin _ (List.ofFn (f (padFin n (List.ofFn x)))), s) := by
  rw [fOuter, QueryImpl.ofComp_apply, OracleComp.pure_bind]

/-- The attack of the attack bit: CCA1 for `true`, CPA for `false`. -/
def atkOf (atkBit : Bool) : Attack := if atkBit then .cca1 else .cpa

/-- `atkOf false = CPA`. -/
theorem atkOf_false : atkOf false = .cpa := rfl

/-- `atkOf true = CCA1`. -/
theorem atkOf_true : atkOf true = .cca1 := rfl

/-- The decryption oracle of `atkOf atkBit` is open exactly when `atkBit` holds and no challenge
was recorded: `decOpen (atkOf atkBit) c = (atkBit && !c)`. -/
theorem decOpen_atkOf (atkBit c : Bool) :
    FixedLengthScheme.decOpen (atkOf atkBit) c = (atkBit && !c) := by
  cases atkBit
  · rw [atkOf, if_neg Bool.false_ne_true, FixedLengthScheme.decOpen_cpa, Bool.false_and]
  · rw [atkOf, if_pos rfl, FixedLengthScheme.decOpen_cca1, Bool.true_and]

/-- The reduction's query budget `q · 1 + 0` (T2's `q · perCall + finCall`). -/
def qRed (q : PolyExpr) : PolyExpr := .add (.mul q (.const 1)) (.const 0)

/-- `(qRed q).eval n = q(n) · 1 + 0`. -/
theorem qRed_eval (q : PolyExpr) (n : ℕ) :
    (qRed q).eval n = q.eval n * (PolyExpr.const 1).eval n + (PolyExpr.const 0).eval n := by
  rw [qRed, PolyExpr.eval_add, PolyExpr.eval_mul]

section Composed

variable (q : PolyExpr) (atkBit b : Bool) (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool))
  (z : List Bool) (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)

/-- The handler's state and the (trivial) outer state, as functions of `eImpl`'s state. -/
def pkAbs (s : ℕ × Option (Fin (ctP.eval n) → Bool)) :
    (Fin ((pkHandler q atkBit b).stateLen.eval n) → Bool) × Unit :=
  (pkHState q atkBit b n s.1 s.2, ())

/-- `pkAbs q atkBit b n s = (pkHState q atkBit b n s.1 s.2, ())`. -/
theorem pkAbs_eq (s : ℕ × Option (Fin (ctP.eval n) → Bool)) :
    pkAbs q atkBit b n s = (pkHState q atkBit b n s.1 s.2, ()) :=
  rfl

/-- Reading a tape through the outer oracle's padding: `f` at the tape `r`. -/
private theorem fOuter_tape (r : Fin n → Bool) :
    padFin n (List.ofFn (padFin ((pkOut 0).eval n) (List.ofFn (f (padFin n (List.ofFn
      (padFin ((pkOut 0).eval n) (List.ofFn r)))))))) = f r := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn]), padFin_ofFn,
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn]), padFin_ofFn]

/-- **One composed call is a call of `eImpl` with the tapes in advance:** from the encoded state
`pkState j o` with `j < q(n)`, the handler composed with `fOuter f` answers as `eImpl` with pad
function `f` and the tapes `extTape (pkSeedTapes ω)` from `(j, o)`, both deterministic, with the
new state abstracted; the counter grows by at most one.

**Proof sketch.** By the oracle and the record: encryption and a fresh challenge ask `f` at the
tape `T_j` (`pkHandler_impl_enc`, `pkHandler_impl_challenge_none`); an open decryption asks `f`
at the nonce of the query (`pkHandler_impl_dec_open`); a closed decryption and a repeated
challenge answer directly. The outer oracle answers `f` (`fOuter_apply`, `fOuter_tape`). -/
theorem comp_pkAbs (i : Fin 3) (x : (bitSpecAt pkDin pkDout n).dom i)
    (s : ℕ × Option (Fin (ctP.eval n) → Bool)) (hs : s.1 < q.eval n) :
    ∃ (y : (bitSpecAt pkDin pkDout n).rng i) (s' : ℕ × Option (Fin (ctP.eval n) → Bool)),
      eImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) (ctP.eval n) n
          (atkOf atkBit) b f (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) i x s =
        .pure (y, s') ∧ s'.1 ≤ s.1 + 1 ∧
      (fOuter n f).comp ((pkHandler q atkBit b).impl n z ω) i x (pkAbs q atkBit b n s) =
        .pure (y, pkAbs q atkBit b n s') := by
  obtain ⟨j, o⟩ := s
  have hj : j < q.eval n := hs
  have hT : AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω) j =
      pkSeedTapes q atkBit b n ω ⟨j, hj⟩ := AdaptiveCPA.extTape_of_lt _ hj
  match i, x with
  | 0, x =>
    refine ⟨_, _, eImpl_enc (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
        (ctP.eval n) n (atkOf atkBit) b f
        (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j o, le_rfl, ?_⟩
    rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq, pkHandler_impl_enc q atkBit b n z ω x j o hj,
      simulate_query, fOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
      pkAbs_eq, pkHState_eq, hT, fOuter_tape]
  | 1, x =>
    by_cases hop : (atkBit && !o.isSome && decWF n (List.ofFn x)) = true
    · refine ⟨_, _, eImpl_dec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
        (ctP.eval n) n (atkOf atkBit) b f
          (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j o, Nat.le_succ _, ?_⟩
      have hwf : decWF n (List.ofFn x) = true := by
        simp only [Bool.and_eq_true] at hop
        exact hop.2
      have hwf' := hwf
      rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
      have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
      have hx0 : padFin n (List.ofFn (padFin ((pkOut 0).eval n) (pairFstD (List.ofFn x)))) =
          padFin n (pairFstD (List.ofFn x)) := by
        rw [GGMRed.ofFn_padFin_of_length (by rw [hwf'.1, hn])]
      rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
        pkHandler_impl_dec_open q atkBit b n z ω x j o hj.le hop,
        simulate_query, fOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
        hx0, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn]; exact hn.symm),
        decOpen_atkOf, decAns_eq]
      simp only [Bool.and_eq_true] at hop
      rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hop.1, hwf⟩)]
    · refine ⟨_, _, eImpl_dec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
        (ctP.eval n) n (atkOf atkBit) b f
          (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j o, Nat.le_succ _, ?_⟩
      rw [Bool.not_eq_true] at hop
      rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
        pkHandler_impl_dec_closed q atkBit b n z ω x j o hj.le hop,
        simulate_pure, OracleComp.pure_bind, decOpen_atkOf, decAns_eq,
        if_neg (by rw [hop]; exact Bool.false_ne_true)]
      have hz : padFin ((pkDout 1).eval n) [] = zeroBits _ := by
        funext k
        simp only [padFin_def, List.getD_nil, zeroBits_apply]
      rw [hz]
  | 2, x =>
    cases o with
    | some c =>
      refine ⟨_, _, eImpl_challenge_some (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          (ctP.eval n) n (atkOf atkBit) b f
        (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j c, Nat.le_succ _, ?_⟩
      rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
        pkHandler_impl_challenge_some q atkBit b n z ω x j c hj.le, simulate_pure,
        OracleComp.pure_bind]
    | none =>
      refine ⟨_, _, eImpl_challenge_none (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          (ctP.eval n) n (atkOf atkBit) b f
        (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j, le_rfl, ?_⟩
      rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
        pkHandler_impl_challenge_none q atkBit b n z ω x j hj,
        simulate_query, fOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
        pkAbs_eq, pkHState_eq, hT, fOuter_tape]

end Composed

/-! ### Transport along output widths and oracle widths -/

/-- **A machine's evaluation does not see its output width:** for `d = d'`, the outputs (as lists)
of `M`'s computations through `bitCodec I O d` and `bitCodec I O d'`, evaluated with `F`, agree.

**Proof sketch.** Substitute `d = d'`. -/
theorem ofFn_evalFn_toCompOn {k : ℕ} {I O : Fin k → ℕ} {d d' : ℕ} (hd : d = d') (M : NUPPT)
    (n q : ℕ) (z : List Bool) (r : M.Coins n) (F : ∀ i, (bitSpec I O).dom i → (bitSpec I O).rng i) :
    List.ofFn ((M.toCompOn (bitCodec I O d) n q z r).evalFn F) =
      List.ofFn ((M.toCompOn (bitCodec I O d') n q z r).evalFn F) := by
  subst hd
  rfl

/-- **The game with pad function `f` does not see the output width:** for `d = d'`, the
expected first output bit of the run through `bitCodec ins outs d` and through
`bitCodec ins outs d'` agree.

**Proof sketch.** Substitute `d = d'`. -/
theorem expect_fImpl_width {ins outs : Fin 3 → ℕ} {d d' : ℕ} (hd : d = d') (c n : ℕ)
    (atk : Attack) (b : Bool) (f : (Fin n → Bool) → (Fin n → Bool)) (A : NUPPT) (q : ℕ)
    (r : A.Coins n) :
    expect (simulate (fImpl ins outs c n atk b f) (A.toComp (bitCodec ins outs d) n q r) none)
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (fImpl ins outs c n atk b f) (A.toComp (bitCodec ins outs d') n q r) none)
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hd
  rfl

/-- **An oracle adversary read at an equal width:** for `m = n`, running
`D.toOracleAdversary n n n q c` against `f` is running `D.toOracleAdversary n m m q c` against `f`
with its inputs and outputs read at width `m`.

**Proof sketch.** Substitute `m = n`; the readings are identities (`padFin_ofFn`). -/
theorem eval_toOracleAdversary_width (D : NUPPT) (n q : ℕ) (c : D.Coins n) {m : ℕ} (hm : m = n)
    (f : (Fin n → Bool) → (Fin n → Bool)) :
    (D.toOracleAdversary n n n q c).eval f =
      (D.toOracleAdversary n m m q c).eval
        (fun x => padFin m (List.ofFn (f (padFin n (List.ofFn x))))) := by
  subst hm
  have h : (fun x => padFin m (List.ofFn (f (padFin m (List.ofFn x))))) = f := by
    funext x
    rw [padFin_ofFn, padFin_ofFn]
  rw [h]

/-! ### The reduction -/

/-- **The PRF reduction** [PS10, Theorem 168.2, step 1]: for a machine adversary `A` with budget
`q`, an attack bit (`atkOf`) and a challenge bit `b`, there is a next-query machine `D` such that,
at every `n` and for every function `f : {0,1}^n → {0,1}^n`, `D` with budget `qRed q` accepts
against `f` with the probability that `A` outputs `1` in the IND experiment with `f` in place of
`f_k` (the oracles `fImpl`, on the lengths `pkDin`, `pkDout`):
`𝔼_c [D^f(c) = 1] = 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (fImpl … f) (A.toComp … r) none]`.

**Proof sketch.** `D` is T4 applied to T2's machine `B` for `pkHandler` and the input-free
companion `A'` of `A`. Its coins are, through the bijections of T4, T2 and the companion, a seed
`ω` and `A`'s coins `r` (`expect_sample_equiv`, `expect_sample_prod`, `expect_sample_comm`). For
fixed `ω` and `r`, T4 and T2 turn `D`'s run against `f` into the evaluation, with `f`, of the
reduction; evaluation is simulation with `fOuter f` (`simulate_ofComp_pure`), which composes with
the handler (`simulate_bind`, `simulate_comp`, `pkHandler_finish`); along `A`'s run (at most
`q(n)` queries, `NUPPT.toComp_costBoundedBy`) the composite is `eImpl` with the tapes of `ω`
(`simulate_eq_of_abs_bounded`, `comp_pkAbs`). Drawing `ω` uniformly gives fresh nonces
(`expect_eImpl`). Widths are transported by `ofFn_evalFn_toCompOn`, `expect_fImpl_width` and
`eval_toOracleAdversary_width`. -/
theorem exists_prfReduction (A : NUPPT) (q : PolyExpr) (atkBit b : Bool) :
    ∃ D : NUPPT, ∀ (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)),
      expect (ProbComp.sample (D.Coins n))
          (fun c => if (D.toOracleAdversary n n n ((qRed q).eval n) c).eval f = true
            then (1 : ℝ) else 0) =
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
              (ctP.eval n) n (atkOf atkBit) b f)
              (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
                (q.eval n) r) none)
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  obtain ⟨A', -, hA'⟩ := exists_toCompOn_of_toComp A
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A' q pkDin pkDout pkOut pkOut (.const 1)
    (pkHandler q atkBit b)
  obtain ⟨D, -, hD⟩ := exists_toOracleAdversary_of_bitCodec B .var .var
  refine ⟨D, fun n f => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA' n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  obtain ⟨φ₄, hφ₄⟩ := hD n
  have hQ : q.eval n * (pkHandler q atkBit b).perCall.eval n +
      (pkHandler q atkBit b).finCall.eval n = (qRed q).eval n := by
    rw [pkHandler_perCall, pkHandler_finCall, qRed_eval]
  have hout : (pkHandler q atkBit b).outLen.eval n = 1 := by
    rw [pkHandler_outLen, PolyExpr.eval_const]
  -- `D`'s coins are a seed and `A`'s coins.
  rw [← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂, expect_sample_prod, expect_sample_comm,
    ← expect_sample_equiv φ₀]
  refine congrArg _ (funext fun r => ?_)
  -- One run of `D` is the reduction evaluated with `f`.
  have hrun : ∀ ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool,
      (if (D.toOracleAdversary n n n ((qRed q).eval n) (φ₄ (φ₂ (ω, φ₀ r)))).eval f = true
        then (1 : ℝ) else 0) =
      expect (simulate (eImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          (ctP.eval n) n (atkOf atkBit) b f (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)))
          (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) r) (0, none))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
    intro ω
    have key : ∀ g : Fin 1 → Bool, (if g 0 = true then (1 : ℝ) else 0) =
        if (List.ofFn g).headD false = true then 1 else 0 := fun g => by
      rw [AdaptiveCPA.headD_ofFn_one]
    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => PolyExpr.var.eval n)
        (fun _ => PolyExpr.var.eval n) ((pkHandler q atkBit b).outLen.eval n)) n
        (q.eval n * (pkHandler q atkBit b).perCall.eval n + (pkHandler q atkBit b).finCall.eval n)
        [] (φ₂ (ω, φ₀ r)) := hφ₂ [] ω (φ₀ r)
    rw [eval_toOracleAdversary_width D n _ _ (PolyExpr.eval_var n), hφ₄, ← hQ, key,
      ofFn_evalFn_toCompOn hout.symm B n _ [] (φ₂ (ω, φ₀ r)), ← h2, InteractiveHandler.advInput_eq,
      hφ₀]
    have hev : simulate (fOuter n f) ((simulate ((pkHandler q atkBit b).impl n [] ω)
        (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          ((PolyExpr.const 1).eval n)) n (q.eval n) r) ((pkHandler q atkBit b).init n)).bind
        (fun res => (pkHandler q atkBit b).finish n [] ω res.2 res.1)) () = _ :=
      simulate_ofComp_pure _ _ _
    have h1 := congrArg (fun c => expect c
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
    simp only [expect_pure] at h1
    refine h1.symm.trans ?_
    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind, pkHandler_finish, simulate_pure, expect_pure]
    rw [pkHandler_init_hstate, show (pkHState q atkBit b n 0 none, ()) =
        pkAbs q atkBit b n (0, none) from (pkAbs_eq q atkBit b n (0, none)).symm,
      simulate_eq_of_abs_bounded _ _ (pkAbs q atkBit b n) (fun s => s.1) (q.eval n)
        (fun i x s hs => comp_pkAbs q atkBit b n f [] ω i x s hs) _ (q.eval n)
        (A.toComp_costBoundedBy _ n (q.eval n) r) (0, none) (Nat.zero_add _).le,
      expect_bind]
    simp only [expect_pure]
    refine congrArg _ (funext fun p => ?_)
    rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])]
  simp only [hrun]
  rw [expect_sample_equiv (pkSeedTapes q atkBit b n) (fun T => expect (simulate
      (eImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) (ctP.eval n) n (atkOf atkBit)
        b f (AdaptiveCPA.extTape T))
      (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
        ((PolyExpr.const 1).eval n)) n (q.eval n) r) (0, none))
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
    expect_eImpl _ _ _ _ _ _ _ (q.eval n)
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _ (q.eval n)
      (A.toComp_costBoundedBy _ n (q.eval n) r) 0 (by omega) none]
  exact expect_fImpl_width (PolyExpr.eval_const 1 n) _ n _ b f A _ r

end TCSlib.Cryptography.Composability.PRFGame
