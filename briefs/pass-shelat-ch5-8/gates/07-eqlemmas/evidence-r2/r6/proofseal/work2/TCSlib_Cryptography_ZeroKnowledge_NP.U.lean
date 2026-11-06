/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
import TCSlib.Cryptography.ZeroKnowledge.NPLemmas
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge proofs for NP: Levin reductions and Theorem 124.1

Step 2 of [PS10, Theorem 124.1]: "to get a zero-knowledge proof `(P, V)` for any NP language
`L`, both `P` and `V` reduce the instance `x` into an instance `x' = f(x)` of graph
3-colouring, the prover additionally reduces the witness `y` to a witness `y' = w(x, y)` for
`x'`, and the parties execute the 3-colouring protocol on `x'`". The reduction must preserve
witnesses, i.e. be a *Levin reduction* (Def-124.a; the text says "Cook's reduction can be
applied to the witness", which Karp/Cook reductions do not provide — source error 47 of the
plan). Zero-knowledge proofs with efficient prover transfer along Levin reductions
(Claim-124.d), which gives [PS10, Theorem 124.1] in the plan's form (A): for every language
`L` with witness relation `R` and every Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)`,
the pulled-back 3-colouring protocol is a zero-knowledge proof with efficient prover for `L`,
given a commitment scheme (hence given a one-way permutation with a hard-core predicate,
[PS10, Theorem 126.4]). The "every language in NP" form is the corollary under the hypothesis
that `3COL` is NP-hard *with Levin reductions* (`LevinNPHard`); the string-level Levin
reduction from `3SAT` is not formalized (plan decision on Theorem 124.1, Claim-124.b/c
deferred).

**Deviations:**
* a Levin reduction is taken *length-regular* with `|f x| = p(|x|)` for a `PolyExpr p ≥ id`
  (assumed: padding a Levin reduction to `3COL` with isolated vertices should give this form
  with `p = q²` for a polynomial `q`, the lengths of `encGraph` being perfect squares, but the
  padding is not formalized; gate 03e, note 14), which makes the coin and round polynomials
  of the pulled-back protocol `subst p` of the original ones and the error bounds
  `ε(p(|x|))`, negligible in `|x|` (`Negligible.comp_of_le`);
* the text's "execute protocol `(P, V)` on `x'`" is read as `(P', V')`; the hypothesis of a
  hard-core predicate for the one-way permutation is made explicit (as in Theorem 126.4).

**Proof infrastructure (run 4):** the transfer proofs use the sibling file
`TCSlib.Cryptography.ZeroKnowledge.NPLemmas` (namespace `LevinTransfer`): the execution
congruence `exec_congr`, the uniform coin projections `coinTrunc`/`UnifProj` with
`distAdv_eq_of_unifProj` (the padding of the random tapes is uniform and independent), the
verifier `liftVerifier V'` and the view re-encoder `postView` of the zero-knowledge transfer,
the machines `exists_liftSimulator`/`exists_liftDistinguisher`, and the strict monotonicity of
a length polynomial `p ≥ id` (`polyExpr_strictMono_of_le`, which gives the left inverse of
`p.eval` along which the distinguisher is re-parametrized).

**Bounded prover messages (ruling G3-3 of gate 03):** the bound on the honest prover's
messages transfers along a Levin reduction with bound `B.subst p`
(`Protocol.ProverBounded.pullback`).

**Scope of Theorem 124.1 (DQ5; gate 03e, minor 3).** The text's Theorem 124.1 asserts one
zero-knowledge proof with negligible soundness error. Here the zero-knowledge protocol is one
iteration of the 3-colouring protocol, with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}`, and
the interactive proof with negligible error is its `n|E|`-fold repetition; that the repetition
is also zero-knowledge, with negligible soundness error, is sequential repetition
[PS10, §7.2.1], which ch. 7 supplies (ruling G3-7(d)), and is not stated here. In the
existential forms the conjunct `∃ π, EfficientProverProof π L R` says nothing about the
zero-knowledge protocol (`npProtocol` already witnesses it, `npProtocol_interactiveProof`);
the tied forms `exists_commitment_zk_proof_of_owp_levinReduction`,
`zk_proof_of_witnessRelation` and `zk_proof_of_witnessRelation_of_owp` state both protocols for
one commitment scheme and one Levin reduction, as `zk_proof_of_levinReduction` does.

**Run-3 repairs (audit P11-1, P11-2):** the transfer lemmas and both forms of Theorem 124.1
take the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` (`L ⊆ witnessLanguage R`): no field of
`LevinReduction` relates `L` to `R` (with `R = ∅` the `witness` field is vacuous), and without
it the `complete` clause of the pulled-back proof is false. The "every language in NP" forms
keep the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` of the Levin reduction's
length polynomial `p ≥ id` (the run-2 `∃ s, EfficientProverProofErr π L R s` was vacuous with
`s = 1`; `one_sub_inv_add_half_pow_lt_one` shows the error is below `1`).

## Main definitions

* `TCSlib.Cryptography.LevinReduction` — Levin (witness-preserving) reductions (Def-124.a).
* `TCSlib.Cryptography.Strategy.pullback`, `TCSlib.Cryptography.Protocol.pullback` — the
  protocol for `L` obtained by reducing to `L'` and running a protocol for `L'`.
* `TCSlib.Cryptography.LevinNPHard` — NP-hardness with Levin reductions (the hypothesis of
  the "every language in NP" form).

## Main results

* `TCSlib.Cryptography.LevinReduction.refl`, `TCSlib.Cryptography.LevinReduction.trans`,
  `TCSlib.Cryptography.LevinReduction.polyTimeReducible` — sanity: Levin reductions compose
  and are Karp reductions (proved).
* `TCSlib.Cryptography.LevinReduction.efficientProverProof`,
  `TCSlib.Cryptography.LevinReduction.efficientProverProofErr`,
  `TCSlib.Cryptography.LevinReduction.zk` — interactive proofs with efficient prover and
  zero-knowledge transfer along Levin reductions (Claim-124.d);
  `TCSlib.Cryptography.Protocol.ProverBounded.pullback` — so does the bound on the prover's
  messages.
* `TCSlib.Cryptography.zk_proof_of_levinReduction` — **[PS10, Theorem 124.1], form (A)**:
  a commitment scheme and a Levin reduction to `3COL` give a zero-knowledge protocol for `L`
  with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}` whose `n|E|`-fold repetition is an
  interactive proof; `TCSlib.Cryptography.zk_proof_of_owp_levinReduction`,
  `TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction` — the same from a
  one-way permutation with a hard-core predicate, untied and tied (Thm-124.1).
* `TCSlib.Cryptography.zk_proof_of_witnessRelation`,
  `TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp` — the "every language in NP" form
  for every witness relation, under `LevinNPHard L3COL R3COL` (the second from a one-way
  permutation, the text's hypothesis); `TCSlib.Cryptography.zk_proof_of_mem_NP`,
  `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp` — the corollaries for `L ∈ NP` with the
  witness relation of `exists_witnessRelation_of_mem_NP`, with the explicit soundness error of
  the Levin reduction's length polynomial
  (`TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one`: the error is below `1`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.7, Karp reductions; §2.3, Levin reductions.)
-/

namespace TCSlib.Cryptography

open Complexity Turing LevinTransfer

/-! ### Levin reductions (Def-124.a) -/

/-- A **Levin reduction** `(f, w)` from `(L, R)` to `(L', R')` [PS10, §4.7, Theorem 124.1,
step 2, "Cook's reduction can be applied to the witness"] (Def-124.a): `f` is a
polynomial-time Karp reduction (`x ∈ L ↔ f x ∈ L'`), `w` is polynomial-time on the pair
`⟨x, y⟩` and maps witnesses to witnesses (`R x y → R' (f x) (w x y)`), and `f` is
length-regular: `|f x| = p(|x|)` for the polynomial `p ≥ id`.

**Deviation:** the text never defines Levin reductions; length-regularity with `p ≥ id` is
assumed (padding with isolated vertices should achieve it for `3COL`, with `p = q²`; not
formalized) so that the pulled-back protocol's polynomials are `subst p` of the original ones
and its error bounds `ε(p(|x|))` are negligible in `|x|`. -/
structure LevinReduction (L L' : Language Bool) (R R' : List Bool → List Bool → Prop)
    (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Prop where
  /-- The instance map is polynomial-time. -/
  f_poly : PolyTimeComputable f
  /-- The witness map is polynomial-time on the pair `⟨x, y⟩`. -/
  w_poly : PolyTimeComputable fun z => w (pairFstD z) (pairSndD z)
  /-- `f` is a Karp reduction. -/
  mem_iff : ∀ x, x ∈ L ↔ f x ∈ L'
  /-- `w` maps witnesses of `x` to witnesses of `f x`. -/
  witness : ∀ x y, R x y → R' (f x) (w x y)
  /-- `f` is length-regular with length polynomial `p`. -/
  length_eq : ∀ x, (f x).length = p.eval x.length
  /-- The length polynomial dominates the identity. -/
  le_eval : ∀ N, N ≤ p.eval N

/-- A Levin reduction is a Karp reduction [AB09, Definition 2.7]. -/
theorem LevinReduction.polyTimeReducible {L L' : Language Bool} {R R' : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L' R R' f w p) : PolyTimeReducible L L' :=
  ⟨f, h.f_poly, h.mem_iff⟩

/-- Sanity: the identity is a Levin reduction of `(L, R)` to itself. -/
theorem LevinReduction.refl (L : Language Bool) (R : List Bool → List Bool → Prop) :
    LevinReduction L L R R id (fun _ y => y) .var where
  f_poly := polyTimeComputable_id
  w_poly := polyTimeComputable_pairSndD
  mem_iff _ := Iff.rfl
  witness _ _ h := h
  length_eq _ := rfl
  le_eval _ := le_rfl

/-- Sanity: Levin reductions compose, with length polynomial `p'.subst p`.

**Proof sketch.** `f' ∘ f` by `PolyTimeComputable.comp`; the composed witness map
`⟨x, y⟩ ↦ w' (f x) (w x y)` is `w'` on the pair `⟨f x, w x y⟩` built by
`PolyTimeComputable.pairEncode` (`pairFstD_pairEncode`, `pairSndD_pairEncode`); membership
and witnesses by transitivity; lengths by `PolyExpr.eval_subst`. -/
theorem LevinReduction.trans {L L' L'' : Language Bool}
    {R R' R'' : List Bool → List Bool → Prop} {f f' : List Bool → List Bool}
    {w w' : List Bool → List Bool → List Bool} {p p' : PolyExpr}
    (h : LevinReduction L L' R R' f w p) (h' : LevinReduction L' L'' R' R'' f' w' p') :
    LevinReduction L L'' R R'' (f' ∘ f) (fun x y => w' (f x) (w x y)) (p'.subst p) where
  f_poly := h'.f_poly.comp h.f_poly
  w_poly := by
    have hfun : (fun z => w' (f (pairFstD z)) (w (pairFstD z) (pairSndD z))) =
        fun z => w' (pairFstD (pairEncode (f (pairFstD z)) (w (pairFstD z) (pairSndD z))))
          (pairSndD (pairEncode (f (pairFstD z)) (w (pairFstD z) (pairSndD z)))) := by
      funext z
      rw [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hfun]
    exact h'.w_poly.comp ((h.f_poly.comp polyTimeComputable_pairFstD).pairEncode h.w_poly)
  mem_iff x := (h.mem_iff x).trans (h'.mem_iff (f x))
  witness x y hxy := h'.witness _ _ (h.witness x y hxy)
  length_eq x := by
    rw [Function.comp_apply, h'.length_eq, h.length_eq, PolyExpr.eval_subst]
  le_eval N := by
    rw [PolyExpr.eval_subst]
    exact (h.le_eval N).trans (h'.le_eval _)

/-! ### Pulling a protocol back along a reduction -/

/-- The strategy that runs `S` on the reduced instance `f x` with the transformed auxiliary
input `g x z` [PS10, §4.7, Theorem 124.1, step 2]: `next x z r hist := S.next (f x) (g x z) r hist`,
coins `S.coins.subst p` (so that the tape at `|x|` has exactly `S.coinLen |f x|` bits when
`|f x| = p(|x|)`). -/
def Strategy.pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) (p : PolyExpr) : Strategy where
  next x z r hist := S.next (f x) (g x z) r hist
  coins := S.coins.subst p

/-- The pulled-back strategy's coin length at `|x|` is `S`'s at `|f x|` under length
regularity. -/
theorem Strategy.coinLen_pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) :
    (S.pullback f g p).coinLen x.length = S.coinLen (f x).length := by
  simp [Strategy.pullback, Strategy.coinLen, PolyExpr.eval_subst, hx]

/-- The protocol for `L` obtained from a protocol `π` for `L'` and a reduction `(f, w)`
[PS10, §4.7, Theorem 124.1, step 2]: `P(x, y) := P'(f x, w x y)`, `V(x, z) := V'(f x, z)`,
rounds `π.rounds.subst p`, same first mover (Claim-124.d, construction).

**Deviation:** "execute protocol `(P, V)` on `x'`" read as `(P', V')`. -/
def Protocol.pullback (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Protocol where
  P := π.P.pullback f w p
  V := π.V.pullback f (fun _ z => z) p
  rounds := π.rounds.subst p
  verifierFirst := π.verifierFirst

/-- Unfolding: the verifier's output in the pulled-back protocol against a prover `P'` is
`π.V.next` on the reduced instance after `π.rounds.eval (p |x|)` moves of `exec` with the
reduced inputs. -/
theorem Protocol.pullback_outV (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) (p : PolyExpr) (P' : Strategy) (x y z : List Bool)
    (r : (π.pullback f w p).ExecCoins P' x) :
    (π.pullback f w p).outV P' x y z r =
      π.V.next (f x) z (List.ofFn r.2)
        (exec P' (π.V.pullback f (fun _ z => z) p) π.verifierFirst x y z (List.ofFn r.1)
          (List.ofFn r.2) (π.rounds.eval (p.eval x.length))).2 := by
  simp [Protocol.outV, Protocol.transcriptWith, Protocol.pullback, Strategy.pullback,
    PolyExpr.eval_subst]

/-- A pulled-back strategy is efficient when the original is and `f`, `g` are
polynomial-time (on `⟨x, z⟩` for `g`): compose the machine of `S` with the FP function
`⟨⟨x, z⟩, msgs⟩ ↦ ⟨⟨f x, g x z⟩, msgs⟩` and re-parametrize `1^{|x|}` to `1^{p |x|}`
(`NUPPT.exists_reparam p`, `NUPPT.exists_comp`, `PolyExpr.eval_subst`, `hx`).

**Proof sketch.** From `hS` take the uniform `A` with `S.next x' z' r hist =
A.runAtL |x'| ⟨⟨x', z'⟩, encodeMsgs hist⟩ r`. `NUPPT.exists_comp A hpre polyTimeComputable_id`
with `pre := ⟨⟨f ∘ pairFstD ∘ pairFstD, g on the pair⟩, pairSndD⟩` (pairing calculus) gives
`B` with `B.runAtL m y r = A.runAtL m (pre y) r`; `NUPPT.exists_reparam B p` gives `C` with
`C.runAtL n y r = B.runAtL (p n) y r`, uniform, coins `A.coins.subst p = (S.pullback …).coins`;
on `n = |x|`, `p n = |f x|` (`hx`), so `C` computes the pulled-back next-message function
(`Strategy.ofNUPPT_next`, `pairFstD_pairEncode`, `pairSndD_pairEncode`). -/
theorem Strategy.pullback_efficient {S : Strategy} (hS : S.Efficient) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) {g : List Bool → List Bool → List Bool}
    (hg : PolyTimeComputable fun z => g (pairFstD z) (pairSndD z)) {p : PolyExpr}
    (hx : ∀ x, (f x).length = p.eval x.length) : (S.pullback f g p).Efficient := by
  obtain ⟨A, hA, hc, hnext⟩ := hS
  have hpre : PolyTimeComputable fun y =>
      pairEncode (pairEncode (f (pairFstD (pairFstD y)))
        (g (pairFstD (pairFstD y)) (pairSndD (pairFstD y)))) (pairSndD y) :=
    ((hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)).pairEncode
      (hg.comp polyTimeComputable_pairFstD)).pairEncode polyTimeComputable_pairSndD
  obtain ⟨B, hBc, -, hBadv, hB⟩ := A.exists_comp hpre polyTimeComputable_id
  obtain ⟨C, hCc, hCu, hC⟩ := B.exists_reparam p
  refine ⟨C, hCu fun n => by rw [hBadv]; exact hA n, ?_, fun x z r hist => ?_⟩
  · show S.coins.subst p = C.coins
    rw [hCc, hBc, hc]
  · rw [Strategy.ofNUPPT_next, hC, hB]
    show S.next (f x) (g x z) r hist = _
    rw [hnext, Strategy.ofNUPPT_next, ← hx x]
    simp only [id, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **Bounded prover messages transfer along a Levin reduction** with bound `B.subst p`
(ruling G3-3 of gate 03): the pulled-back prover runs `π.P` on `(f x, w x y)`, `R x y` gives
`R' (f x) (w x y)` (`LevinReduction.witness`), and `|f x| = p(|x|)`
(`LevinReduction.length_eq`, `PolyExpr.eval_subst`). -/
theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    {π : Protocol} {B : PolyExpr} (hB : π.ProverBounded R' B) :
    (π.pullback f w p).ProverBounded R (B.subst p) := by
  rw [Protocol.proverBounded_iff] at hB ⊢
  intro x y r hist hxy
  rw [PolyExpr.eval_subst, ← h.length_eq x]
  exact hB (f x) (w x y) r hist (h.witness x y hxy)

/-! ### Negligibility along polynomial reparametrization -/

/-- A negligible function composed with a map `φ ≥ id` is negligible: for `N ≥ max n₀ 1`,
`φ N ≥ N ≥ n₀` so `|μ (φ N)| < 1 / (φ N)^c ≤ 1 / N^c` (the bookkeeping for the error bounds
`ε(|f x|) = ε(p(|x|))` of the pulled-back protocol, Claim-124.d). -/
theorem Negligible.comp_of_le {μ : ℕ → ℝ} (hμ : Negligible μ) (φ : ℕ → ℕ) (hφ : ∀ N, N ≤ φ N) :
    Negligible fun N => μ (φ N) := by
  intro c
  obtain ⟨n₀, h₀⟩ := hμ c
  refine ⟨max n₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hφN : n₀ ≤ φ N := le_trans (le_trans (le_max_left _ _) hN) (hφ N)
  refine lt_of_lt_of_le (h₀ (φ N) hφN) ?_
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  exact one_div_le_one_div_of_le hNpos (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hφ N) c)

/-! ### Executions of the pulled-back protocol -/

/-- The execution of two pulled-back strategies on `x` is the execution of the original
strategies on `f x` with the transformed auxiliary inputs and the same random tapes
(`LevinTransfer.exec_congr`; the pulled-back next-message functions are those of the
originals on the reduced inputs by definition). -/
private theorem exec_pullback (P V : Strategy) (f : List Bool → List Bool)
    (g g' : List Bool → List Bool → List Bool) (p : PolyExpr) (vFirst : Bool)
    (x zP zV rP rV : List Bool) (k : ℕ) :
    exec (P.pullback f g p) (V.pullback f g' p) vFirst x zP zV rP rV k =
      exec P V vFirst (f x) (g x zP) (g' x zV) rP rV k := by
  refine exec_congr ?_ ?_ vFirst k <;> intro _ <;> rfl

/-- The execution of an arbitrary prover `P'` against a pulled-back verifier on `x` is the
execution of the prover `⟨fun _ _ r hist => P'.next x [] r hist, const (P'.coinLen |x|)⟩`
(which hard-wires `x` and has `P'`'s random tape) against the original verifier on `f x`
(`LevinTransfer.exec_congr`). -/
private theorem exec_pullback_cheat (P' V : Strategy) (f : List Bool → List Bool)
    (g' : List Bool → List Bool → List Bool) (p : PolyExpr) (vFirst : Bool)
    (x zV rP rV : List Bool) (k : ℕ) :
    exec P' (V.pullback f g' p) vFirst x [] zV rP rV k =
      exec ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ V vFirst (f x)
        [] (g' x zV) rP rV k := by
  refine exec_congr ?_ ?_ vFirst k <;> intro _ <;> rfl

/-- The coin length of a pulled-back strategy at `|x|` is at least (in fact equal to) the
original's at `|f x|` under length regularity — the form in which `LevinTransfer.coinTrunc`
casts the honest coins of the pulled-back protocol to those of `π` on `f x`. -/
private theorem coinLen_le_coinLen_pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) :
    S.coinLen (f x).length ≤ (S.pullback f g p).coinLen x.length :=
  (Strategy.coinLen_pullback S f g hx).ge

/-- **The honest execution of the pulled-back protocol is the honest execution of `π` on the
reduced instance:** the verifier's output in `(π.pullback f w p)` on `(x, y, z)` with coins
`r` is the output of `π` on `(f x, w x y, z)` with the coins cast along
`Strategy.coinLen_pullback` (`Protocol.pullback_outV`, `exec_pullback`,
`LevinTransfer.ofFn_coinTrunc_of_eq`, the move count `π.rounds (p |x|) = π.rounds |f x|`). -/
private theorem outV_pullback_honest (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) (y z : List Bool)
    (r : (π.pullback f w p).ExecCoins (π.pullback f w p).P x) :
    (π.pullback f w p).outV (π.pullback f w p).P x y z r =
      π.outV π.P (f x) (w x y) z
        (Prod.map (coinTrunc (coinLen_le_coinLen_pullback π.P f w hx))
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Protocol.pullback, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.P f w hx).symm,
    ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.V f (fun _ z => z) hx).symm,
    exec_pullback, ← hx]

/-- **A cheating prover for the pulled-back protocol is a cheating prover for `π`:** the
verifier's output in `(π.pullback f w p)` against `P'` on `x` with coins `r` is the output
of `π` on `f x` against the prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist,
const (P'.coinLen |x|)⟩` (which hard-wires `x` and has `P'`'s random tape) with the verifier
coins cast along `Strategy.coinLen_pullback` (`exec_congr`). -/
private theorem outV_pullback_cheat (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) (P' : Strategy) (z : List Bool)
    (r : (π.pullback f w p).ExecCoins P' x) :
    (π.pullback f w p).outV P' x [] z r =
      π.outV ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ (f x) [] z
        (Prod.map (coinTrunc (Strategy.coinLen_eq _ _).le)
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  have hc : (⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ :
      Strategy).coinLen (f x).length = P'.coinLen x.length := Strategy.coinLen_eq _ _
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ hc,
    ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.V f (fun _ z => z) hx).symm,
    exec_pullback_cheat, ← hx]

/-! ### Claim-124.d: zero-knowledge proofs transfer along Levin reductions -/

/-- **Interactive proofs with efficient prover transfer along Levin reductions, soundness
error `s ∘ p`** [PS10, §4.7, "it is easy to verify that the above protocol is a
zero-knowledge proof"] (Claim-124.d, proof half): if `π` is an interactive proof for `L'` with
efficient prover w.r.t. `R'` and soundness error `s`, `(f, w)` is a Levin reduction of
`(L, R)` to `(L', R')`, and every `x ∈ L` has an `R`-witness (`hLR`, i.e.
`L ⊆ witnessLanguage R`), then `π.pullback f w p` is an interactive proof for `L` with
efficient prover w.r.t. `R` and soundness error `N ↦ s (p N)`.

**Repair (run-3 audit P11-1):** the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` was added. No
field of `LevinReduction` relates `L` to `R` — with `R = ∅` the `witness` field is vacuous, so
a witness map that outputs non-witnesses is a valid Levin reduction — while the `complete`
clause of the conclusion needs the pulled-back honest prover, which runs `π.P` on `w x y`, to
hold a witness `y` with `R x y`; without `hLR` the statement is refutable (`npProtocol` for
the relation `|x| = |y|` pulled back along `id` and `w x y := ⟨x, x⟩`). Equivalent
alternative: state the lemma for `L := witnessLanguage R`.

**Proof sketch.** Efficiency of both parties: `Strategy.pullback_efficient` with `h.f_poly`,
`h.w_poly` (for `V` the map `g := fun _ z => z` is `polyTimeComputable_pairSndD`), `h.length_eq`.
Completeness for every witness: for `R x y`, `R' (f x) (w x y)` (`h.witness`), and the
execution of the pulled-back protocol on `(x, y, z)` with coins `r` is the execution of `π` on
`(f x, w x y, z)` with the coins cast along `Strategy.coinLen_pullback` (`outV_pullback_honest`:
`Protocol.pullback_outV` and `LevinTransfer.exec_congr` — the pulled-back next-message
functions are those of `π` on `(f x, w x y)` and `(f x, z)` by definition — with the move
count `π.rounds.eval (p |x|) = π.rounds.eval |f x|` by `h.length_eq`); the cast is a uniform
projection (`LevinTransfer.unifProj_coinTrunc`, `UnifProj.uprob_comp`), so
`hπ.completeWitness` gives probability one. Bounded prover messages:
`Protocol.ProverBounded.pullback` with the bound `B.subst p` of `hπ.boundedP`. Completeness:
for `x ∈ L` take `y` with `R x y` (`hLR`); the honest messages have at most `B(p(|x|))` bits
and the verifier accepts with probability one (`Protocol.ProverBounded.exists_complete`).
Soundness: for `x ∉ L`, `f x ∉ L'` (`h.mem_iff`); a prover `P'` for the pulled-back protocol
on `x` is the prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen |x|)⟩`
for `π` on `f x` with the same coins (`outV_pullback_cheat`,
`P*.coinLen |f x| = P'.coinLen |x|`), and
`hπ.sound (f x) _ P* z` gives `1 - s |f x| ≤ Pr[out = [false]]`, i.e. `1 - s (p |x|)` by
`h.length_eq`. -/
theorem LevinReduction.efficientProverProofErr {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    (hLR : ∀ x ∈ L, ∃ y, R x y) {π : Protocol} {s : ℕ → ℝ}
    (hπ : EfficientProverProofErr π L' R' s) :
    EfficientProverProofErr (π.pullback f w p) L R (fun N => s (p.eval N)) := by
  have hcompl : ∀ x y, R x y → ∀ z : List Bool,
      uprob (fun r : (π.pullback f w p).ExecCoins (π.pullback f w p).P x =>
        (π.pullback f w p).outV (π.pullback f w p).P x y z r = [true]) = 1 := by
    intro x y hxy z
    have hx := h.length_eq x
    have key := hπ.completeWitness (f x) (w x y) (h.witness x y hxy) z
    rw [← ((unifProj_coinTrunc (coinLen_le_coinLen_pullback π.P f w hx)).prod
      (unifProj_coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx))).uprob_comp
      (fun r' => π.outV π.P (f x) (w x y) z r' = [true])] at key
    rw [← key]
    congr 1
    funext r
    rw [outV_pullback_honest π f w hx]
  obtain ⟨B, hB⟩ := hπ.boundedP
  refine ⟨⟨Strategy.pullback_efficient hπ.efficientV h.f_poly polyTimeComputable_pairSndD
    h.length_eq, (hB.pullback h).exists_complete hLR hcompl, fun x hx P' z => ?_⟩,
    Strategy.pullback_efficient hπ.efficientP h.f_poly h.w_poly h.length_eq,
    ⟨B.subst p, hB.pullback h⟩, hcompl⟩
  · have hlen := h.length_eq x
    have hfx : f x ∉ L' := fun hfx => hx ((h.mem_iff x).2 hfx)
    have hU : UnifProj (Prod.map (coinTrunc le_rfl)
        (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hlen)) :
          (π.pullback f w p).ExecCoins P' x →
            π.ExecCoins ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩
              (f x)) :=
      (unifProj_coinTrunc _).prod (unifProj_coinTrunc _)
    have key := hπ.sound (f x) hfx
      ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ z
    rw [← hU.uprob_comp] at key
    refine le_of_eq_of_le (by rw [hlen]) (le_of_le_of_eq key ?_)
    congr 1
    funext r
    rw [outV_pullback_cheat π f w hlen]

/-- **Interactive proofs with efficient prover transfer along Levin reductions** (Claim-124.d,
proof half, negligible error): as `LevinReduction.efficientProverProofErr`, the soundness
error `ε (p N)` being negligible by `Negligible.comp_of_le` with `h.le_eval`
(`EfficientProverProof.exists_err`, `EfficientProverProofErr.efficientProverProof`).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`LevinReduction.efficientProverProofErr`). -/
theorem LevinReduction.efficientProverProof {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    (hLR : ∀ x ∈ L, ∃ y, R x y) {π : Protocol} (hπ : EfficientProverProof π L' R') :
    EfficientProverProof (π.pullback f w p) L R := by
  obtain ⟨ε, hε, herr⟩ := hπ.exists_err
  exact (h.efficientProverProofErr hLR herr).efficientProverProof (hε.comp_of_le _ h.le_eval)

/-- **Zero-knowledge transfers along Levin reductions** [PS10, §4.7, "it is easy to verify
that the above protocol is a zero-knowledge proof"] (Claim-124.d, zero-knowledge half): if `π`
is zero-knowledge for `R'` and `(f, w)` is a Levin reduction of `(L, R)` to `(L', R')`, then
`π.pullback f w p` is zero-knowledge for `R`.

**Proof sketch.** Let `V*` be an efficient verifier for the pulled-back protocol. The
verifier `V*' := LevinTransfer.liftVerifier V*` for `π`, `V*'.next x' z' r hist := V*.next
(pairFstD z') (pairSndD z') (r.take (V*.coinLen |pairFstD z'|)) hist` with coins `V*.coins`
(at `|x'| = p |x| ≥ |x|` the tape is long enough, `PolyExpr.eval_mono`, `h.le_eval`), recovers
`x` from its auxiliary input `z' = ⟨x, z⟩` and ignores `x'`; it is efficient
(`LevinTransfer.liftVerifier_efficient`, from `V*`'s machine with
`polyTimeComputable_pairTakePoly`). `hzk V*'` gives a uniform simulator `S'`; the simulator for
`V*` is `S` with `S.simulate x z r = post (S'.simulate (f x) ⟨x, z⟩ r)`, where
`post := LevinTransfer.postView V*.coins` re-encodes the view `⟨⟨x', ⟨x, z⟩⟩, ⟨r', msgs⟩⟩` as
`⟨⟨x, z⟩, ⟨r'.take (V*.coinLen |x|), msgs⟩⟩` (`LevinTransfer.exists_liftSimulator`:
`NUPPT.exists_comp` with `pre y := ⟨f (fst y), y⟩`, then `NUPPT.exists_reparam p`; uniform,
coins `S'.coins.subst p`). For `Lz`, `D`: the distinguisher `D'` for `π` at parameter
`|x'| = p |x|` is `D` re-parametrized along the left inverse `φ N' := min (invFun p.eval N') N'`
of `p.eval` — well defined since `p ≥ id` is strictly increasing
(`LevinTransfer.polyExpr_strictMono_of_le`) — composed with `post`
(`LevinTransfer.exists_liftDistinguisher`: `NUPPT.exists_reparam_advice`, `NUPPT.exists_comp`);
auxiliary bound `Lz' := add (add (mul (const 2) var) (const 2)) Lz` (`|⟨x, z⟩| ≤ 2|x| + 2
+ Lz |x| ≤ Lz' |x'|`). `hzk V*' Lz' D'` gives `ε'`; on `R x y` (so `R' (f x) (w x y)`), `post` of
the view of `V*'` in `π` on `(f x, w x y, ⟨x, z⟩)` with coins `(r₁, r₂')` is the view of `V*` in
the pulled-back protocol with coins `(r₁, r₂'.take (V*.coinLen |x|))`
(`LevinTransfer.exec_congr`, `liftVerifier_next`, `postView_encode`), and `D'`'s verdict is
`D`'s on the re-encoded sample with truncated coins (`LevinTransfer.distinguisherL_lift`);
the truncations are uniform projections, so the two advantages coincide
(`LevinTransfer.distAdv_eq_of_unifProj`) and `distAdv ≤ ε' |f x| = ε' (p |x|)`;
`ε := ε' ∘ p.eval` is negligible by `Negligible.comp_of_le`. -/
theorem LevinReduction.zk {L L' : Language Bool} {R R' : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L' R R' f w p) {π : Protocol} (hzk : ZK π R') :
    ZK (π.pullback f w p) R := by
  intro V' hV'
  obtain ⟨S', hS'u, hS'⟩ := hzk (liftVerifier V') (liftVerifier_efficient hV')
  obtain ⟨S, hSc, hSu, hS⟩ := exists_liftSimulator S' h.f_poly V'.coins p
  refine ⟨S, hSu hS'u, fun Lz D => ?_⟩
  -- the left inverse `φ` of the (strictly increasing) length polynomial
  have hmono := polyExpr_strictMono_of_le h.le_eval
  set φ : ℕ → ℕ := fun n => min (Function.invFun p.eval n) n with hφ_def
  have hφle : ∀ n, φ n ≤ n := fun n => min_le_right _ _
  have hφp : ∀ N, φ (p.eval N) = N := fun N => by
    simp only [hφ_def, Function.leftInverse_invFun hmono.injective N]
    exact min_eq_left (h.le_eval N)
  obtain ⟨D', hD'c, hD'⟩ := exists_liftDistinguisher D φ hφle V'.coins
  set Lz' : PolyExpr := .add (.add (.mul (.const 2) .var) (.const 2)) Lz with hLz'
  obtain ⟨ε', hε', hadv⟩ := hS' Lz' D'
  refine ⟨fun N => ε' (p.eval N), hε'.comp_of_le _ h.le_eval, fun x y z hxy hz => ?_⟩
  have hlen := h.length_eq x
  have hz' : (pairEncode x z).length ≤ Lz'.eval (f x).length := by
    rw [length_pairEncode, hlen, hLz']
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have h₁ := h.le_eval x.length
    have h₂ := Lz.eval_mono (h.le_eval x.length)
    omega
  have key := hadv (f x) (w x y) (pairEncode x z) (h.witness x y hxy) hz'
  -- coin-space bookkeeping
  have hxle : x.length ≤ (f x).length := by rw [hlen]; exact h.le_eval _
  have hφx : φ (f x).length = x.length := by rw [hlen]; exact hφp _
  have hDle : D.coinLen x.length ≤ D'.coinLen (f x).length := by
    simp only [NUPPT.coinLen, hD'c]
    exact D.coins.eval_mono hxle
  have hVle : V'.coinLen x.length ≤ (liftVerifier V').coinLen (f x).length := by
    rw [liftVerifier_coinLen]
    exact V'.coins.eval_mono hxle
  have hPeq : (π.P.pullback f w p).coinLen x.length = π.P.coinLen (f x).length :=
    Strategy.coinLen_pullback π.P f w hlen
  have hSeq : S.coinLen x.length = S'.coinLen (f x).length := by
    simp only [NUPPT.coinLen, hSc, PolyExpr.eval_subst, hlen]
  calc distAdv (fun r => (((π.pullback f w p).withV V').viewV x y z r).encode) (S.simulate x z)
        (D.distinguisherL x.length)
      = distAdv (fun r => ((π.withV (liftVerifier V')).viewV (f x) (w x y) (pairEncode x z) r).encode)
          (S'.simulate (f x) (pairEncode x z)) (D'.distinguisherL (f x).length) := by
        refine (distAdv_eq_of_unifProj ((unifProj_coinTrunc hPeq.le).prod (unifProj_coinTrunc hVle))
          (unifProj_coinTrunc hSeq.le) (unifProj_coinTrunc hDle) (fun r ρ => ?_)
          (fun r ρ => ?_)).symm
        · -- the view of `V*'` in `π` re-encodes to the view of `V'` in the pulled-back protocol
          rw [distinguisherL_lift hD' hφx hDle]
          congr 2
          simp only [Protocol.viewV, Protocol.transcriptWith, Protocol.withV_P, Protocol.withV_V,
            Protocol.withV_rounds, Protocol.withV_verifierFirst, Protocol.pullback, Prod.map,
            postView_encode]
          rw [ofFn_coinTrunc_of_eq _ hPeq, ofFn_coinTrunc]
          simp only [PolyExpr.eval_subst, ← hlen, Strategy.coinLen]
          congr 2
          refine congrArg Prod.snd (exec_congr ?_ ?_ _ _)
          · intro _
            rfl
          · intro _
            exact liftVerifier_next V' _ x z _ _
        · -- the simulator for `V'` is `postView` of the simulator for `V*'`
          rw [distinguisherL_lift hD' hφx hDle]
          congr 2
          simp only [NUPPT.simulate, NUPPT.runAt_eq, hS, pairFstD_pairEncode]
          rw [ofFn_coinTrunc_of_eq _ hSeq, ← hlen]
    _ ≤ ε' (f x).length := key
    _ = ε' (p.eval x.length) := by rw [hlen]

/-! ### Theorem 124.1 -/

/-- **[PS10, Theorem 124.1], form (A): a commitment scheme and a Levin reduction to `3COL`
give a zero-knowledge protocol for `L` with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}` whose
`n|E|`-fold repetition is an interactive proof** (Thm-124.1): for a commitment scheme
`(Com, ℓ)` and a Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)` with
`L ⊆ witnessLanguage R` (`hLR`),
the pulled-back `n|E|`-fold 3-colouring protocol is an interactive proof for `L` with
efficient prover w.r.t. `R`, and the pulled-back one-iteration protocol is zero-knowledge for
`R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`.

**Deviation (DQ5):** the proof and the zero-knowledge statements are for the repeated and
the single-iteration protocols respectively (sequential composition, [PS10, §7.2.1], is out
of scope; the text's single zero-knowledge proof with negligible soundness error is debt that
ch. 7 discharges, ruling G3-7(d)); the reduction is an explicit hypothesis (the text's
"Cook's reduction applied to the witness" is a Levin reduction, never defined there).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added — the first and
third conjuncts are instances of `LevinReduction.efficientProverProofErr`, and without it
the reduction `id`, `w x y := []` of `(3COL, ∅)` to `(3COL, R_3COL)` refutes them on the
2-vertex one-edge graph (the pulled-back prover commits to the constant colouring
`decColoring n [] = 0` and opens two equal colours). -/
theorem zk_proof_of_levinReduction {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) :=
  ⟨h.efficientProverProof hLR (colRep_efficientProverProof hC), h.zk (col_zk hC),
    h.efficientProverProofErr hLR (col_efficientProverProofErr hC)⟩

/-- **[PS10, Theorem 124.1]: if one-way permutations (with a hard-core predicate) exist, every
language with a Levin reduction to `3COL` has a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`** (Thm-124.1, untied existential form): for `L ⊆ witnessLanguage R`
(`hLR`) there is a protocol that is an interactive proof for `L` with efficient prover w.r.t.
`R`, and a protocol that is zero-knowledge for `R` and an interactive proof with efficient
prover and soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` — the commitment scheme of
[PS10, Theorem 126.4] (`exists_commitment_of_owp_hardCore`) plugged into
`zk_proof_of_levinReduction`.

**Deviation:** hard-core predicate explicit (source error 47); single OWP rather than a
collection; see `zk_proof_of_levinReduction` for the two-protocol form (DQ5). The first
conjunct alone says nothing about the zero-knowledge protocol (gate 03e, minor 3:
`npProtocol` pulled back along `(f, w)` already witnesses it); the tied form, both protocols
from one commitment scheme, is `exists_commitment_zk_proof_of_owp_levinReduction`.

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`zk_proof_of_levinReduction`). -/
theorem zk_proof_of_owp_levinReduction
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ P.HardCore h)
    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ π : Protocol, ZK π R ∧ EfficientProverProofErr π L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  obtain ⟨h1, h2, h3⟩ := zk_proof_of_levinReduction hC h hLR
  exact ⟨⟨_, h1⟩, _, h2, h3⟩

/-- **[PS10, Theorem 124.1], tied form: if one-way permutations exist, every language with a
Levin reduction to `3COL` has a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}` whose `n|E|`-fold repetition is an interactive proof**
(Thm-124.1; gate 03e, minor 3): from the text's hypothesis, a single one-way permutation, there
is a commitment scheme `(Com, ℓ)` (`exists_commitment_of_owp`, [PS10, Theorem 126.4] with the
hard-core predicate of Goldreich–Levin) for which the conclusion of
`zk_proof_of_levinReduction` holds: both protocols are built from `Com` and the reduction.

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem exists_commitment_zk_proof_of_owp_levinReduction
    (how : ∃ P : PermFamily, OneWayPermutation P)
    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
      EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp how
  exact ⟨Com, ℓ, hC, zk_proof_of_levinReduction hC h hLR⟩

/-- Sanity (run-3 audit P11-2): the soundness error `1 - 1/k + (1/2)^k` of the one-iteration
protocols is strictly below `1` for `k ≥ 1`, since `k < 2^k` (`Nat.lt_two_pow_self`). Hence
`EfficientProverProofErr π L R (fun N => 1 - 1/(p N) + (1/2)^{p N})` with `p N ≥ N ≥ 1`
asserts genuine soundness: the verifier rejects every `x ∉ L` with probability at least
`1/p(|x|) - 2^{-p(|x|)} > 0`. -/
theorem one_sub_inv_add_half_pow_lt_one {k : ℕ} (hk : 0 < k) :
    1 - 1 / (k : ℝ) + (1 / 2 : ℝ) ^ k < 1 := by
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast hlt
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by rw [one_div_pow]
  have h4 : 1 / (2 : ℝ) ^ k < 1 / (k : ℝ) := one_div_lt_one_div_of_lt hkpos h2
  linarith

/-- NP-hardness with Levin reductions [PS10, §4.7, Theorem 124.1, step 2, the implicit
hypothesis] (Claim-124.b/c as a hypothesis): every language with a witness relation Levin-reduces
to `(L', R')`. The string-level Levin reduction `3SAT → 3COL` that would establish
`LevinNPHard L3COL R3COL` is not formalized (plan decision on Theorem 124.1). -/
def LevinNPHard (L' : Language Bool) (R' : List Bool → List Bool → Prop) : Prop :=
  ∀ (L : Language Bool) (R : List Bool → List Bool → Prop), WitnessRelation L R →
    ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
      LevinReduction L L' R R' f w p

/-- **[PS10, Theorem 124.1], "every language in NP", for every witness relation** (Thm-124.1;
gate 03e, minors 3 and 4): under NP-hardness of `3COL` with Levin reductions, for a commitment
scheme `(Com, ℓ)` and every witness relation `R` of `L` there is a Levin reduction `(f, w)` of
`(L, R)` to `(3COL, R_3COL)` with length polynomial `p ≥ id` for which the pulled-back
one-iteration 3-colouring protocol is zero-knowledge for `R` with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`, and its `n|E|`-fold repetition is an interactive proof with
efficient prover (`zk_proof_of_levinReduction`, with `hLR` from `WitnessRelation.mem_iff`).
The Levin reduction `LevinReduction L L3COL R R3COL f w p` is part of the conclusion (ruling
R-03e-r2-1 of gate 03e round 2), so further protocols can be pulled back along the same maps.

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL)
    {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool}
    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
    ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
      LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
      EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨f, w, p, h⟩ := h3 L R hR
  exact ⟨f, w, p, h, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof", for every witness relation** (Thm-124.1; gate 03e, minors 3 and 4):
from the text's hypothesis, a one-way permutation, there is a commitment scheme
(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds
(the Levin reduction included), under NP-hardness of `3COL` with Levin reductions.

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
    (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool}
    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
      ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
        LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
        EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
        ZK ((colProtocol Com ℓ).pullback f w p) R ∧
        EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp how
  exact ⟨Com, ℓ, hC, zk_proof_of_witnessRelation h3 hC hR⟩

/-- **[PS10, Theorem 124.1], "every language in NP", one-iteration form: a zero-knowledge
protocol with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}`**, under NP-hardness of `3COL` with
Levin reductions: for a commitment scheme and every `L ∈ NP` there is a witness relation `R` for
`L` with an interactive proof with efficient prover, and a protocol that is zero-knowledge
for `R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`, where `p ≥ id` is the length polynomial of the Levin
reduction (the two protocols of `zk_proof_of_levinReduction`; the witness relation from
`exists_witnessRelation_of_mem_NP`, [PS10, Definition 191.11], supplies `hLR`). This is the
corollary of `zk_proof_of_witnessRelation`, which holds for every witness relation (gate 03e,
minor 4) and ties the two protocols together; here the conjunct
`∃ π, EfficientProverProof π L R` alone says nothing about the zero-knowledge protocol
(`npProtocol` witnesses it, minor 3).

**Repair (run-3 audit P11-2):** the run-2 conclusion `∃ s, EfficientProverProofErr π L R s`
asserted no soundness (`s := 1` turns the clause into `0 ≤ uprob …`, so it followed from the
parties' efficiency and completeness alone); the explicit error of the Levin reduction's
length polynomial is kept, together with `∀ N, N ≤ p.eval N`, so that the error is below `1`
by the noticeable margin `1/p(N) - 2^{-p(N)}` (`one_sub_inv_add_half_pow_lt_one`). -/
theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool}
    {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
  obtain ⟨_, _, p, -, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
  exact ⟨R, hR, ⟨_, h1⟩, _, p, hp, h2, h3'⟩

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof", one-iteration form: a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`**, under NP-hardness of `3COL` with Levin reductions and with the
hard-core predicate explicit (`exists_commitment_of_owp_hardCore`, `zk_proof_of_mem_NP`):
the zero-knowledge protocol has the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}`
of the Levin reduction's length polynomial `p ≥ id`.

**Repair (run-3 audit P11-2):** explicit soundness error instead of the vacuous
`∃ s, EfficientProverProofErr π L R s` (see `zk_proof_of_mem_NP`). The form for every witness
relation, from the text's hypothesis (a one-way permutation) and with the two protocols tied,
is `zk_proof_of_witnessRelation_of_owp` (gate 03e, minors 3 and 4). -/
theorem zk_proof_of_mem_NP_of_owp (h3 : LevinNPHard L3COL R3COL)
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ P.HardCore h)
    {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  exact zk_proof_of_mem_NP h3 hC hL

end TCSlib.Cryptography


/- ===== gate 07 statement sweep: seal-candidate collector (appended to the statement-only copy) =====
Walks every constant declared in this file (the current module of the statement-only copy, in which
every theorem/lemma/example value is `sorry`): the TYPE of every constant (theorems, definitions,
instances, structures and their fields/constructors/recursors, auxiliaries), and the VALUE of every
definition/instance/abbreviation/opaque (theorem values are `sorry`, so proofs contribute nothing).
Every TCSlib constant declared in another module that occurs there is classified:
* `def` (a plain, non-instance, non-reducible, non-projection, non-auxiliary, non-private
  definition): a seal candidate. Its value and its type are walked further (`deep` tier).
* instance / `@[reducible]` (incl. `abbrev`) / private / auxiliary (matcher, `_unary`, …):
  transparent or unnameable, so not sealed; recorded, and their values and types are walked.
* any other constant (theorem, structure, inductive, constructor, projection, axiom, …): its TYPE is
  walked (using a constant can make the elaborator reduce its type), it is not sealed.
`direct` = occurs in this file's types/values; `deep` = reached only through a foreign constant.
Output: SWEEP_OUT.cands.tsv, SWEEP_OUT.uses.tsv, SWEEP_OUT.transparent.tsv -/
namespace SweepCollect
open Lean
def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit
def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || numSuffix s "eq_" ||
    s == "eq_def" || s == "eq_unfold"
def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false
end SweepCollect

open Lean Meta in
run_cmd do
  let env ← getEnv
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6/proofseal/work2/TCSlib_Cryptography_ZeroKnowledge_NP.coll"
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  let kindOf (n : Name) : String :=
    match env.find? n with
    | some (.defnInfo _) =>
      if isPrivateName n then "private"
      else if SweepCollect.isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "aux"
      else if env.isProjectionFn n then "proj"
      else if isInstanceCore env n then "instance"
      else if getReducibilityStatusCore env n == .reducible then "reducible"
      else if getReducibilityStatusCore env n == .irreducible then "irreducible"
      else "def"
    | some (.thmInfo _) => "thm"
    | some (.axiomInfo _) => "axiom"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "ctor"
    | some (.recInfo _) => "rec"
    | some (.quotInfo _) => "quot"
    | none => "none"
  -- local constants of this file
  let locals := env.constants.map₂.toList.filter fun (n, _) => !(n.components.contains `SweepCollect)
  -- candidate ↦ (tier, via set, owners)
  let mut cands : Std.HashMap Name (String × NameSet × NameSet) := {}
  let mut transp : Std.HashMap Name (String × NameSet) := {}
  let mut uses : Array String := #[]
  for (ln, ci) in locals do
    -- owner: strip auxiliary components / private prefix
    let owner := (privateToUserName? ln).getD ln
    let roots : Array (Name × String) :=
      (ci.type.getUsedConstantsAsSet.toArray.map (·, "T")) ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | _ => #[])
    -- worklist: (constant, region T/V, via (anonymous = direct))
    let mut work : Array (Name × String × Name) := roots.map fun (n, r) => (n, r, Name.anonymous)
    let mut seen : Std.HashSet (Name × String) := {}
    let mut found : Array String := #[]
    while !work.isEmpty do
      let (u, r, via) := work.back!
      work := work.pop
      if seen.contains (u, r) then continue
      seen := seen.insert (u, r)
      let some j := env.getModuleIdxFor? u | continue   -- local or unknown: locals are walked as roots
      unless isTCS j do continue
      let some cu := env.find? u | continue
      let k := kindOf u
      let via' := if via.isAnonymous then u else via
      if k == "def" then
        let tier := if via.isAnonymous then "direct" else "deep"
        let (t0, vs, os) := cands.getD u (tier, {}, {})
        let t1 := if t0 == "direct" || tier == "direct" then "direct" else "deep"
        cands := cands.insert u (t1, if via.isAnonymous then vs else vs.insert via, os.insert owner)
        if via.isAnonymous then found := found.push s!"{u}@{r}"
      else if k == "instance" || k == "reducible" || k == "private" || k == "aux" || k == "proj" then
        let (m0, os) := transp.getD u (k, {})
        transp := transp.insert u (m0, os.insert owner)
      -- walk further: the type always; the value of definitions (sealed or transparent)
      for v in cu.type.getUsedConstantsAsSet.toArray do
        unless seen.contains (v, r) do work := work.push (v, r, via')
      if let .defnInfo dv := cu then
        for v in dv.value.getUsedConstantsAsSet.toArray do
          unless seen.contains (v, r) do work := work.push (v, r, via')
    if !found.isEmpty then
      uses := uses.push s!"{owner}\t{ln}\t{" ".intercalate found.toList}"
  let mut cl : Array String := #[]
  for (n, (t, vs, os)) in cands.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    let vsT := ", ".intercalate ((vs.toArray.qsort Name.lt).toList.take 3 |>.map toString)
    cl := cl.push s!"{n}\t{modNames[j.toNat]!}\t{t}\t{vsT}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".cands.tsv") ("\n".intercalate cl.toList ++ "\n")
  IO.FS.writeFile (outBase ++ ".uses.tsv") ("\n".intercalate uses.toList ++ "\n")
  let mut tl : Array String := #[]
  for (n, (k, os)) in transp.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    tl := tl.push s!"{n}\t{k}\t{modNames[j.toNat]!}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".transparent.tsv") ("\n".intercalate tl.toList ++ "\n")
  -- own-file dependency graph (for the minimiser's cascade/masking rule): for every local constant,
  -- its declaration line and the declaration lines of the local constants its type/value mentions
  let lineOf (n : Name) : Lean.Elab.Command.CommandElabM Int := do
    let mut cur := n
    for _ in [0:8] do
      if let some r ← Lean.findDeclarationRanges? cur then return (r.range.pos.line : Int)
      if let some u := privateToUserName? cur then
        if let some r ← Lean.findDeclarationRanges? u then return (r.range.pos.line : Int)
      match cur with
      | .str p _ => cur := p
      | .num p _ => cur := p
      | .anonymous => return -1
    return -1
  let localSet : NameSet := locals.foldl (fun s (n, _) => s.insert n) {}
  let mut dl : Array String := #[]
  for (ln, ci) in locals do
    -- theorem values included: top-level theorem values are `sorry` here, but the auxiliary
    -- theorems `D.proof_N` abstracted from a definition's body carry that body's proofs
    let refs := ci.type.getUsedConstantsAsSet.toArray ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray
       | _ => #[])
    let mut ls : Array Int := #[]
    for v in refs do
      if localSet.contains v && v != ln then
        let l ← lineOf v
        unless ls.contains l do ls := ls.push l
    let l0 ← lineOf ln
    dl := dl.push s!"{l0}\t{ln}\t{" ".intercalate (ls.toList.map toString)}"
  IO.FS.writeFile (outBase ++ ".deps.tsv") ("\n".intercalate dl.toList ++ "\n")
