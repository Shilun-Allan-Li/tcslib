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
  (every Levin reduction to `3COL` can be padded to this form by adding isolated vertices),
  which makes the coin and round polynomials of the pulled-back protocol `subst p` of the
  original ones and the error bounds `ε(p(|x|))`, negligible in `|x|` (`Negligible.comp_of_le`);
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
  zero-knowledge transfer along Levin reductions (Claim-124.d).
* `TCSlib.Cryptography.zk_proof_of_levinReduction` — **[PS10, Theorem 124.1], form (A)**:
  a commitment scheme and a Levin reduction to `3COL` give a zero-knowledge proof for `L`;
  `TCSlib.Cryptography.zk_proof_of_owp_levinReduction` — the same from a one-way permutation
  with a hard-core predicate (Thm-124.1).
* `TCSlib.Cryptography.zk_proof_of_mem_NP`, `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp` —
  the "every language in NP" form under `LevinNPHard L3COL R3COL`, with the explicit soundness
  error of the Levin reduction's length polynomial
  (`TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one`: the error is below `1`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.7, Karp reductions; §2.3.3, Levin reductions.)
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
assumed (achievable by padding) so that the pulled-back protocol's polynomials are `subst p`
of the original ones and its error bounds `ε(p(|x|))` are negligible in `|x|`. -/
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
        (Prod.map (coinTrunc le_rfl)
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ rfl,
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
`hπ.completeWitness` gives probability one. Completeness:
`complete x hx := let ⟨y, hy⟩ := hLR x hx; ⟨y, completeWitness x y hy⟩`. Soundness: for
`x ∉ L`, `f x ∉ L'` (`h.mem_iff`); a prover `P'` for the pulled-back protocol on `x` is the
prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen |x|)⟩` for `π` on
`f x` with the same coins (`outV_pullback_cheat`, `P*.coinLen |f x| = P'.coinLen |x|`), and
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
  refine ⟨⟨Strategy.pullback_efficient hπ.efficientV h.f_poly polyTimeComputable_pairSndD
    h.length_eq, fun x hx => ?_, fun x hx P' z => ?_⟩,
    Strategy.pullback_efficient hπ.efficientP h.f_poly h.w_poly h.length_eq, hcompl⟩
  · obtain ⟨y, hy⟩ := hLR x hx
    exact ⟨y, hcompl x y hy⟩
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
give a zero-knowledge proof for `L`** (Thm-124.1): for a commitment scheme `(Com, ℓ)` and a
Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)` with `L ⊆ witnessLanguage R` (`hLR`),
the pulled-back `n|E|`-fold 3-colouring protocol is an interactive proof for `L` with
efficient prover w.r.t. `R`, and the pulled-back one-iteration protocol is zero-knowledge for
`R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`.

**Deviation (DQ5):** the proof and the zero-knowledge statements are for the repeated and
the single-iteration protocols respectively (sequential composition, [PS10, §7.2.1], is out
of scope); the reduction is an explicit hypothesis (the text's "Cook's reduction applied to
the witness" is a Levin reduction, never defined there).

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
language with a Levin reduction to `3COL` has a zero-knowledge proof** (Thm-124.1, headline):
for `L ⊆ witnessLanguage R` (`hLR`) there is a protocol that is an interactive proof for `L`
with efficient prover w.r.t. `R`, and a protocol that is zero-knowledge for `R` and an
interactive proof with efficient prover and soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` —
the commitment scheme of [PS10, Theorem 126.4] (`exists_commitment_of_owp_hardCore`) plugged
into `zk_proof_of_levinReduction`.

**Deviation:** hard-core predicate explicit (source error 47); single OWP rather than a
collection; see `zk_proof_of_levinReduction` for the two-protocol form (DQ5).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`zk_proof_of_levinReduction`). -/
theorem zk_proof_of_owp_levinReduction
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h)
    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ π : Protocol, ZK π R ∧ EfficientProverProofErr π L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  obtain ⟨h1, h2, h3⟩ := zk_proof_of_levinReduction hC h hLR
  exact ⟨⟨_, h1⟩, _, h2, h3⟩

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

/-- **[PS10, Theorem 124.1], "every language in NP"**, under NP-hardness of `3COL` with Levin
reductions: for a commitment scheme and every `L ∈ NP` there is a witness relation `R` for
`L` with an interactive proof with efficient prover, and a protocol that is zero-knowledge
for `R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`, where `p ≥ id` is the length polynomial of the Levin
reduction (the two protocols of `zk_proof_of_levinReduction`; the witness relation from
`exists_witnessRelation_of_mem_NP`, [PS10, Definition 191.11], supplies `hLR`).

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
  obtain ⟨f, w, p, h⟩ := h3 L R hR
  obtain ⟨h1, h2, h3'⟩ := zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx
  exact ⟨R, hR, ⟨_, h1⟩, _, p, h.le_eval, h2, h3'⟩

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof"**, under NP-hardness of `3COL` with Levin reductions and with the
hard-core predicate explicit (`exists_commitment_of_owp_hardCore`, `zk_proof_of_mem_NP`):
the zero-knowledge protocol has the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}`
of the Levin reduction's length polynomial `p ≥ id`.

**Repair (run-3 audit P11-2):** explicit soundness error instead of the vacuous
`∃ s, EfficientProverProofErr π L R s` (see `zk_proof_of_mem_NP`). -/
theorem zk_proof_of_mem_NP_of_owp (h3 : LevinNPHard L3COL R3COL)
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h)
    {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  exact zk_proof_of_mem_NP h3 hC hL

end TCSlib.Cryptography
