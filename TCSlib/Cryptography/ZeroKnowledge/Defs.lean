/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge: honest-verifier, general, statistical and perfect

The zero-knowledge notions of [PS10, §4.6] on top of the interaction model of
`Interaction.lean` (foundation decision D8): honest-verifier zero-knowledge
[PS10, Definition 121.1], zero-knowledge against every efficient verifier
[PS10, Definition 121.2], and the perfect and statistical variants (Def-122.a) through the
sup-over-test-sets closeness `StatClose` of `Asymptotic/Sampling.lean`, together with the
implications statistical ⇒ computational (`StatZK.zk`, `StatZK.hvzk`), general ⇒ honest-verifier
(`ZK.hvzk`), and the negligibility bookkeeping converting the chapter's per-vertex bounds
`2^{-n}`, `e^{-n}` into functions of the instance length `|x|` (Inf-4.4).

The simulator is a uniform `Complexity.NUPPT` run once at parameter `|x|` on `⟨x, z⟩`
(`Complexity.NUPPT.simulate`); its output is a word read as an encoded view
(`View.encode`: `⟨⟨x, z⟩, ⟨r, messages⟩⟩`), and the distinguisher is a non-uniform PPT run at
parameter `|x|` on the encoded view (`Complexity.NUPPT.distinguisherL`).

**Deviation (D8):** strict PPT simulators (the text's expected polynomial time is not
formalized; the rewinding simulators of the chapter are truncated and the theorems become
statistical); the auxiliary input of the verifier is bounded by an arbitrary polynomial
`Lz : PolyExpr` quantified after the simulator (the class a `t(|x|)`-time verifier can read,
and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the error bound is
a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
stated for a protocol and a witness relation without assuming the proof property, which the
theorems add separately.
The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e,
note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the
encoded view, which contains `z`. With `|z|` exponential in `ℓ(n)` it can open the perfectly
binding commitments by exhaustive search. On a graph with two proper colourings outside one
colour-permutation orbit, that tells the two real views apart with advantage 1, while the
simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every
`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol.
Protocols with exactly simulable views are not affected. For the same reason the
distinguisher's advice is indexed by the parameter `|x|`, not by its input length.

**Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
or `PerfectZKAbort` (see their docstrings). The source's perfect zero-knowledge protocol,
graph isomorphism [PS10, Theorem 122.3], is formalized as `StatZK` with negligible error
(`gi_statZK`, `ZeroKnowledge/GraphIsomorphismZK.lean`), the substantive instance of the
notions of this file; `perfectZK_zeroRounds` is a degenerate one. The abort form implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), by running the
aborting simulator `|x|` times on fresh coins (`AbortRetry.retry`).

## Main definitions

* `Complexity.NUPPT.simulate` — the simulator's output on `(x, z)`.
* `TCSlib.Cryptography.HVZK` — honest-verifier zero-knowledge [PS10, Definition 121.1]
  (Def-121.1).
* `TCSlib.Cryptography.ZK` — zero-knowledge [PS10, Definition 121.2] (Def-121.2).
* `TCSlib.Cryptography.StatZK`, `TCSlib.Cryptography.PerfectZK`,
  `TCSlib.Cryptography.PerfectZKAbort` — statistical zero-knowledge with error `δ(|x|)`,
  perfect zero-knowledge (`δ = 0`), and the abort form of perfect zero-knowledge
  [Gol01, Definition 4.3.1] (Def-122.a).
* `TCSlib.Cryptography.AbortRetry.attempt`, `TCSlib.Cryptography.AbortRetry.retry` — one
  attempt of an aborting simulator on a coin block, and the simulator that retries it `|x|`
  times (as functions of the machine layout).

## Main results

* `TCSlib.Cryptography.StatZK.zk`, `TCSlib.Cryptography.StatZK.hvzk` — statistical
  zero-knowledge with negligible error implies zero-knowledge and honest-verifier
  zero-knowledge (`distAdv_le_of_statClose`).
* `TCSlib.Cryptography.ZK.hvzk` — zero-knowledge implies honest-verifier zero-knowledge.
* `TCSlib.Cryptography.PerfectZK.zk`, `TCSlib.Cryptography.StatZK.mono` — perfect
  zero-knowledge is zero-knowledge; weakening the error.
* `TCSlib.Cryptography.perfectZK_zeroRounds` — non-vacuity: the protocol with no messages is
  perfectly zero-knowledge.
* `TCSlib.Cryptography.PerfectZKAbort.statZK`, `TCSlib.Cryptography.PerfectZKAbort.zk` — the
  abort form implies statistical zero-knowledge with error `2^{-|x|}`, hence zero-knowledge
  (`TCSlib.Cryptography.AbortRetry.statClose_retry`: the first non-`⊥` output of `K`
  independent runs of an aborting sampler is `2^{-K}`-close to its conditional law;
  `TCSlib.Cryptography.AbortRetry.exists_retrySimulator`: the retrying simulator is a uniform
  PPT, by `EncodingMachines.polyTimeComputable_firstIdx`, an instance of
  `Complexity.polyTimeComputable_iterateFind`).
* `TCSlib.Cryptography.negligible_inv_pow_sqrt_div`,
  `TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_exp_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div` — `a^{-√(N/C)}` is negligible
  in `N` (Inf-4.4): the per-vertex bounds of the graph protocols are negligible in `|x|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge, pp. 120–122.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Simulators -/

/-- The simulator's output on `(x, z)` [PS10, Definitions 121.1 and 121.2, `S(x, z)`]: one
activation of `S` at parameter `|x|` on `⟨x, z⟩`, a word read as an encoded view. -/
def _root_.Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) :
    List Bool :=
  S.runAt x.length (pairEncode x z) r

/-- `simulate` unfolds to the typed activation at parameter `|x|`. -/
theorem _root_.Complexity.NUPPT.simulate_eq (S : NUPPT) (x z : List Bool)
    (r : S.Coins x.length) : S.simulate x z r = S.runAt x.length (pairEncode x z) r := rfl

/-! ### Honest-verifier and general zero-knowledge -/

/-- Honest-verifier zero-knowledge of `π` for the witness relation `R`
[PS10, Definition 121.1] (Def-121.1): there is a uniform PPT simulator `S` such that for every
auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a negligible `ε`
with, for all `x`, witnesses `y` of `x` and auxiliary inputs `z` of length `≤ Lz(|x|)`, the
advantage of `D` (at parameter `|x|`) between the honest verifier's view of
`P(x, y) ↔ V(x, z)` and `S(x, z)` at most `ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. -/
def HVZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤
        ε x.length

/-- Zero-knowledge of `π` for the witness relation `R` [PS10, Definition 121.2] (Def-121.2):
for every efficient verifier strategy `V'` there is a uniform PPT simulator `S` such that for
every auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a
negligible `ε` with, for all `x`, witnesses `y` and auxiliary inputs `z` of length `≤ Lz(|x|)`,
the advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
`ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. The
cheating verifier `V'` is only `Efficient`, with no message-prefix cap (question Q-1 of
gate 03, ruled: no cap on `V*`), so its class is larger than the text's. Since the honest
prover's messages are polynomially bounded in `|x|` in the proof systems
(`Protocol.ProverBounded`, ruling G3-3 of gate 03), the view of every efficient `V'` — `x`,
`z`, its tape and the honest prover's messages — is polynomially bounded all the same. -/
def ZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
    ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
        distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z)
          (D.distinguisherL x.length) ≤ ε x.length

/-- The defining property of `ZK`: `ZK π R` iff for every efficient `V'` there is a uniform
simulator `S` such that for every `Lz` and every distinguisher `D` some negligible `ε` bounds
`distAdv (view of V' in P(x, y) ↔ V'(x, z)) (S(x, z)) (D at |x|) ≤ ε(|x|)` for all `x`, `y` with
`R x y`, and `z` with `|z| ≤ Lz(|x|)`. -/
theorem ZK_iff (π : Protocol) (R : List Bool → List Bool → Prop) :
    ZK π R ↔ ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
      ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
          distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z)
            (D.distinguisherL x.length) ≤ ε x.length := Iff.rfl

/-- Statistical zero-knowledge of `π` for `R` with error `δ(|x|)` (Def-122.a, campaign
addition needed for the truncated simulators): for every efficient `V'` there is a uniform PPT
simulator whose output on `(x, z)` is `StatClose` (every test set, sup form) within `δ(|x|)`
to the view of `V'` in `P(x, y) ↔ V'(x, z)`, for all `x`, witnesses `y` and all auxiliary
inputs `z`.

**Deviation (D8):** strict PPT simulator; the bound is in `|x|`. -/
def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)

/-- Perfect zero-knowledge [PS10, §4.6, "perfect zero-knowledge"] (Def-122.a): statistical
zero-knowledge with error `0`, i.e. the simulator's output has exactly the law of the view.

**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion. A
strict simulator with bit coins outputs every string with a dyadic probability, and an
honest prover drawing polynomially many fair coins cannot draw a uniform permutation of
`n ≥ 3` points (`n! ∤ 2^c`), so the reply of the honest graph-isomorphism prover
[PS10, Protocol 120.6] depends on the witness. [PS10, Theorem 122.3] is formalized as
`StatZK` with negligible error (`gi_statZK`); the instances of this notion are degenerate
(`perfectZK_zeroRounds`). -/
def PerfectZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  StatZK π R (fun _ => 0)

/-- Perfect zero-knowledge with abort [Gol01, Definition 4.3.1] (Def-122.a, the GMR form):
for every efficient `V'` there is a uniform PPT simulator that outputs `⊥ = []` with
probability at most `1/2` and whose output, conditioned on not aborting, has exactly the law
of the view of `V'`: for every test set `T`,
`Pr[T(view)] · Pr[S ≠ ⊥] = Pr[S ≠ ⊥ ∧ T(S)]` (`⊥ = []` is never a view encoding).

**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion:
as for `PerfectZK`, the honest graph-isomorphism prover's permutation, drawn from fair coins,
is not uniform, so its reply depends on the witness, which no simulator sees. The abort form
holds for ideal permutations at the concrete layer (`giSimAttempt_perfectAbort`). It implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), hence
zero-knowledge (`PerfectZKAbort.zk`); the source's "perfect" results are stated as `StatZK`
with negligible error. -/
def PerfectZKAbort (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1 / 2 ∧
    ∀ T : List Bool → Prop,
      uprob (fun r : (π.withV V').ExecCoins π.P x => T ((π.withV V').viewV x y z r).encode) *
          uprob (fun r : S.Coins x.length => S.simulate x z r ≠ []) =
        uprob (fun r : S.Coins x.length => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))

/-! ### Implications between the notions -/

/-- Statistical zero-knowledge with negligible error implies zero-knowledge
[PS10, §4.6, perfect/statistical ⇒ computational]: the same simulator works for every
distinguisher, with `ε := δ`, since a distinguisher's advantage between `δ`-close samplers is
at most `δ` (`distAdv_le_of_statClose`, [Gar26, Lemma 3.1]). -/
theorem StatZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ =>
    distAdv_le_of_statClose _ _ (hclose x y z hR) _⟩⟩

/-- Statistical zero-knowledge with negligible error implies honest-verifier zero-knowledge
when the honest verifier is efficient: instantiate `V' := V` (`Protocol.withV_self`) and
apply `distAdv_le_of_statClose`. -/
theorem StatZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R := by
  obtain ⟨S, hS, hclose⟩ := h π.V hV
  refine ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ => ?_⟩⟩
  have hc := hclose x y z hR
  rw [Protocol.withV_self] at hc
  exact distAdv_le_of_statClose _ _ hc _

/-- Zero-knowledge implies honest-verifier zero-knowledge when the honest verifier is
efficient [PS10, §4.6, after Definition 121.2]: instantiate `V' := V`. -/
theorem ZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} (hV : π.V.Efficient)
    (h : ZK π R) : HVZK π R := by
  obtain ⟨S, hS, hsim⟩ := h π.V hV
  refine ⟨S, hS, fun Lz D => ?_⟩
  obtain ⟨ε, hε, hadv⟩ := hsim Lz D
  refine ⟨ε, hε, fun x y z hR hz => ?_⟩
  have hc := hadv x y z hR hz
  rwa [Protocol.withV_self] at hc

/-- Weakening the statistical error. -/
theorem StatZK.mono {π : Protocol} {R : List Bool → List Bool → Prop} {δ δ' : ℕ → ℝ}
    (h : StatZK π R δ) (hle : ∀ n, δ n ≤ δ' n) : StatZK π R δ' := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun x y z hR => (hclose x y z hR).mono (hle _)⟩

/-- The zero function is negligible. -/
theorem negligible_const_zero : Negligible (fun _ => (0 : ℝ)) := fun c =>
  ⟨1, fun n hn => by
    rw [abs_zero]
    exact one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr hn) c)⟩

/-- Perfect zero-knowledge is statistical zero-knowledge with error `0`. -/
theorem PerfectZK.statZK {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    StatZK π R (fun _ => 0) := h

/-- Perfect zero-knowledge implies zero-knowledge [PS10, §4.6]. -/
theorem PerfectZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    ZK π R :=
  StatZK.zk negligible_const_zero h

/-- Non-vacuity (gate 03e, note 10): the protocol with no messages is perfectly
zero-knowledge for every relation.

**Proof sketch.** The view of any `V'` is `⟨x, z, r, []⟩` (no moves, `exec_zero`), and the
simulator `NUPPT.ofPolyTimeUniform` of the layout map `w ↦ ⟨inArg w, ⟨inCoins w, []⟩⟩` with
`V'`'s coin polynomial outputs `⟨⟨x, z⟩, ⟨r, []⟩⟩` on its own tape `r`; the prover's tape does
not enter the view (`uprob_fst` after `Equiv.prodComm`), so the two laws coincide. -/
theorem perfectZK_zeroRounds (P V : Strategy) (b : Bool) (R : List Bool → List Bool → Prop) :
    PerfectZK ⟨P, V, .const 0, b⟩ R := by
  intro V' _
  have hF : PolyTimeComputable fun w =>
      pairEncode (NUPPT.inArg w) (pairEncode (NUPPT.inCoins w) []) :=
    NUPPT.polyTimeComputable_inArg.pairEncode
      (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const []))
  refine ⟨NUPPT.ofPolyTimeUniform hF V'.coins, NUPPT.ofPolyTimeUniform_uniform hF _,
    fun x y z _ T => ?_⟩
  have h1 : uprob (fun r : (Protocol.withV ⟨P, V, .const 0, b⟩ V').ExecCoins P x =>
      T ((Protocol.withV ⟨P, V, .const 0, b⟩ V').viewV x y z r).encode) =
      uprob (fun ρ : V'.Coins x.length =>
        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
    rw [← uprob_comp_equiv (Equiv.prodComm _ _)]
    exact uprob_fst (fun ρ : V'.Coins x.length =>
      T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) [])))
  have h2 : uprob (fun ρ : (NUPPT.ofPolyTimeUniform hF V'.coins).Coins x.length =>
      T ((NUPPT.ofPolyTimeUniform hF V'.coins).simulate x z ρ)) =
      uprob (fun ρ : V'.Coins x.length =>
        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
    refine OneWay.uprob_congr fun ρ => ?_
    rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
    simp [NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
  simp only [h2]
  rw [abs_nonpos_iff, sub_eq_zero]
  exact h1

/-! ### Retrying an aborting simulator -/

namespace AbortRetry

open EncodingMachines Finset Complexity.StateLoop

/-- One attempt of the retrying simulator on its machine layout
`w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩` at the index `t`: the simulator `S` at parameter `n = |1^n|` on the
argument `y`, with empty advice and the `t`-th block of `S.coinLen n` coins of `r`. -/
def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
  S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
    (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
      (S.coinLen (NUPPT.inParam w).length)))

/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
`inParam w`, argument `inArg w`, empty advice and coins
`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
        (S.coinLen (NUPPT.inParam w).length))) :=
  rfl

/-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
(for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
`EncodingMachines.firstIdx`), or `⊥` if every attempt aborts. -/
noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
  if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
      (NUPPT.inParam w).length then
    attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
  else []

/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
attempt `i` if `i < N`, and `[]` otherwise. -/
theorem retry_eq (S : NUPPT) (w : List Bool) :
    retry S w =
      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
          (NUPPT.inParam w).length then
        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
      else [] :=
  rfl

/-- If attempt `i < |inParam w|` is the first that does not abort (`attempt S w i ≠ []`, and
`attempt S w j = []` for every `j < i`), then `retry S w` is attempt `i`.

**Proof sketch.** `firstIdx` of the non-abort test is `i` (`firstIdx_eq_of`); rewrite
`retry_eq` with it and take the `i < |inParam w|` branch. -/
theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
  rw [retry_eq, h, if_pos hi]

/-- If all `|inParam w|` attempts abort (`attempt S w t = []` for every `t < |inParam w|`),
then `retry S w = []`. Together with `retry_eq_attempt` this covers every input.

**Proof sketch.** `firstIdx` of the non-abort test is `|inParam w|` (`firstIdx_eq_of_forall`);
rewrite `retry_eq` with it and take the `else` branch. -/
theorem retry_eq_nil {S : NUPPT} {w : List Bool}
    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
      (NUPPT.inParam w).length :=
    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
  rw [retry_eq, h', if_neg (lt_irrefl _)]

/-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.

**Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
(`unaryPoly_comp`, `unaryMul_poly`, `polyTimeComputable_pairDropPoly`, `truncate_poly`), the
layout (`NUPPT.polyTimeComputable_layout`) and the machine of `S`
(`NUPPT.polyTimeComputable_output`). -/
theorem attempt_poly (S : NUPPT) :
    PolyTimeComputable fun u => attempt S (pairSndD u) (pairFstD u).length := by
  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
  have hpar : PolyTimeComputable fun u => NUPPT.inParam (pairSndD u) :=
    NUPPT.polyTimeComputable_inParam.comp polyTimeComputable_pairSndD
  have hr : PolyTimeComputable fun u => NUPPT.inCoins (pairSndD u) :=
    NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD
  have hc : PolyTimeComputable fun u =>
      List.replicate (S.coinLen (NUPPT.inParam (pairSndD u)).length) true :=
    unaryPoly_comp S.coins hpar
  have ht : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD u)).drop
      ((pairFstD u).length * S.coinLen (NUPPT.inParam (pairSndD u)).length) :=
    congr ((polyTimeComputable_pairDropPoly .var).comp ((unaryMul_poly ht hc).pairEncode hr))
      fun u => by simp
  have hblk := truncate_poly hdrop hc
  have hlay := NUPPT.polyTimeComputable_layout hpar
    (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_const []) hblk
  exact congr (S.polyTimeComputable_output.comp hlay) fun u => rfl

/-- **The retrying simulator is polynomial-time** as a function of its layout: the first
non-aborting index is `EncodingMachines.polyTimeComputable_firstIdx` (an instance of the
repetition lemma `Complexity.polyTimeComputable_iterateFind`) with the test of
`attempt_poly`, and the output is that attempt (`attempt_poly` at the found index) or `[]`
(`polyTimeComputable_ite`). -/
theorem retry_poly (S : NUPPT) : PolyTimeComputable (retry S) := by
  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
  have hatt := attempt_poly S
  have hp : PolyTimeComputable fun u =>
      [decide (attempt S (pairSndD u) (pairFstD u).length ≠ [])] :=
    congr (ltTest_poly (unaryConst_poly 0) (unaryLength_poly hatt)) fun u => by
      simp [List.length_pos_iff]
  have hN : PolyTimeComputable fun w => List.replicate (NUPPT.inParam w).length true :=
    unaryLength_poly NUPPT.polyTimeComputable_inParam
  have hidx := polyTimeComputable_firstIdx (p := fun w t => decide (attempt S w t ≠ [])) hp hN
  have hsel : PolyTimeComputable fun w => attempt S w
      (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) :=
    congr (hatt.comp (hidx.pairEncode polyTimeComputable_id)) fun w => by simp
  refine congr (polyTimeComputable_ite (ltTest_poly hidx hN) hsel (polyTimeComputable_const []))
    fun w => ?_
  simp only [retry, decide_eq_true_eq]

/-- **The retrying simulator is a uniform PPT**: `NUPPT.ofPolyTimeUniform` of `retry_poly`
with `|x|` blocks of `S.coinLen |x|` coins; on `(x, z)` it computes `retry S` on the layout
`⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem exists_retrySimulator (S : NUPPT) :
    ∃ S' : NUPPT, S'.Uniform ∧ S'.coins = .mul .var S.coins ∧
      ∀ x z (r : S'.Coins x.length), S'.simulate x z r =
        retry S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) :=
  ⟨NUPPT.ofPolyTimeUniform (retry_poly S) (.mul .var S.coins),
    NUPPT.ofPolyTimeUniform_uniform _ _, rfl, fun x z r => by
      rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
      rfl⟩

/-- The first hit of `K` draws read through `EncodingMachines.firstIdx`: if `a t` is `g` of
the `t`-th draw and `q t` tests `E` on it (for `t < K`), then the first hit mapped by `g` and
defaulted to `d` is `a` at the first index accepted by `q`, or `d` if there is none.

**Proof sketch.** If `i := firstIdx q K < K`, the draw `i` is in `E` (`q_firstIdx`) and no
earlier draw is (`firstIdx_min`); splitting `List.finRange K` at `i`
(`List.drop_eq_getElem_cons`, `List.take_append_drop`, `List.getElem_finRange`) gives
`firstHit E xs = some (xs i)` by `List.findSome?_eq_some_iff`. Otherwise no draw is in `E`
(`firstIdx_eq_iff`) and `firstHit E xs = none` (`firstHit_eq_none_iff`). -/
theorem firstHit_map_getD_eq {α β : Type*} (E : α → Prop) [DecidablePred E] {K : ℕ}
    (xs : Fin K → α) (g : α → β) (d : β) (a : ℕ → β) (q : ℕ → Bool)
    (ha : ∀ t (ht : t < K), a t = g (xs ⟨t, ht⟩))
    (hq : ∀ t (ht : t < K), q t = decide (E (xs ⟨t, ht⟩))) :
    ((firstHit E xs).map g).getD d = if firstIdx q K < K then a (firstIdx q K) else d := by
  split_ifs with h
  · set i := firstIdx q K with hi_def
    have hEi : E (xs ⟨i, h⟩) := by
      have := q_firstIdx h
      rw [hq i h] at this
      exact of_decide_eq_true this
    have hmin : ∀ j (hj : j < i), ¬ E (xs ⟨j, hj.trans h⟩) := fun j hj hE => by
      have := firstIdx_min hj
      rw [hq j (hj.trans h)] at this
      exact absurd (decide_eq_true hE) (by rw [this]; decide)
    have hsome : firstHit E xs = some (xs ⟨i, h⟩) := by
      unfold firstHit
      rw [List.findSome?_eq_some_iff]
      refine ⟨(List.finRange K).take i, ⟨i, h⟩, (List.finRange K).drop (i + 1), ?_, ?_, ?_⟩
      · have hlen : i < (List.finRange K).length := by simpa using h
        have hsplit : List.finRange K = (List.finRange K).take i ++
            (List.finRange K)[i] :: (List.finRange K).drop (i + 1) := by
          rw [← List.drop_eq_getElem_cons hlen, List.take_append_drop]
        rw [List.getElem_finRange] at hsplit
        exact hsplit
      · simp [hEi]
      · intro j hj
        obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 hj
        have hki : k < i := lt_of_lt_of_le hk (min_le_left _ _)
        simp [hmin k hki]
    rw [hsome, ha i h]
    rfl
  · have hall := firstIdx_eq_iff.1 (le_antisymm firstIdx_le (not_lt.1 h))
    have hnone : firstHit E xs = none := (firstHit_eq_none_iff E xs).2 fun t hE => by
      have := hall t t.isLt
      rw [hq t t.isLt] at this
      exact absurd (decide_eq_true hE) (by rw [this]; decide)
    rw [hnone]
    rfl

/-- **Retrying an aborting sampler** (amplification by repetition): let `g` be a
sampler on a finite uniform space `Ω`, `E` the event "`g` does not abort", with
`Pr[¬ E] ≤ 1/2`, and suppose the output of `g` conditioned on `E` has the law of the sampler
`Y`. Then the output of `g` on the first of `K` independent draws in `E` (the default `d₀` if
there is none) is within `2^{-K}` of `Y`.

**Proof sketch.** Let `p := Pr[E] ≥ 1/2` and `f := (1 - p)^K`, the probability that no draw
is in `E` (`uprob_firstHit_none`). Each `a ∈ E` is the first hit with the same probability
`q₀` (`firstHit_uniform_of_some`), so for a test set `T`, splitting over the fibres of
`firstHit` (`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`),
`Pr[T(retry)] = [T d₀] · f + q₀ · #{a ∈ E : T (g a)}`, and with `T := ⊤`,
`1 = f + q₀ · #E`. The conditional-law hypothesis times `|Ω|` is
`Pr[T(Y)] · #E = #{a ∈ E : T (g a)}`, so `Pr[T(retry)] = [T d₀] · f + (1 - f) · Pr[T(Y)]`
(`linear_combination`) and `|Pr[T(Y)] - Pr[T(retry)]| = f · |Pr[T(Y)] - [T d₀]| ≤ f ≤ 2^{-K}`. -/
theorem statClose_retry {Ω τ : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype τ]
    (E : Ω → Prop) [DecidablePred E] (g : Ω → List Bool) (Y : τ → List Bool) (d₀ : List Bool)
    (habort : uprob (fun ω => ¬ E ω) ≤ 1 / 2)
    (hcond : ∀ T : List Bool → Prop,
      uprob (fun t => T (Y t)) * uprob E = uprob (fun ω => E ω ∧ T (g ω)))
    (K : ℕ) :
    StatClose Y (fun ws : Fin K → Ω => ((firstHit E ws).map g).getD d₀) ((2 : ℝ)⁻¹ ^ K) := by
  classical
  intro T
  have hpE : uprob E = 1 - uprob (fun ω => ¬ E ω) := by rw [uprob_not]; ring
  obtain ⟨d, hd⟩ : ∃ d, E d := by
    by_contra hne
    push_neg at hne
    have h0 : uprob E = 0 := by
      rw [← uprob_false (α := Ω)]
      exact OneWay.uprob_congr fun ω => ⟨fun h => hne ω h, False.elim⟩
    linarith
  have hsome : ∀ a, E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) =
      uprob (fun xs : Fin K → Ω => firstHit E xs = some d) :=
    fun a ha => firstHit_uniform_of_some E K ha hd
  have hnot : ∀ a, ¬ E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) = 0 := by
    intro a ha
    rw [← uprob_false (α := Fin K → Ω)]
    exact OneWay.uprob_congr fun xs => ⟨fun h => ha (firstHit_eq_some_imp E h), False.elim⟩
  have hdec : ∀ S' : Option Ω → Prop, uprob (fun xs : Fin K → Ω => S' (firstHit E xs)) =
      (if S' none then (1 - uprob E) ^ K else 0) +
        uprob (fun xs : Fin K → Ω => firstHit E xs = some d) *
          (univ.filter fun a => E a ∧ S' (some a)).card := by
    intro S'
    rw [uprob_comp_eq_sum_fiber (firstHit E) S', sum_filter, Fintype.sum_option,
      uprob_firstHit_none E K]
    congr 1
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hSa : S' (some a)
    · by_cases hEa : E a
      · simp [hSa, hEa, hsome a hEa]
      · simp [hSa, hEa, hnot a hEa]
    · simp [hSa]
  have hsim := hdec fun o => T ((o.map g).getD d₀)
  have htot := hdec fun _ => True
  rw [uprob_true] at htot
  simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, if_true,
    and_true] at hsim htot
  -- the conditional law in counting form
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc := hcond T
  rw [uprob_eq_card_filter E, uprob_eq_card_filter (fun ω => E ω ∧ T (g ω)), mul_div_assoc',
    div_left_inj' hcard] at hc
  generalize uprob (fun xs : Fin K → Ω => firstHit E xs = some d) = q₀ at hsim htot
  generalize hf : (1 - uprob E) ^ K = f at hsim htot
  have hY0 := uprob_nonneg (fun t => T (Y t))
  have hY1 := uprob_le_one (fun t => T (Y t))
  have hsimeq : uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀)) =
      (if T d₀ then f else 0) + (1 - f) * uprob (fun t => T (Y t)) := by
    rw [hsim]
    linear_combination (-q₀) * hc + (-uprob (fun t => T (Y t))) * htot
  have hf0 : 0 ≤ f := hf ▸ pow_nonneg (by linarith [uprob_le_one E]) K
  have hfK : f ≤ (2 : ℝ)⁻¹ ^ K :=
    hf ▸ pow_le_pow_left₀ (by linarith [uprob_le_one E]) (by linarith) K
  show |uprob (fun t => T (Y t)) -
    uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀))| ≤ (2 : ℝ)⁻¹ ^ K
  rw [hsimeq, abs_le]
  split_ifs <;> constructor <;> nlinarith

/-- The probability that the retrying simulator's attempt aborts is the complement of its
success probability (a restatement of `PerfectZKAbort`'s first clause for
`AbortRetry.statClose_retry`). -/
theorem uprob_not_ne_nil_le {Ω : Type*} [Fintype Ω] (g : Ω → List Bool)
    (h : uprob (fun ω => g ω = []) ≤ 1 / 2) : uprob (fun ω => ¬ g ω ≠ []) ≤ 1 / 2 := by
  simpa using h

end AbortRetry

open AbortRetry in
/-- **Perfect zero-knowledge with abort implies statistical zero-knowledge with error
`2^{-|x|}`** (the abort form of [Gol01, Definition 4.3.1], amplified by repetition)
(ruling G3-4 of gate 03): retry the aborting simulator on `|x|` disjoint coin blocks and
output the first non-`⊥` result.

**Proof sketch.** For an efficient `V'` take the aborting simulator `S` of `h`; the
retrying simulator `S'` of `AbortRetry.exists_retrySimulator` is a uniform PPT with `|x|`
blocks of `S.coinLen |x|` coins. Read its tape as `|x|` independent blocks (the bijection
`e` built from `finCongr`, `finProdFinEquiv` and `Equiv.curry`, through
`StatClose.comp_equiv_right`): the `t`-th slice of the tape is `List.ofFn` of block `t`, so
attempt `t` is `S` on block `t` (`S` is uniform, so its advice is `[]`), and the retrying
simulator is the first non-`⊥` attempt (`AbortRetry.firstHit_map_getD_eq`). The two clauses
of `h` are the hypotheses of `AbortRetry.statClose_retry` with `K = |x|`. -/
theorem PerfectZKAbort.statZK {π : Protocol} {R : List Bool → List Bool → Prop}
    (h : PerfectZKAbort π R) : StatZK π R (fun n => (2 : ℝ)⁻¹ ^ n) := by
  intro V' hV'
  obtain ⟨S, hSu, hS⟩ := h V' hV'
  obtain ⟨S', hS'u, hS'c, hS'⟩ := exists_retrySimulator S
  refine ⟨S', hS'u, fun x y z hxy => ?_⟩
  obtain ⟨habort, hcond⟩ := hS x y z hxy
  have hlen : S'.coinLen x.length = x.length * S.coinLen x.length := by
    simp only [NUPPT.coinLen, hS'c, PolyExpr.eval_mul, PolyExpr.eval_var]
  -- the tape of `S'` as `|x|` blocks of `S.coinLen |x|` coins
  let e : S'.Coins x.length ≃ (Fin x.length → S.Coins x.length) :=
    ((Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
      (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool))).trans (Equiv.curry _ _ _)
  have hblock : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
      ((List.ofFn r).drop (t * S.coinLen x.length)).take (S.coinLen x.length) =
        List.ofFn (e r ⟨t, ht⟩) := by
    intro r t ht
    have hle : t * S.coinLen x.length + S.coinLen x.length ≤ x.length * S.coinLen x.length := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ ht
    refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
    · simp only [List.length_take, List.length_drop, List.length_ofFn, hlen]
      omega
    · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
        Function.comp_apply, Equiv.symm_symm, Equiv.curry_apply, Function.curry_apply]
      congr 1
      ext
      simp [finProdFinEquiv]
      ring
  have hatt : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
      attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t =
        S.simulate x z (e r ⟨t, ht⟩) := by
    intro r t ht
    simp only [attempt, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
      List.length_replicate]
    rw [hblock r t ht, NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, hSu]
  have heq : ∀ r : S'.Coins x.length, S'.simulate x z r =
      ((firstHit (fun ω => S.simulate x z ω ≠ []) (e r)).map (S.simulate x z)).getD [] := by
    intro r
    rw [hS' x z r, firstHit_map_getD_eq (fun ω => S.simulate x z ω ≠ []) (e r)
      (S.simulate x z) []
      (attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)))
      (fun t => decide (attempt S
        (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t ≠ []))
      (hatt r) (fun t ht => by simp only [hatt r t ht])]
    simp only [retry, NUPPT.inParam_layout, List.length_replicate]
  have key := (statClose_retry (fun ω => S.simulate x z ω ≠ []) (S.simulate x z)
    (fun r : (π.withV V').ExecCoins π.P x => ((π.withV V').viewV x y z r).encode) []
    (uprob_not_ne_nil_le _ habort) hcond x.length).comp_equiv_right e
  intro T
  have hu : uprob (fun t : S'.Coins x.length => T (S'.simulate x z t)) =
      uprob (fun t : S'.Coins x.length => T (((firstHit (fun ω => S.simulate x z ω ≠ []) (e t)).map
        (S.simulate x z)).getD [])) :=
    OneWay.uprob_congr fun t => by rw [heq t]
  rw [hu]
  exact key T

/-- **Perfect zero-knowledge with abort implies zero-knowledge** (ruling G3-4 of gate 03):
`PerfectZKAbort.statZK` and `StatZK.zk` with the negligible error `2^{-n}`
(`negligible_two_pow_neg`). -/
theorem PerfectZKAbort.zk {π : Protocol} {R : List Bool → List Bool → Prop}
    (h : PerfectZKAbort π R) : ZK π R :=
  h.statZK.zk negligible_two_pow_neg

/-! ### Negligibility in the instance length (Inf-4.4) -/

/-- For `a > 1` and `C > 0` the function `N ↦ a^{-√(N / C)}` (with `Nat.sqrt` and natural
division) is negligible in `N` (Inf-4.4): the per-vertex error bounds `2^{-n}` and `e^{-n}` of
the graph protocols, whose instances have length `|x| ≥ n² / C`, are negligible in `|x|`.

**Proof sketch.** Fix `c`. Put `t := Nat.sqrt (N / C)`; then `N / C < (t + 1)²`
(`Nat.lt_succ_sqrt`), so `N < C (t + 1)² + C ≤ 2 C (t + 1)²` and
`N ^ c ≤ (2 C)^c (t + 1)^{2c}`. By `tendsto_pow_const_div_const_pow_of_one_lt`
(as in `negligible_two_pow_neg`), `(t + 1)^{2c} / a^{t+1} → 0`, so there is `t₀` with
`(2 C)^c · a · (t + 1)^{2c} < a^{t+1}` for `t ≥ t₀`, i.e. `(2C)^c (t+1)^{2c} < a^t`; and
`t ≥ t₀` as soon as `N ≥ C (t₀ + 1)²` (`Nat.le_sqrt`). Hence for such `N`,
`a⁻¹ ^ t = 1 / a^t < 1 / ((2C)^c (t+1)^{2c}) ≤ 1 / N^c`. -/
theorem negligible_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C) :
    Negligible fun N => a⁻¹ ^ Nat.sqrt (N / C) := by
  intro c
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans ha
  have hCr : (0 : ℝ) < (C : ℝ) ^ c := by positivity
  have hpos : (0 : ℝ) < 1 / ((C : ℝ) ^ c * a) := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (2 * c) ha
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hpos))
  refine ⟨max (C * t₀ * t₀) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNC : C * t₀ * t₀ ≤ N := le_of_max_le_left hN
  set t := Nat.sqrt (N / C) with ht_def
  -- `t₀ ≤ t` since `C t₀² ≤ N`
  have ht0 : t₀ ≤ t := by
    rw [ht_def, Nat.le_sqrt, Nat.le_div_iff_mul_le hC]
    calc t₀ * t₀ * C = C * t₀ * t₀ := by ring
      _ ≤ N := hNC
  -- `N < (t + 1)² C`
  have hNlt : N < (t + 1) * (t + 1) * C :=
    (Nat.div_lt_iff_lt_mul hC).1 (Nat.lt_succ_sqrt (N / C))
  have hNltR : (N : ℝ) < ((t : ℝ) + 1) ^ 2 * C := by
    have := hNlt
    rw [← pow_two] at this
    exact_mod_cast this
  -- the limit at `t + 1`: `(t + 1)^{2c} C^c < a^t`
  have hlim := ht₀ (t + 1) (by omega)
  have hlim' : ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a) < a ^ (t + 1) := by
    have hapos : (0 : ℝ) < a ^ (t + 1) := pow_pos ha0 _
    rw [div_lt_iff₀ hapos] at hlim
    push_cast at hlim
    calc ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a)
        < 1 / ((C : ℝ) ^ c * a) * a ^ (t + 1) * ((C : ℝ) ^ c * a) := by
          gcongr
      _ = a ^ (t + 1) := by field_simp
  have hkey : ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c < a ^ t := by
    rw [pow_succ, ← mul_assoc] at hlim'
    exact lt_of_mul_lt_mul_right hlim' ha0.le
  -- `N^c ≤ (t + 1)^{2c} C^c`
  have hNpow : (N : ℝ) ^ c ≤ ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) hNltR.le c
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  show |a⁻¹ ^ t| < 1 / (N : ℝ) ^ c
  rw [abs_of_pos (pow_pos (inv_pos.mpr ha0) t), inv_pow, ← one_div]
  exact one_div_lt_one_div_of_lt hNpos (hNpow.trans_lt hkey)

/-- `2^{-√(N / C)}` is negligible in `N` (Inf-4.4, the graph-isomorphism bound). -/
theorem negligible_two_pow_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => (2 : ℝ)⁻¹ ^ Nat.sqrt (N / C) :=
  negligible_inv_pow_sqrt_div one_lt_two hC

/-- `e^{-√(N / C)}` is negligible in `N` (Inf-4.4, the 3-colouring bound). -/
theorem negligible_exp_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => Real.exp (-(Nat.sqrt (N / C) : ℝ)) := by
  have h1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine (negligible_inv_pow_sqrt_div h1 hC).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul, mul_one]

/-- A function bounded by `a^{-√(N / C)}` is negligible (Inf-4.4 in the form used by the
protocol theorems: a bound `a^{-n}` in the number of vertices `n ≥ √(|x| / C)` is a bound
`a^{-√(|x| / C)}` in the instance length). -/
theorem negligible_of_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C)
    {ν : ℕ → ℝ} (hν : ∀ N, |ν N| ≤ a⁻¹ ^ Nat.sqrt (N / C)) : Negligible ν :=
  (negligible_inv_pow_sqrt_div ha hC).mono ⟨0, fun N _ => by
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans ha.le)) _)]
    exact hν N⟩

/-- A bound `a^{-n}` in a parameter `n ≥ √(N / C)` transfers to `a^{-√(N / C)}`
(monotonicity of `a⁻¹ ^ ·` for `a > 1`). -/
theorem inv_pow_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C N n : ℕ}
    (hn : Nat.sqrt (N / C) ≤ n) : a⁻¹ ^ n ≤ a⁻¹ ^ Nat.sqrt (N / C) :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (zero_le_one.trans ha.le)) (inv_le_one_of_one_le₀ ha.le) hn

end TCSlib.Cryptography
