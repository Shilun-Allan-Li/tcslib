# Fill `bb1-sim` (T2, T3): design round 1, a relational simulation lemma in `Games`

This is a design note for the statement phase of fill unit `bb1-sim`, which covers T2 `bb1_sim_real`
and T3 `bb1_sim_random`. It was prepared read-only: no Lean was run, and nothing was committed. Every
Lean line number refers to the pins below and was read with `git show <pin>:<path>`.

| Pin | Value |
|---|---|
| #331 head (statements; Gate 40 closed) | `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| T4 branch `fill/pairings-bb1-machine` (T4 still `sorry`; the 7 readers are not in it yet) | `7c0a55e0239c14786612d0cd4462e64238543ca1` |
| Records commit with the ruling (decision log, 2026-11-16, "Rulings (Seyoon) … (2) T2/T3 design") | `bf08dbfa3a057a3b41d20f6dbede3066bc5e6660` |
| Records tip when this note was written (`TCSlib/Cryptography/Games/` is identical to #331's) | `a0e3148309dbc3bf836d46745b707724599541f0` |
| Gate 40 note | `briefs/pairings/gates/40-pairings-statements/findings/gate40-pairings-statements-findings.md`, § "Truth and sufficiency", the T2 paragraph |

**The ruling (Seyoon, 2026-11-16).** A public relational simulation lemma goes into `Games`. It
relates two handlers whose state types `σ` and `τ` are linked by an invariant `R : σ → τ → Prop`.
Each oracle call keeps the invariant, and the answers have equal laws. The lemma is statement-gated
together with the `bb1-sim` fill, and it is preferred to a combined state kept local to the fill.

**Summary of the proposal.**
* A new module, `TCSlib/Cryptography/Games/Relational.lean`, with three statements:
  * `ProbComp.expect_simulate_rel` (the target);
  * `ProbComp.prob_simulate_rel` (the event and acceptance corollary);
  * `ProbComp.expect_sample_rel` (discharges one call that samples once, coupled by a bijection).
* T2 uses `expect_simulate_rel` twice, together with the existing `Games.expect_simulate_eager`
  twice. T3 needs only the existing single-state `ProbComp.expect_simulate_congr`, after one
  eager/lazy step.
* The main practical risk is not the lemma. It is the set of readers that T2 needs in the frozen
  `Defs.lean` and `BonehBoyen.lean` (§3.3, §5). A probe should settle that set before the statement
  PR.

---

## 1. The `Games` API this builds on (at `9e7a9648`)

All paths below are relative to `TCSlib/Cryptography/`.

### 1.1 Types

| Name (full namespace `TCSlib.Cryptography.Games`) | What it is | File:line |
|---|---|---|
| `OracleSpec ι` | structure with fields `dom rng : ι → Type` | `Games/OracleComp.lean:74` |
| `OracleComp spec α` | inductive type: `pure : α → _`, `query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)` | `Games/OracleComp.lean:84` |
| `OracleComp.AllOutputs P c` | every possible output satisfies `P` | `Games/OracleComp.lean:292` |
| `unifSpec : OracleSpec ℕ` | `abbrev`, `⟨fun _ => Unit, fun m => Fin (m + 1)⟩` | `Games/Probability.lean:73` |
| `ProbComp` | `abbrev ProbComp := OracleComp unifSpec` | `Games/Probability.lean:77` |
| `ProbComp.sample T` | uniform element of a nonempty finite type | `Games/Probability.lean:92` |
| `ProbComp.expect : ProbComp α → (α → ℝ) → ℝ` | expectation | `Games/Probability.lean:106` |
| `ProbComp.prob c p` | `expect` of the indicator | `Games/Probability.lean:112` |
| `QueryImpl spec σ spec'` | `abbrev`, `∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)`. Notation under R-04-4. | `Games/Simulate.lean:73` |
| `simulate (impl : QueryImpl spec σ spec') : OracleComp spec α → σ → OracleComp spec' (α × σ)` | defined by recursion: `pure a, s ↦ pure (a, s)`; `query i x k, s ↦ (impl i x s).bind fun ys => simulate impl (k ys.1) ys.2` | `Games/Simulate.lean:83` |
| `accept G := prob G (· = true)`, `advantage G₀ G₁ := abs (accept G₀ - accept G₁)` | acceptance probability and advantage of games | `Games/Advantage.lean:63`, `:72` |
| `bitSpec din dout` | `abbrev`, `⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩` | `Games/BitCodec.lean:73` |
| `NUPPT.toComp D codec n q r : OracleComp spec α` | the machine as an oracle computation | `Games/Machines.lean:221` |

**Note on names.**
* For games there is no `acceptProb`: the acceptance probability is `Games.accept`.
* `acceptProb` exists only in the concrete layer (`Foundations/Experiments.lean:72`). The bridge
  between the two is `Games.Bridge.acceptProb_eq` (`Games/Bridges/Experiments.lean:120`).
* T2's frozen sketch cites `Games.expect_simulate_congr`. The lemma's actual name is
  `Games.ProbComp.expect_simulate_congr`.

### 1.2 The two lemmas the ruling is about, verbatim

`Games/Hopping.lean:384–393`, namespace `TCSlib.Cryptography.Games.ProbComp`:

```lean
theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G
```

Here both implementations have the single state type `σ`, and both runs start from the same `s`.
This is the restriction that Gate 40 flagged.

`Games/Hopping.lean:494–503`, namespace `TCSlib.Cryptography.Games`; both T2 and T3 use it:

```lean
theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (hfresh : ∀ i x s, ¬ used s →
      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
    ProbComp.expect (simulate O c s) G =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G
```

This lemma also has one state type. It moves a one-shot sample between "drawn in advance" and
"drawn at the call that spends it".

### 1.3 Every `simulate_*` and `expect_simulate_*` lemma in `Games/`

| Lemma | Content | File:line |
|---|---|---|
| `simulate_pure`, `simulate_query` (`@[simp]`) | the two defining equations | `Games/Simulate.lean:93`, `:97` |
| `simulate_bind`, `simulate_call` | sequencing; a single call | `Games/Simulate.lean:107`, `:114` |
| `simulate_comp` | composing implementations (state `σ₁ × σ₂`) | `Games/Simulate.lean:199` |
| `simulate_withLog` | logging is conservative | `Games/Simulate.lean:241` |
| `simulate_costBoundedBy`, `simulate_costBoundedBy_once` | query cost under simulation | `Games/Simulate.lean:264`, `:290` |
| `simulate_eq_of_abs` | **two state types**, `f : σ₂ → σ₁`, exact equality of computations, every state | `Games/Simulate.lean:334` |
| `simulate_eq_of_abs_bounded` | the same, deterministic calls, with a query budget `cnt` | `Games/Simulate.lean:357` |
| `simulate_allOutputs_bad` | a sticky bad flag stays raised | `Games/Hopping.lean:179` |
| `expect_eq_until_bad`, `prob_eq_until_bad`, `identical_until_bad`, `identical_until_bad_init`, `hagree_of_eq` | the fundamental lemma; one state type | `Games/Hopping.lean:201`, `:252`, `:306`, `:343`, `:331` |
| `ProbComp.expect_simulate_congr` | equal laws per call; one state type | `Games/Hopping.lean:384` |
| `ProbComp.prob_bad_le` | per-query potential bound | `Games/Hopping.lean:403` |
| `simulate_eq_of_used` (private) | helper for the eager lemma | `Games/Hopping.lean:469` |
| `expect_simulate_eager` | one-shot coins in advance; one state type | `Games/Hopping.lean:494` |
| `simulate_castImpl_toCompOn`, `expect_simulate_castImpl_toCompOn` | transport along equal length functions | `Games/BitCodec.lean:415`, `:430` |
| `simulate_ofComp_pure`, `Bridge.simulate_eq` | query trees | `Games/Bridges/QueryTree.lean:83`, `:124` |

Supporting expectation lemmas:

| Lemma | File:line |
|---|---|
| `expect_pure` | `Games/Probability.lean:116` |
| `expect_bind` | `:127` |
| `expect_sample` | `:146` |
| `expect_const` | `:173` |
| `expect_mono` | `:192` |
| `prob_eq_expect` | `:207` |
| `prob_bind` | `:223` |
| `expect_sample_equiv` | `:303` |
| `expect_sample_comm` | `:312` |
| `expect_expect_sample` | `:325` |
| `expect_sub` | `:339` |
| `abs_expect_sub_le` | `:392` |
| `expect_congr_of_allOutputs` | `Games/Hopping.lean:101` |
| `Bridge.prob_sample_eq_uprob` | `Games/Bridges/Experiments.lean:65` |
| `Bridge.expect_sample_pair` | `Games/Bridges/Experiments.lean:72` |

### 1.4 The handler types of the IBE game and of the simulator

All lines below are in `AdvancedEncryption/IdentityBased/`.

| Object | Type or definition | File:line |
|---|---|---|
| `IBEScheme.sidSpec κ` | `abbrev := bitSpec (S.inLens κ) (S.outLens κ)`. `inLens` and `outLens` are defs (`:201`, `:217`), sealed for consumers. | `Defs.lean:232` |
| `IBEScheme.SidState κ` | `abbrev := Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)` | `Defs.lean:240` |
| **real handler** `S.sidImpl b κ pp msk` | `QueryImpl (S.sidSpec κ) (S.SidState κ) unifSpec` | `Defs.lean:258–281` |
| its readers | `sidImpl_init_none`/`_some`, `_keyGen_none`/`_target`/`_ne`, `_challenge_none`/`_repeat`/`_fresh`/`_invalid`, all stated with **typed** queries `Fin (S.idLen.eval κ) → Bool` | `Defs.lean:284–346` |
| `S.oracleImpl κ init key chal` | `QueryImpl (S.sidSpec κ) σ unifSpec` built from typed handlers; readers `oracleImpl_zero`/`_one`/`_two` (typed) | `Defs.lean:352`, `:363`, `:372`, `:381` |
| `S.sidGame A q b κ` | `(S.setup κ).bind fun k => (sample (A.Coins κ)).bind fun r => (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind fun res => .pure (res.1 0)` | `Defs.lean:399` (`sidGame_eq` `:407`) |
| `BB1SimState G ℓ κ d` | `abbrev := Option ((Fin ℓ(κ) → Bool) × ZMod (G.group κ d).order) × Option (Fin ctLen(κ) → Bool)` | `BonehBoyen.lean:429` |
| **simulator** `bb1SimImpl G ℓ b κ d g X Y Z T` | `QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec := (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit …) (bb1SimKeyQ …) (bb1SimChal …)` | `BonehBoyen.lean:627–631` (`_eq` `:634`) |
| simulator readers | `bb1SimInit_none`/`_some` (`:487`, `:496`), `bb1SimKeyQ_none`/`_target`/`_ne` (`:517`–`:530`), `bb1SimChal_none`/`_repeat`/`_fresh`/`_invalid` (`:578`–`:611`), `bb1SimParams_eq` (`:448`), `bb1SimKey_eq` (`:466`), `bb1SimCt_eq` (`:548`) | `BonehBoyen.lean` |
| `bb1SimGame G ℓ A q b real κ` | draws `r`, `g ∈ G^*`, `(a, b', c)`, `T`, `ρ`; simulates `bb1SimImpl` from `(none, none)` | `BonehBoyen.lean:645` (`_eq` `:660`) |
| T2 `bb1_sim_real` | `advantage (sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤ uprob (fun r => (G.inst κ r).order < 2 ^ ℓ.eval κ)` | `BonehBoyenSecurity.lean:89–92` (sketch `:73–88`) |
| T3 `bb1_sim_random` | `advantage (bb1SimGame … false false κ) (bb1SimGame … true false κ) = 0` | `BonehBoyenSecurity.lean:104–106` (sketch `:94–103`) |

The two state types in T2 differ in their first component:
* the real game's is `Option ID`;
* the simulator's is `Option (ID × Z_p)`.

Within one run, the stored `α₁` is related to the real game's `h` only through `ID*`. The relation
`h = g_1^{−ID*} g^{α₁}` is exactly the invariant `R`.

---

## 2. The proposed statements

### 2.1 Placement: a new file `Games/Relational.lean`

**Recommended: a new child module `TCSlib/Cryptography/Games/Relational.lean`**, about 150–190
lines, namespace `TCSlib.Cryptography.Games`, imported by the `Games.lean` facade. Reasons:

* **Modularity.** The new file is one coherent cluster: comparing simulations on related states.
  Its only imports are `Games.Simulate` and `Games.Probability`; it needs nothing from `Hopping`.
* **Verification cost and ownership.** `Games/Hopping.lean` (524 lines) is imported directly by 7
  modules and transitively by most of `Cryptography/`. Appending to it would rebuild and re-seal
  that whole closure, and would put a shared file into the fill's diff. The facade `Games.lean` is
  imported only by `TCSlib.lean`. A new module therefore costs only itself, the facade and the
  root, and it is a file that only `bb1-sim` owns.
* **Size.** Appending would also be acceptable for size (Hopping would reach about 640 lines, under
  the 1000-line cap). This is not the reason to prefer the new file; the two reasons above are.
* **Exports.** The facade change is one `import` line and one `## Contents` entry
  (`Games.lean:5–11`, `:32–48`). `TCSlib.lean` already imports the facade (line 65), so the root
  does not change.
* **Placement elsewhere.** `Games` has no `Basic.lean`, and this is a framework lemma, not a
  pairing helper. Placing it in the pairing area would make it a private host, which the ruling
  rules out.

`Hopping.lean` is left byte-identical. In particular, its docstring gets no cross-reference, because
any change there rebuilds its whole downstream closure. The new file points back to
`ProbComp.expect_simulate_congr` and `simulate_eq_of_abs` instead.

### 2.2 Statement-phase text of the new module

The first two lemmas have `sorry` bodies at the statement phase. The third (L2) is proved from the
first (L1) at that point, by the proved-modulo rule, as `bb1_sidSecure` is proved from T2–T4. Every
line is at most 100 characters. There is no `@[simp]` and no new definition, so no reader is owed.

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulations on related states

Two implementations of the same oracles may keep states of different types: in a security proof
the real game and its simulation often record different data for the same history (for BB1, the
committed identity with a group element `h`, or with an exponent `α_1`). If a relation `R`
between the two kinds of state holds at the start, and every call from related states answers
alike and leads to related states, then the two simulations of any computation answer alike and
end in related states (`ProbComp.expect_simulate_rel`). "Alike" is measured by expectations: a
call, or a run, from related states gives the same expectation to any two functions of the
answer and the state that agree at equal answers and related states.

With one state type and `R` the equality this is `ProbComp.expect_simulate_congr`
(`Games.Hopping`); with `R s t ↔ s = f t` it is the law form of `simulate_eq_of_abs`
(`Games.Simulate`), without a query budget.

## Main definitions

None.

## Main results

* `ProbComp.expect_simulate_rel`: implementations on related states simulate alike.
* `ProbComp.prob_simulate_rel`: events on the output have the same probability, so games that
  return a bit computed from the output have the same acceptance probability.
* `ProbComp.expect_sample_rel`: a call that draws one uniform sample meets the hypothesis of
  `expect_simulate_rel` when a bijection of the samples matches the answers and relates the new
  states.

## References

* [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal certification of code-based
  cryptographic proofs*, POPL 2009 (the probabilistic relational Hoare logic and its rule for
  adversary calls with oracles that keep a relational invariant). ⟨location to pin, Q11⟩
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332, revision of 18 January 2006 (bridging steps). ⟨location to pin, Q11⟩
-/

namespace TCSlib.Cryptography.Games

namespace ProbComp

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **Implementations on related states simulate alike.** Let `impl₀` keep states in `σ` and
`impl₁` in `τ`, related by `R : σ → τ → Prop`. Suppose that every call from related states
`R s t` gives the same expectation to any function `g₀` of the answer and the new `σ`-state and
any function `g₁` of the answer and the new `τ`-state that agree at equal answers and related
states:
`(∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) → 𝔼[g₀] (impl₀ i x s) = 𝔼[g₁] (impl₁ i x t)`.
Then from related states the simulations of every computation `c` do the same for functions of
the output and the final state: if `R s t`, and `G₀ (a, s') = G₁ (a, t')` whenever `R s' t'`,
then `𝔼[G₀] (simulate impl₀ c s) = 𝔼[G₁] (simulate impl₁ c t)`.
[BGZ09, ⟨rule for adversary calls⟩] [Sho04, ⟨bridging steps⟩]

**Deviation:** [BGZ09] asks for a coupling of the two calls whose support relates their results;
here the hypothesis is its expectation form (equal expectations for every pair of test functions
that agree along the relation), which such a coupling implies and which is all the induction
uses.

**Proof sketch.** Induction on `c`, generalizing the two states. At a return `a`, `R s t` gives
`G₀ (a, s) = G₁ (a, t)`. At a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`); by the induction hypothesis the two
continuation values agree at equal answers and related new states, so the hypothesis on the call
equates them. -/
theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
    (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
    expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
  sorry

/-- **Events on the output, from related states:** under the hypothesis of
`expect_simulate_rel`, from related states `R s t` every event `P` on the output of `c` has the
same probability under the two simulations:
`Pr[P (simulate impl₀ c s).1] = Pr[P (simulate impl₁ c t).1]`. For a game that returns a bit
computed from the output this equates the acceptance probabilities (`accept_eq`). -/
theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (P : α → Prop) {s : σ} {t : τ} (hst : R s t) :
    prob (simulate impl₀ c s) (fun p => P p.1) = prob (simulate impl₁ c t) (fun p => P p.1) := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_simulate_rel impl₀ impl₁ R h c _ _ (fun _ _ _ _ => rfl) hst

/-- **A sampling call, coupled by a bijection:** let `c₀` draw `u ∈ U` and return `f₀ u`, and
`c₁` draw `v ∈ V` and return `f₁ v`. If a bijection `e : U ≃ V` gives equal answers and related
states, `(f₀ u).1 = (f₁ (e u)).1` and `R (f₀ u).2 (f₁ (e u)).2`, then `c₀` and `c₁` give the same
expectation to any `g₀`, `g₁` that agree at equal answers and related states,
`𝔼[g₀] c₀ = 𝔼[g₁] c₁`: the hypothesis of `expect_simulate_rel` for such a call.

**Proof sketch.** Both sides are uniform averages (`expect_bind`, `expect_pure`); reindex the
average over `V` along `e` (`expect_sample_equiv`) and compare the two averages pointwise. -/
theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
    (R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)
    (hf : ∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ R (f₀ u).2 (f₁ (e u)).2)
    (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
  sorry

end ProbComp

end TCSlib.Cryptography.Games
```

**Changes to the facade `Games.lean`.**
* Import: `import TCSlib.Cryptography.Games.Relational`, after `…Games.Hopping` (line 9).
* `## Contents` entry: "`TCSlib.Cryptography.Games.Relational`: simulations of two implementations
  on related states (the relational form of simulation congruence)."

**How the hypothesis expresses the ruling's wording.** The ruling asks for "an invariant `R`
preserved by each oracle call, with equal answer laws". The single hypothesis `h` contains both
parts:
* **Equal answer laws.** Take `g₀`, `g₁` to be the same function of the answer only; `h` then says
  the two answers have the same law.
* **Preservation of `R`.** The test functions need to agree only at *related* successor states. If
  a call could reach a successor that is unrelated to the other side's successors, a pair of test
  functions would separate the two calls.

Packaging both parts as one expectation condition is what makes the induction a direct copy of
`expect_simulate_congr`'s. It is also the form in which the conclusion comes out, so the lemma
composes. Requiring an explicit coupling instead would add a new kind of object to `Games`
(Q3 in §5).

### 2.3 How the proofs would go, and which existing lemmas they use

* **L1 `expect_simulate_rel`.** The proof has the same shape as `ProbComp.expect_simulate_congr`
  (`Hopping.lean:384–393`): induction on `OracleComp` (`OracleComp.lean:84`), generalizing `s`, `t`
  and `hst`. It uses:
  * `simulate_pure` and `simulate_query` (`Simulate.lean:93`, `:97`);
  * `expect_pure` and `expect_bind` (`Probability.lean:116`, `:127`).

  An unchecked outline:
  ```lean
    induction c generalizing s t with
    | pure a =>
      rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
      exact hG a s t hst
    | query i x k ih =>
      rw [simulate_query, simulate_query, expect_bind, expect_bind]
      exact h i x s t hst _ _ fun y s' t' hR => ih y hR
  ```
* **L2 `prob_simulate_rel`.** Proved from L1 with `prob_eq_expect` (`Probability.lean:207`). It is
  proved at the statement phase.
* **L3 `expect_sample_rel`.** Uses `expect_bind`, `expect_pure` and `expect_sample_equiv`
  (`Probability.lean:303`); about 10 lines.
* **Rule 10.** Every foreign definition is read through its published lemmas: `simulate` through
  `simulate_pure`/`simulate_query`, `expect` through `expect_pure`/`expect_bind`, `prob` through
  `prob_eq_expect`, and `sample` through `expect_sample_equiv`. `QueryImpl` is an `abbrev`, which
  counts as notation. Nothing is unfolded, so the canonical seal of the new owner should pass
  unchanged.

### 2.4 Why it is not a duplicate

**How the search was done.** I searched `TCSlib/` at `9e7a9648` in four ways:
1. A script scanned every `theorem` or `lemma` statement mentioning `simulate` at least twice, or
   `simulate` together with two `QueryImpl`s. 49 hits; each was classified from its statement, and
   the relevant ones were read in full.
2. `git grep` for the terms "coupl", "bisim", `σ → τ → Prop`, `σ₁`/`σ₂`/`τ` beside
   `simulate`/`QueryImpl`, "pRHL", "Barthe" and "bridging".
3. The same grep for `expect_simulate_rel`, `simulate_rel`, `σ → τ → Prop` and "bisim" on **every
   local and remote branch** (including `fill/pairings-bb1-machine`, `fill/pairings-pair-bdh` and
   `stmt/*`). This found nothing.
4. The T4 helper modules on `7c0a55e0`.

**Result.**
* No public or private lemma relates two simulations by a relation between different state types.
* The new lemma generalizes three existing lemmas without restating any of them:
  * `expect_simulate_congr`, the case where `R` is equality;
  * the law form of `simulate_eq_of_abs`, the case `R s t ↔ s = f t`;
  * the unbudgeted cases of the ETT forms, the case `R s t ↔ P t ∧ s = f t`.
* L3 is new. No lemma states a bijective coupling of one sample as a relational step; the existing
  uses inline `expect_sample_equiv`.

**Near-relatives, and why each is not the same statement.**

| Lemma | File:line | Relation to the proposal |
|---|---|---|
| `Games.ProbComp.expect_simulate_congr` | `Games/Hopping.lean:384` | One state type, the same start state. The `R = Eq` special case. |
| `Games.simulate_eq_of_abs` | `Games/Simulate.lean:334` | Two state types, but a function `f : σ₂ → σ₁` and **exact equality of computations** for **every** state. It cannot express re-randomization (T2's `h ↔ α₁`, `r̃ ↔ r`) or an invariant (Gate 40: "structural state abstraction, but not arbitrary distributional re-randomization"). |
| `Games.simulate_eq_of_abs_bounded` | `Games/Simulate.lean:357` | As above, with deterministic calls and a budget. |
| `Composability.ETTGame.expect_simulate_abs`, `expect_simulate_abs_inv` | `Encryption/PrivateKey/EncryptThenTag/Tools.lean:65`, `:88` | **Closest relatives.** Law form with a function abstraction `f`, an invariant `P` on one side, and a **query budget** (`cnt`, `κ`, `CostBoundedBy`). A function cannot relate T2's states, where `h` and `α₁` are linked through `ID*`. In the ETT layer (the file's docstring: "candidates for promotion to the `Games` layer"), and recorded in **DL-40** as a deferred promotion (`duplication-ledger.md:67`). The new lemma is the unbudgeted relational generalization; the budgeted ETT lemmas are not instances of it (Q5). |
| `Games.expect_eq_until_bad`, `prob_eq_until_bad`, `identical_until_bad(_init)` | `Games/Hopping.lean:201`, `:252`, `:306`, `:343` | One state type; equality up to a bad flag. |
| `Games.expect_simulate_eager` | `Games/Hopping.lean:494` | One state type; moves one-shot coins. Used *beside* the new lemma (§3). |
| `Composability.ChallengeSim.expect_simulate_eager` | `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean:148` | The same name in another namespace; a CPA-shaped eager step with one state type. |
| `NMSim.expect_simulate_rImpl_eager` | `Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean:267` | An application of `Games.expect_simulate_eager`. |
| `ETTGame.simulate_tapeImpl_congr`, `expect_simulate_tapeImpl`, `freshImpl`, `tapeImpl` | `…/EncryptThenTag/Tools.lean:145`, `:167`, `:116`, `:130` | Tapes against fresh coins; state `σ` against `σ × ℕ`, fixed by construction, with a budget. |
| `AdaptiveCPA.simulate_tapeImpl_congr`, `expect_tapeImpl` | `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:170`, `:244` | Specific tape hybrids. |
| `PRFGame.expect_lazyImpl` | `Encryption/PrivateKey/OracleFromPRF/Lazy.lean:351` | Lazy against eager random function; two state shapes, proved by its own induction for one pair of handlers. A specific bisimulation; the new lemma would be the generic tool for such proofs. |
| `ETTGame.expect_ettImpl_lazy`, `expect_ettLazyTape` | `Encryption/PrivateKey/EncryptThenTag/Lazy.lean:499`, `:461` | The same, for ETT. |
| `PRFGame.simulate_eImpl_congr` | `Encryption/PrivateKey/OracleFromPRF/Games.lean:199` | Congruence for one family of handlers. |
| `HashSignFill.expect_simulate_sample_once` | `Authentication/Signatures/HashAndSign/OneQuerySampling.lean:47` | One-query sampling law. |
| `LamportFill.planted_coupling` | `Authentication/Signatures/Lamport/Planted.lean:403` | A deterministic "coupling" for one specific aborting handler (at most one query). |
| `NMSim.expect_runB_good` (private) | `Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:702` | A coupling through `expect_eq_until_bad`. |
| `BB1Machine.exists_simulate_tape_eq_pure`, `expect_castImpl_freshImpl` (T4 branch) | `…/BonehBoyenMachine/Draws.lean:399`, `…/Reduction.lean:203` at `7c0a55e0` | Specific to T4's tape handler. |

**Note.** Several of these specific bisimulations (`expect_lazyImpl`, `expect_ettImpl_lazy`) could
later be re-proved from `expect_simulate_rel`. That is a candidate refactor for the DL-40 clean-up,
not part of this unit.

---

## 3. How T2 and T3 use it

The fill-local names below (`bb1RealAt`, `bb1RealLazy`, `bb1SimLazy`, `BB1RealState`) are
illustrative. Let `S := bb1Scheme G ℓ` and `c := A.toComp (S.sidCodec κ) κ q ρ`; this is the same
computation in both games. Fix the generator coins `r`, and write `d = G.desc κ r` and
`B = G.group κ d`. A coin set is *good* when `2^ℓ ≤ p`.

### 3.1 T2 `bb1_sim_real`

**Chain.** All quantities below are acceptance probabilities conditioned on `r`. Steps (1)–(4) and
(6)–(7) hold for every `r`; only step (5) uses good coins.

| Step | Equation | How it is justified |
|---|---|---|
| (1) | `Pr[sidGame_b | r] = 𝔼_{g,α,g₂,ρ} 𝔼_h Pr[simulate (S.sidImpl b κ pp_h msk_h) c ∅]` | Move the setup sample `h` inside, past `g₂` and `ρ` (`expect_sample_comm`, `expect_expect_sample`). |
| (2) | `= 𝔼_{g,α,g₂,ρ} 𝔼_h Pr[simulate (bb1RealAt h) c ∅]` | **`expect_simulate_rel` with `R_h`** (step R1 below). |
| (3) | `= 𝔼_{g,α,g₂,ρ} Pr[simulate bb1RealLazy c ∅]` | **`Games.expect_simulate_eager`** (step E-h below). |
| (4) | `= 𝔼_{g,α,b',ρ} Pr[… with g₂ := g^{b'}]` | `expect_sample_equiv` with the bijection `Z_p ≃ G`, `b' ↦ g^{b'}` (`g ≠ 1`). |
| (5) | `= 𝔼_{g,α,b',ρ} Pr[simulate bb1SimLazy c ∅]` | **`expect_simulate_rel` with `R`** (step M below); needs good coins. |
| (6) | `= 𝔼_{g,α,b',ρ} 𝔼_c Pr[simulate (bb1SimImpl b κ d g X Y g^c e(g,g)^{αb'c}) c ∅]` | **`Games.expect_simulate_eager`** (step E-c below). |
| (7) | `= Pr[bb1SimGame_{b,true} | r]` | Reorder; merge `(a, b', c)` (`Bridge.expect_sample_pair`); with `real = true` the sample `T` is unused (`expect_const`). |
| Bad coins | `abs (accept₀ − accept₁) ≤ 𝔼_r 1[p < 2^ℓ] = uprob (…)` | Pointwise bound `abs (F₀ r − F₁ r) ≤ 1[bad r]`, then `Bridge.prob_sample_eq_uprob` and `BilinearGen.inst_eq` (`Pairing/Group.lean:282`). |

**Handlers and invariants.** Throughout, `X = g^α` and `Y = g₂ = g^{b'}`.

* **Step R1** (equation (2)): from the real handler to a handler that stores `h`.
  * `impl₀ := S.sidImpl b κ pp_h msk_h` on `S.SidState κ`, where
    `pp_h = ⟨d, (g, X, Y, h)⟩` and `msk_h = ⟨d, ((g, X, Y, h), Y^α)⟩`. This is the shape of
    `bb1Scheme`'s setup output, `(⟨d, k.1⟩, ⟨d, k⟩)`.
  * `impl₁ := bb1RealAt h` on
    `BB1RealState := Option ((Fin ℓ(κ) → Bool) × B.G) × Option (Fin ctLen(κ) → Bool)`. On a
    committed state it runs `sidImpl`'s call with the *stored* `h`. On the first `Init` it stores
    `(ID*, h)`.
  * `R_h s u :↔ s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`.
  * Start: `R_h (none, none) (none, none)`.
  * Per-call obligations: from related states the two calls are the same computation, with the
    state mapped. The deterministic cases need `expect_pure`. The sampling cases (`KeyGen` for
    `ID ≠ ID*`, a fresh `Challenge`) need L3 with `e := Equiv.refl`.
* **Step E-h** (equation (3)): `Games.expect_simulate_eager` with `O := bb1RealLazy` (draws
  `h ← G` at the first `Init`), `OE h := bb1RealAt h`, and `used u := u.1.isSome`.
  * From a committed state, `bb1RealAt h = bb1RealLazy`.
  * `KeyGen` and `Challenge` before `Init` answer `⊥` and leave the state uncommitted.
  * `Init` from an uncommitted state is the spending call.
* **Step M** (equation (5)): the main relation. **This is the coupling in T2's sketch.**
  * `impl₀ := bb1RealLazy`.
  * `impl₁ := bb1SimLazy b κ d g X Y (zt := fun c => (g^c, e(g, g)^{(α b' c)}))`: the simulator
    with the challenge coin `c` drawn at the first valid challenge.
  * `R u v :↔ u.2 = v.2 ∧ Option.Rel (fun (t, h) (t', α₁) => t = t' ∧
    h = X ^ (−idToZ t).val * g ^ α₁.val) u.1 v.1`, i.e., the same recorded challenge, and
    `h = g₁^{−ID*} g^{α₁}`.
  * Start: `R (none, none) (none, none)`.
* **Step E-c** (equation (6)): `Games.expect_simulate_eager` with `O := bb1SimLazy …` and
  `OE c := bb1SimImpl b κ d g X Y (g^c) (e(g,g)^{αb'c})`, both on `BB1SimState`, and
  `used v := v.2.isSome`. `Z` and `T` enter only the fresh valid challenge
  (`bb1SimChal_fresh`), so the coins are one-shot.

**Per-call obligations of step M.** In every case the precondition is `R u v`. The left column is
`bb1RealLazy`, read through `sidImpl`'s readers. The right column is `bb1SimLazy`, read through
`oracleImpl_*_onSpec` and the `bb1Sim*` readers.

| Call | Real (`impl₀`) | Simulator (`impl₁`) | Why the hypothesis of L1 holds |
|---|---|---|---|
| `Init`, uncommitted | Draw `h ← G`. Answer `encPP ⟨d,(g,X,Y,h)⟩`. Store `(ID, h)`. | `bb1SimInit_none`: draw `α₁ ← Z_p`. Answer `encPP ⟨d, bb1SimParams g X Y ID α₁⟩`. Store `(ID, α₁)`. | **L3** with `e : G ≃ Z_p`, the inverse of `α₁ ↦ X^{(−ID)} g^{α₁}` (a bijection for each `ID`, because `g ≠ 1`). `bb1SimParams_eq` makes the parameters equal, so the answers are equal (compared through `ofFn_bb1Scheme_encPP`). The new states are in `R`. |
| `Init`, committed | Answer the stored parameters. | `bb1SimInit_some`. | Deterministic. `R` gives `h = X^{−t} g^{α₁}`. |
| `KeyGen` before `Init`, or for `ID*` | `⊥` (`sidImpl_keyGen_none`, `_target`) | `bb1SimKeyQ_none`, `_target` | Deterministic; states unchanged. |
| `KeyGen` for `ID ≠ ID*` | Draw `r̃`. Answer `⟨1, encSK ⟨d,(Y^α F(ID)^{r̃}, g^{r̃})⟩⟩` (`sidImpl_keyGen_ne`, `bb1Scheme_keyGen`, `BB1.keyGen_eq`). | `bb1SimKeyQ_ne`: draw `r`. Answer `⟨1, encSK ⟨d, bb1SimKey g X Y t α₁ ID r⟩⟩`. | **L3** with `r̃ ↦ r̃ + b'/(ID − ID*)` (`Equiv.addRight`). Good coins make `ID − ID* ≠ 0` in `Z_p` (`bitsToNat_lt`, `bitsToNat_injective`, `Asymptotic/Sampling.lean:412`, `:417`). The keys are equal by BB04's computation, with `F(ID) = g^{α(ID−ID*)+α₁}` (`bb1SimKey_eq`, `BB1.F_eq`, `pow_val_mul` and exponent laws). States unchanged. |
| `Challenge` before `Init` | `⊥` | `bb1SimChal_none` | Deterministic. |
| `Challenge`, repeated | the recorded ciphertext | `bb1SimChal_repeat` | `u.2 = v.2`. |
| `Challenge`, first, invalid | `⊥` (`sidImpl_challenge_invalid`) | `bb1SimChal_invalid` | Both message spaces depend only on `d` (`bb1Scheme_msgSpace_iff`). |
| `Challenge`, first, valid | Draw `s`. Answer and record `encCT ⟨d, (e(X,Y)^s · M_b, g^s, F(ID*)^s)⟩` (`sidImpl_challenge_fresh`, `bb1Scheme_enc`, `BB1.encrypt_eq`). | Draw `c`. Answer and record `bb1SimCt d (g^c) (e(g,g)^{αb'c}) α₁ M_b`. | **L3** with `e := Equiv.refl` (`s = c`). `F(ID*) = g^{α₁}`; `e(X,Y)^c = e(g,g)^{αb'c}` (`bilinear_pow`, `pow_val_mul_GT`); `G_T` is commutative. Answers compared through `ofFn_bb1SimCt` and an `encCT` reader (§3.3). |

**Mapping to T2's frozen sketch** (`BonehBoyenSecurity.lean:78–88`).

| Sketch sentence | Where it is in this design |
|---|---|
| "Fix coins with `2^ℓ ≤ p` …" | The good-coin case, used in `KeyGen` for `ID ≠ ID*`. |
| "Map `α ↦ a`, `g_2 ↦ g^{b'}` …" | Steps (4) and (5). |
| "… and `h ↦ g_1^{−ID*} g^{α_1}`" | Step M at `Init`. It is per call only after E-h moves `h` to `Init`: `h` is drawn before `ID*` exists. |
| "Answers to `Init` agree." | The two `Init` rows. |
| "the simulated key with exponent `r` is the real key with exponent `r̃` …" | The `KeyGen` row for `ID ≠ ID*`. |
| "The challenge is `Encrypt` with `s = c` …" | The valid-challenge row, after E-c moves `c` to the challenge. |
| "The state machines agree step by step (`simulate` with matched implementations, `Games.expect_simulate_congr`)" | **Becomes `ProbComp.expect_simulate_rel` with `R`**, plus the two eager steps. |
| "differ only on the excluded coins" | The bad-coin row of the chain. |

The sketch's route is sound, but two of its steps are implicit: the timing of `h` (drawn before
`ID*`) and of `c` (drawn before the challenge). The docstring-only sketch refresh at landing
(standing rule) should name `expect_simulate_rel` and the two `expect_simulate_eager` steps.

### 3.2 T3 `bb1_sim_random`

The relational lemma is **not needed** for T3. Both games use the same simulator shape and the same
state type `BB1SimState`, so `R` is equality and the existing `ProbComp.expect_simulate_congr`
applies. L3 is used with `R := Eq` at one call.

**Chain, for each `b`.**

| Step | Equation | How it is justified |
|---|---|---|
| (1) | `Pr[bb1SimGame_{b,false}] = 𝔼_{r,g,abc,ρ} 𝔼_T Pr[simulate (bb1SimImpl b κ d g X Y Z T) c ∅]` | Move `T` inside, past `ρ`. |
| (2) | `= 𝔼_{r,g,abc,ρ} Pr[simulate (bb1SimLazy b κ d g X Y (zt := fun T => (Z, T))) c ∅]` | **`Games.expect_simulate_eager`** (step E-T): `used v := v.2.isSome`, and `T` is spent at the first valid challenge. |

**Comparing the two bits.** Then `bb1SimLazy false …` and `bb1SimLazy true …` have the same law
call by call (`ProbComp.expect_simulate_congr`, `Hopping.lean:384`):
* `Init` and `KeyGen` are identical (the same `bb1SimInit` and `bb1SimKeyQ`).
* `Challenge` before `Init`, repeated, or invalid is identical: the validity test does not depend
  on `b`.
* At the first valid challenge, apply **L3 with `R := Eq`** and the bijection
  `T ↦ decodeT M₁⁻¹ · decodeT M₀ · T` of `G_T`. Then `M₀ · T = M₁ · e(T)`, so the answers are
  equal and both sides record the same ciphertext (compared through `ofFn_bb1SimCt`).

Hence the accepts are equal, and `advantage = 0` (`advantage_eq`).

**Relation to T3's sketch** (`BonehBoyenSecurity.lean:98–103`). The sketch says: "exchanging the
sample of `T` with the rest of the game (`expect_expect_sample`) and reindexing it by
`T ↦ M_b^{−1} M_{1−b} · T`".
* `expect_expect_sample` alone cannot move `T` past the adaptive history. The step that does it is
  E-T. Gate 40 made the same point: "an unconditional permutation chosen before seeing the adaptive
  history is not required".
* The reindexing is per call, at the challenge.

The sketch refresh at landing should name `expect_simulate_eager` and `expect_simulate_congr`.

### 3.3 What else the fill needs

1. **Readers in the frozen files.** This is the main dependency.
   * **From T4's PR** (approved; not yet on `7c0a55e0`):
     * `IBEScheme.oracleImpl_{zero,one,two}_onSpec` (`Defs.lean`), for reading `bb1SimImpl` at the
       game's query type; needed by T2 and T3;
     * `bb1Scheme_msgSpace_iff`, for T2's invalid-challenge case;
     * `ofFn_bb1SimCt`, for the challenge answers in T2 and T3;
     * `ofFn_bb1Scheme_encPP` and `ofFn_bb1Scheme_encSK`, for T2's `Init` and `KeyGen` answers.
   * **Probably new** (to be confirmed by a probe):
     * **a reader for `sidImpl` at the game's query type.** The nine `sidImpl_*` readers take typed
       queries `Fin (S.idLen.eval κ) → Bool`. Under the seals, `inLens` blocks unification with
       `(S.sidSpec κ).dom i`, which is the obstruction T4 hit for `oracleImpl`. Proposed:
       `IBEScheme.sidImpl_eq_oracleImpl : S.sidImpl b κ pp msk =
       S.oracleImpl κ (S.sidImpl b κ pp msk 0) (S.sidImpl b κ pp msk 1) (S.sidImpl b κ pp msk 2)`.
       It is one reader, proved by `funext` and a three-way `match` with `rfl`. Combined with
       T4's `_onSpec` readers it makes the typed `sidImpl_*` lemmas apply. The alternative is three
       `sidImpl_*_onSpec` readers in T4's form.
     * **an `ofFn` reader for `bb1Scheme`'s `encCT`** (`ofFn_bb1Scheme_encCT`), parallel to T4's
       `encPP` and `encSK` readers, for comparing the real challenge with `bb1SimCt`.
   * **Constructing values in a consumer file.** T4's report notes that anonymous constructors
     `⟨d, pp⟩ : (bb1Scheme G ℓ).PP κ` do not elaborate under the seals. The real-side handlers
     (`bb1RealAt`, `bb1RealLazy`) should therefore take the setup's output map as a parameter,
     instantiated from `bb1Scheme_setup` and `BB1.setup_eq` at the use site. They should not
     construct `PP` or `MSK` values themselves.
2. **Group helpers.** None of these is published:
   * `a ↦ g^{a.val}` is a bijection `Z_p ≃ G` for `g ≠ 1`. Only the `G_T` form
     `pow_val_bijective` exists (`Pairing/Group.lean:224`).
   * The additive and negation exponent laws `x^{(u+v).val} = x^{u.val} x^{v.val}` and
     `x^{(−u).val} = (x^{u.val})⁻¹`, next to `pow_val_mul` (`:192`).
   * Residue injectivity of `ℓ`-bit identities when `2^ℓ ≤ p`, from `bitsToNat_lt` and
     `bitsToNat_injective`.

   Each is a short proof from `exists_pow_eq`, `pow_order` and Mathlib's `orderOf` facts. Q10 asks
   where they go.
3. **Lazy handlers, with readers and eager lemmas.**
   * `bb1SimLazy` should be generic in the challenge coins (`zt : U → G × G_T`). One definition
     then serves T2's `c` (`U = Z_p`) and T3's `T` (`U = G_T`), with one eager lemma derived from
     `Games.expect_simulate_eager`.
   * `bb1RealAt` and `bb1RealLazy` serve T2's `h`.
   * They are public definitions in a helper module, so each lands with case readers (policy §1).
   * No new eager lemma is to be proved: DL-33 recorded an earlier near-copy of the eager lemma.
4. **Averaging a pointwise bound.** T2's last step needs `abs (𝔼 f − 𝔼 g) ≤ 𝔼 h` from
   `∀ x, abs (f x − g x) ≤ h x`. The only copy is the **private**
   `abs_expect_sub_le_expect` (`Encryption/PrivateKey/EncryptThenTag/Forgery.lean:515`), which
   DL-40 has queued for promotion. The fill must not add a second private copy (Q6).
5. **Plumbing that already exists.**
   * Game equations: `IBEScheme.sidGame_eq`, `bb1SimGame_eq`, the `bb1Scheme_*` `simps` equations,
     `BB1.setup_eq`.
   * Advantage: `accept_eq`, `advantage_eq`.
   * Expectations: `prob_bind`, `expect_bind`, `expect_sample_comm`, `expect_expect_sample`,
     `Bridge.expect_sample_pair`, `expect_const`, `expect_sample_equiv`,
     `Bridge.prob_sample_eq_uprob`.
   * Group: `BilinearGen.inst_eq`, `bilinear_pow`, `pow_val_mul(_GT)`.
   * The instance `nonempty_ne_one` (`Pairing/Group.lean:147`) for sampling `G^*`.
   * No query budget is needed anywhere.
6. **Layout.**
   * Helper modules under `IdentityBased/BonehBoyenSecurity/`, for example `Lazy.lean` (the lazy
     handlers and eager lemmas), `Real.lean` (R1 and E-h) and `Coupling.lean` (step M with the
     group helpers).
   * `BonehBoyenSecurity.lean` gains their imports and a `## Contents` section, following T4's
     precedent for `BonehBoyenMachine.lean`.
   * T2's and T3's headers and statement prose stay byte-identical.
   * At landing, the `**Proof sketch.**` paragraphs get a docstring-only refresh.
   * Size: the plan estimates T2 at 400–800 lines and T3 at 150–350. The lazy handlers and their
     readers move T2 toward the upper end.

---

## 4. Unit split and gating

### 4.1 Statement phase (Phase S)

**Contents of the change.**
* The new file `Games/Relational.lean` exactly as in §2.2:
  * `expect_simulate_rel` and `expect_sample_rel` are `sorry`'d, with sketches;
  * `prob_simulate_rel` is proved from `expect_simulate_rel` (proved-modulo).
* The `Games.lean` facade: one import and one `## Contents` entry.
* Nothing else. `Hopping.lean`, `TCSlib.lean` and every pairing file stay unchanged.

**Branch.** Phase S touches only `Games/`, which sits above the pairing closure and is disjoint
from #331, #340 and T4's branch. It can therefore be a small PR on the records tip. The precedent
is #210's shared statements S1–S3, which were added `sorry`'d and later filled by the units.

**Evidence, in the campaign's usual form.**
* A build of `Games.Relational`, `Games` and the root.
* An axiom census: `sorryAx` only in `expect_simulate_rel` and `expect_sample_rel`, and inherited by
  `prob_simulate_rel`.
* Canonical seals of the new owner (strict and coe, A and B), with paired controls and the
  explicit-unfold scan.
* Style lint; frozen check: no other file is changed.

**Before Phase S is filed, a probe (not committed).** This avoids T4's mid-fill stop. The probe
should:
* state T2's per-call obligations for step M and T3's challenge obligation;
* check them under the development seals, using T4's 7 readers and the proposed
  `sidImpl_eq_oracleImpl` and `ofFn_bb1Scheme_encCT`;
* put the exact reader set to Seyoon as a scope request before the fill is issued.

### 4.2 Fill (Phase F, unit `bb1-sim`)

**What the unit owns.**
* The proof bodies of `expect_simulate_rel` and `expect_sample_rel` in `Games/Relational.lean`.
  Their headers and statement prose are frozen at the Phase S commit.
* T2 and T3 in `IdentityBased/BonehBoyenSecurity.lean`, plus the new helper modules.
* The reader insertions that the scope ruling approves.

**Base.** The fill uses T4's readers, so it must be based on T4's PR after the readers land there,
or on the records tip once that PR has merged.

**End state.** `bb1_sidSecure` reaches standard axioms once both T4 and `bb1-sim` are in.

### 4.3 Gate coverage

* **Gate 44** audits T4's PR (`fill/pairings-bb1-machine`): the T4 fill, and the 7 readers checked
  as pure insertions. It does not cover `Games/Relational.lean` or T2/T3, and it should not be
  widened to them.
* **Recommended: one `bb1-sim` gate after Gate 44**, numbered with the next free number when it is
  staged. Having one gate for the statement and the fill matches the ruling. Its pack:
  1. pins the Phase S commit as the statement baseline;
  2. runs a frozen-header check: `expect_simulate_rel`, `prob_simulate_rel` and
     `expect_sample_rel` are byte-identical to Phase S apart from their `**Proof sketch.**`, and T2
     and T3 are byte-identical to #331;
  3. audits the three statements for generality, docstring fidelity, attribution, placement and
     non-duplication against the table in §2.4;
  4. checks the reader insertions as pure insertions, as Gate 44 does;
  5. audits the fill: seals for the new owners and for every owner whose closure changed, axioms,
     and the sketch refresh.
* **Alternative.** If Seyoon wants the `Games` statement fixed before the fill is issued, Phase S
  can be appended to Gate 44's pack as a separate item. The files are disjoint and the item is
  statement-only. The fill would then be audited at the later gate.
* **The file-disjointness caveat.** The premise that "T4's PR … owns disjoint files" holds for the
  owned files, but not for the reader insertions:
  * T4's PR inserts into `Defs.lean` and `BonehBoyen.lean`, and `bb1-sim` probably needs more
    insertions in the same two files.
  * To keep the diffs disjoint in time, sequence them: T4 merges first, then `bb1-sim`.
  * The `bb1-sim` readers go at different anchors: in `Defs.lean`, after T4's `_onSpec` block
    (`sidImpl_eq_oracleImpl` mentions `oracleImpl`, so it must follow `Defs.lean:352`); in
    `BonehBoyen.lean`, next to the `simps` attribute (`:386`).
  * Each of those owners' canonical seals is re-run in that gate.

---

## 5. Risks and open questions

### Risks

1. **The reader scope (high).**
   * T2 cannot read `sidImpl` at the game's query type with the published readers. This is the
     `inLens` obstruction from T4's report.
   * T2 probably also needs an `encCT` reader, and a way to avoid constructing
     `(bb1Scheme G ℓ).PP κ` values in a consumer file.
   * Without a probe first, the fill would stop mid-way as T4 did (§3.3, item 1; §4.1).
2. **Dependence on T4's PR (medium).** `bb1-sim` consumes `oracleImpl_*_onSpec`,
   `bb1Scheme_msgSpace_iff` and the `ofFn_*` readers, and both units insert into the same two
   frozen files. Q9 covers the ordering.
3. **Sketch drift (low; standard).**
   * T2's frozen sketch cites `Games.expect_simulate_congr` (the wrong namespace, and the wrong
     lemma, since the state types differ).
   * Both sketches leave the eager/lazy steps implicit (§3.1, §3.2).
   * The standing rule gives a docstring-only refresh at landing; the statements are never changed.
4. **Budget and DL-40 (low).**
   * `expect_simulate_rel` has no query budget, so the budgeted ETT `expect_simulate_abs(_inv)`
     are not instances of it.
   * If DL-40's promotion later wants them derived from the relational form, it needs a budgeted
     variant (Q5).
   * Today's ETT copies stay as recorded in DL-40. Nothing new is duplicated.
5. **Duplication traps for the fill (medium).**
   * A second private copy of `abs_expect_sub_le_expect` (Q6).
   * Re-proving an eager lemma instead of citing `Games.expect_simulate_eager` (the DL-33
     precedent).
   * Private group helpers that duplicate a Mathlib fact. The fill should check Mathlib's
     `orderOf` and `ZMod` API first and disclose whatever it adds.
6. **Audit of the hypothesis form (low).**
   * An auditor may ask whether a hypothesis stated as "the conclusion for one call" is checkable.
     L3 answers this: in the BB1 proofs every call is either deterministic or one sample coupled by
     a bijection.
   * The hypothesis is weaker than an explicit coupling, which implies it. Its conclusion has the
     same form, so it composes.
7. **Attribution (low).** The locations in [BGZ09] (the rule for adversary calls) and [Sho04]
   (bridging steps) are not pinned here: the PDFs are not in the repository, and nothing was read
   to confirm a section number (Q11).
8. **Verification cost (low).**
   * Phase S rebuilds one new module, the `Games` facade and the root.
   * The reader insertions in Phase F rebuild the IBE closure, and need canonical re-seals of
     `Defs` and `BonehBoyen`.
9. **Name collision (none found).** `expect_simulate_rel`, `prob_simulate_rel` and
   `expect_sample_rel` exist on no branch. Readers should not confuse `Games.expect_simulate_eager`
   with `ChallengeSim.expect_simulate_eager`.

### Open questions for Seyoon (recommended option first)

- **Q1. Placement.**
  - (A) A new `Games/Relational.lean`, imported by the `Games` facade.
  - (B) Append to `Games/Hopping.lean` after `expect_simulate_congr`. This touches a widely
    imported file and costs a large rebuild and re-seal.
- **Q2. Names.**
  - (A) `Games.ProbComp.expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel`, beside
    `ProbComp.expect_simulate_congr`.
  - (B) Root `Games.` names, as with `expect_simulate_eager`.
- **Q3. Form of the hypothesis.**
  - (A) The inline expectation hypothesis of §2.2: equal expectations of test functions that agree
    along `R`.
  - (B) A named predicate (for example `ProbComp.RelLaw R c₀ c₁`) with its `relLaw_iff` reader.
  - (C) An explicit coupling computation with an `AllOutputs` support condition.
- **Q4. Companions.**
  - (A) `prob_simulate_rel` and `expect_sample_rel` with the target.
  - (B) The target only. The fill then discharges calls inline with `expect_sample_equiv`.
- **Q5. Query budget.**
  - (A) None now.
  - (B) Also state `expect_simulate_rel_bounded` (a budget `cnt`/`κ`), so that DL-40 can later
    re-derive ETT's `expect_simulate_abs(_inv)` from it.
- **Q6. The averaging bound `abs (𝔼 f − 𝔼 g) ≤ 𝔼 h`.**
  - (A) The T2 fill writes it inline in T2's proof (a few lines, disclosed), and DL-40's promotion
    stays queued.
  - (B) Promote the ETT lemma now into `Games/Probability.lean` (a widely imported file).
  - (C) Add it to `Games/Relational.lean` in Phase S.
- **Q7. Reading `sidImpl` at the game's query type.**
  - (A) One reader, `IBEScheme.sidImpl_eq_oracleImpl`, in `Defs.lean` after T4's `_onSpec`
    readers. It is carried by the `bb1-sim` PR under an advance scope ruling from the probe.
  - (B) Three `sidImpl_{zero,one,two}_onSpec` readers in T4's form.
  - (C) Ask T4's PR to carry it, which widens T4's approved minimal scope.
- **Q8. Gate.**
  - (A) One `bb1-sim` gate after Gate 44, covering the Phase S statement, the reader insertions and
    the fill.
  - (B) Fold the Phase S statement into Gate 44's pack and audit the fill later.
- **Q9. Order and bases.**
  - (A) Phase S as its own small PR on the records tip. The fill is stacked on T4's PR, or based on
    the tip once T4 has merged.
  - (B) Everything on one branch stacked on T4's PR.
- **Q10. Group helpers** (`Z_p ≃ G` for `g ≠ 1`, exponent laws, identity injectivity on good
  coins).
  - (A) Public helpers with formula docstrings in the fill's helper module, disclosed.
  - (B) A reader-style request into the frozen `Pairing/Group.lean`.
- **Q11. Attribution of the lemma.**
  - (A) Cite [BGZ09] and [Sho04] at locations the maintainer pins from the sources.
  - (B) Treat it as a framework lemma and give only the design references; policy §2 allows tags to
    be omitted for technical glue.

---

## Appendix: search record

**Scanner.** A script was run on `9e7a9648` with `python3 -I`; it is in the job's scratch area and
is not committed. It lists every `theorem` or `lemma` under `TCSlib/` whose statement contains
`simulate` twice, or `simulate` together with two `QueryImpl`s. 49 hits; each was classified from
its statement, and the relevant ones were read in full and are listed in §2.4.

**Greps on `9e7a9648`.**
* `coupl|bisim` (case-insensitive) under `TCSlib/Cryptography`: prose only, in Lamport,
  HashAndSign, NonMalleability, FromPRF and the IBE docstrings. No generic lemma.
* `Barthe|pRHL|CertiCrypt|EasyCrypt|bridging step` under `TCSlib` and `blueprint`: no
  cryptographic citation.
* `theorem …simulate…` in `Games/`: the rows of §1.3.

**All local and remote branches:** `expect_simulate_rel|simulate_rel|σ → τ → Prop|bisim` under
`TCSlib/Cryptography`. Nothing found.

**The `Games/` layer:** `git diff 9e7a9648 a0e31483 -- TCSlib/Cryptography/Games` is empty.
