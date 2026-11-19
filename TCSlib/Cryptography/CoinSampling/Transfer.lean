/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.CoinSampling.Basic
import TCSlib.Cryptography.Games.Closeness
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coin draws in games: closeness and correctness transfer

A coin sampler `S` used inside a game is the computation `S.draw` (fair coins, decoded; `none`
when it gives up) or, with a default value `d` as the fallback, `S.drawD d`. This file connects
these draws to the exact draw `sample Ω` of the game:

* **security** (statistical): one draw followed by any continuation is `S.fail`-close to the
  exact draw followed by the same continuation (`close_draw_bind`, any fallback branch;
  `close_drawD_bind`, default fallback), and a fresh draw per oracle query costs `S.fail` per
  query (`close_simulate_draw`); `ProbComp.Close.bind` chains the draws of a game;
* **correctness** (exact): a default-fallback draw only produces possible outputs of the exact
  draw (`outputsSubset_drawD`), so with `OracleComp.OutputsSubset.bind`/`.simulate` every
  `AllOutputs` property of a scheme (perfect correctness, injectivity on reachable encodings)
  holds for its coin implementation without re-proof; a fallback branch that is correct by
  construction is `allOutputs_draw_bind`.

## Main definitions

* `CoinSampling.CoinSampler.draw`, `.drawD`: draws through a coin sampler in a game.

## Main results

* `CoinSampling.CoinSampler.expect_draw`: the mixture identity for games.
* `CoinSampling.CoinSampler.close_draw_bind`, `.close_drawD_bind`, `.close_simulate_draw`.
* `CoinSampling.allOutputs_sample_iff`: the possible outputs of an exact draw are all values.
* `CoinSampling.CoinSampler.outputsSubset_drawD`, `.allOutputs_draw_bind`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Lemma 51.17 (rejection sampling is uniform conditioned on success) and Definition 181.1
  (`ε`-closeness).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332, revision of 18 January 2006, §1.1 (bridging steps and the difference lemma).
-/

namespace TCSlib.Cryptography.CoinSampling

open TCSlib.Cryptography.Games

/-- **The possible outputs of an exact draw are all values**:
`(sample T).AllOutputs P ↔ ∀ t, P t` (`sample_eq`, `allOutputs_query`, and surjectivity of the
enumeration `(Fintype.equivFin T).symm`). Glue. -/
theorem allOutputs_sample_iff {T : Type} [Fintype T] [Nonempty T] {P : T → Prop} :
    (ProbComp.sample T).AllOutputs P ↔ ∀ t, P t := by
  rw [ProbComp.sample_eq, OracleComp.map_eq_bind, ProbComp.sampleFin_eq, OracleComp.query_bind,
    OracleComp.allOutputs_query]
  simp only [OracleComp.pure_bind, OracleComp.allOutputs_pure]
  refine ⟨fun h t => ?_, fun h y => h _⟩
  have := h (Fin.cast (Nat.sub_add_cancel Fintype.card_pos).symm (Fintype.equivFin T t))
  exact ((Fintype.equivFin T).symm_apply_apply t) ▸ this

namespace CoinSampler

variable {Ω β : Type} [Fintype Ω] {s : ℕ}

/-- **A draw through the sampler**: `s` uniform coins, decoded; `none` when it gives up.
Glue. -/
noncomputable def draw (S : CoinSampler Ω s) : ProbComp (Option Ω) :=
  S.dec <$> ProbComp.sample (Fin s → Bool)

/-- `S.draw = S.dec <$> sample (Fin s → Bool)`. -/
theorem draw_eq (S : CoinSampler Ω s) :
    S.draw = S.dec <$> ProbComp.sample (Fin s → Bool) := rfl

/-- **A draw with the default fallback** `d`: the decoded value, or `d` when the sampler gives
up. The standard fallback: `d` is a legitimate exact outcome, so no format changes and every
`AllOutputs` property transfers (`outputsSubset_drawD`). Glue. -/
noncomputable def drawD (S : CoinSampler Ω s) (d : Ω) : ProbComp Ω :=
  (fun c => (S.dec c).getD d) <$> ProbComp.sample (Fin s → Bool)

/-- `S.drawD d = (fun c => (S.dec c).getD d) <$> sample (Fin s → Bool)`. -/
theorem drawD_eq (S : CoinSampler Ω s) (d : Ω) :
    S.drawD d = (fun c => (S.dec c).getD d) <$> ProbComp.sample (Fin s → Bool) := rfl

/-- **The mixture identity for games**: for every `F : Option Ω → ℝ`,
`𝔼_{S.draw} F = fail · F(none) + (1 − fail) · 𝔼_{a ← Ω} F(some a)` [PS10, Lemma 51.17],
abstract form (`expect_map`, `Bridge.expect_sample_eq_uexp`, `uexp_comp_dec`). -/
theorem expect_draw [Nonempty Ω] (S : CoinSampler Ω s) (F : Option Ω → ℝ) :
    ProbComp.expect S.draw F =
      S.fail * F none +
        (1 - S.fail) * ProbComp.expect (ProbComp.sample Ω) (fun a => F (some a)) := by
  rw [draw_eq, ProbComp.expect_map, Bridge.expect_sample_eq_uexp, S.uexp_comp_dec,
    Bridge.expect_sample_eq_uexp]

/-- **One draw, any fallback branch**: a game that draws through `S` and continues with `K`
(`K none` is the fallback) is `fail`-close to the game that draws exactly and continues with
`K ∘ some` [PS10, Definition 181.1], a statistical bridging step of [Sho04, §1.1].

**Proof sketch.** `expect_bind`, then `expect_draw` with `F o = 𝔼_{K o} g ∈ [0, 1]`: the
difference is `fail · (F none − 𝔼_a F(some a))`, of absolute value at most `fail`. -/
theorem close_draw_bind [Nonempty Ω] (S : CoinSampler Ω s) (K : Option Ω → ProbComp β) :
    ProbComp.Close S.fail (S.draw.bind K)
      ((ProbComp.sample Ω).bind fun a => K (some a)) := (ProbComp.close_iff _ _ _).2 fun g hg => by
  rw [ProbComp.expect_bind, ProbComp.expect_bind, S.expect_draw]
  have h₀ := ProbComp.expect_mem_unit (K none) hg
  have h₁ := ProbComp.expect_mem_unit (ProbComp.sample Ω)
    (g := fun a => ProbComp.expect (K (some a)) g) fun a => ProbComp.expect_mem_unit _ hg
  have hf0 := S.fail_nonneg
  have hf1 := S.fail_le_one
  generalize ProbComp.expect (K none) g = x at h₀ ⊢
  generalize ProbComp.expect (ProbComp.sample Ω) (fun a => ProbComp.expect (K (some a)) g) = y
    at h₁ ⊢
  generalize S.fail = f at hf0 hf1 ⊢
  obtain ⟨hx0, hx1⟩ := h₀
  obtain ⟨hy0, hy1⟩ := h₁
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

/-- **One draw, default fallback**: `S.drawD d >>= k` is `fail`-close to `sample Ω >>= k`
(`close_draw_bind` with `K o = k (o.getD d)`). -/
theorem close_drawD_bind [Nonempty Ω] (S : CoinSampler Ω s) (d : Ω) (k : Ω → ProbComp β) :
    ProbComp.Close S.fail ((S.drawD d).bind k) ((ProbComp.sample Ω).bind k) :=
    (ProbComp.close_iff _ _ _).2 fun g hg => by
  have e : ProbComp.expect ((S.drawD d).bind k) g =
      ProbComp.expect (S.draw.bind fun o => k (o.getD d)) g := by
    rw [ProbComp.expect_bind, ProbComp.expect_bind, drawD_eq, draw_eq, ProbComp.expect_map,
      ProbComp.expect_map]
  rw [e]
  exact (ProbComp.close_iff _ _ _).1 (S.close_draw_bind (fun o => k (o.getD d))) g hg

/-- **A fresh draw per oracle query**: an oracle whose every call draws through `S` (body `K`,
fallback `K … none`) is, over a computation with at most `m` queries, `m · fail`-close to the
oracle that draws exactly (`ProbComp.Close.simulate` with `close_draw_bind`). The summed failure
bound for draws made inside oracles (keys per `KeyGen` query). -/
theorem close_simulate_draw [Nonempty Ω] {ι σ α : Type} {spec : OracleSpec ι}
    (S : CoinSampler Ω s) (K : ∀ i, spec.dom i → σ → Option Ω → ProbComp (spec.rng i × σ))
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (st : σ) :
    ProbComp.Close (m * S.fail)
      (Games.simulate (fun i x st' => S.draw.bind (K i x st')) c st)
      (Games.simulate
        (fun i x st' => (ProbComp.sample Ω).bind fun a => K i x st' (some a)) c st) :=
  ProbComp.Close.simulate S.fail_nonneg (fun i x st' => S.close_draw_bind (K i x st')) c m hc st

/-- **A default fallback only shrinks the possible outputs**: every possible output of
`S.drawD d` is a possible output of `sample Ω` (it is an element of `Ω`;
`allOutputs_sample_iff`). With `OracleComp.OutputsSubset.bind` and `.simulate`, a scheme whose
exact draws are replaced by default-fallback coin draws keeps **every** `AllOutputs` property.
Glue. -/
theorem outputsSubset_drawD [Nonempty Ω] (S : CoinSampler Ω s) (d : Ω) :
    OracleComp.OutputsSubset (S.drawD d) (ProbComp.sample Ω) :=
    (OracleComp.outputsSubset_iff _ _).2 fun P hP => by
  have hall := allOutputs_sample_iff.1 hP
  rw [drawD_eq, OracleComp.map_eq_bind]
  exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun c _ =>
    OracleComp.allOutputs_pure.2 (hall _)

/-- **A fallback branch that is correct by construction keeps correctness**: if every
continuation `K (some a)` and the fallback `K none` satisfy `P` at all outputs, so does the
coin draw followed by `K` (`allOutputs_true`, `AllOutputs.bind`). The form for fallbacks that
change the output format, such as sending in the clear. Glue. -/
theorem allOutputs_draw_bind (S : CoinSampler Ω s) {K : Option Ω → ProbComp β} {P : β → Prop}
    (hsome : ∀ a, (K (some a)).AllOutputs P) (hnone : (K none).AllOutputs P) :
    (S.draw.bind K).AllOutputs P :=
  OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun o _ => by
    cases o with
    | none => exact hnone
    | some a => exact hsome a

end CoinSampler

end TCSlib.Cryptography.CoinSampling
