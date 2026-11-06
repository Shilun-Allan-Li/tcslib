/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorLemmas
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorMachine
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the simulator

The zero-knowledge half of [PS10, Proposition 127.6]: the simulator of [PS10, Algorithm 128.7]
for one iteration of [PS10, Protocol 127.5] (Alg-128.7), its efficiency (Claim-128.a), and
[PS10, Proposition 128.8] (Prop-128.8) through the hybrid chain of the text's proof,
corrected: the simulator `S` guesses an edge `e'` and a pair of distinct colours, commits to
them at the endpoints of `e'` and to the colour `0` elsewhere, runs `V*` and succeeds if `V*`
asks for `e'`; `S'` (Claim-129.a) uses the witness and a uniform colour permutation `π` at the
two endpoints instead of a uniform distinct pair — identically distributed by the bijection
`π ↦ (π a, π b)` between `S₃` and the distinct pairs (Lem-129.b); `S''` (Claim-129.c) commits
like the honest prover to `π (c k)` for **all** `k` but keeps the restart rule, so each attempt
succeeds with probability exactly `1/|E|` and, conditioned on success, outputs the honest view;
`S' ≈ S''` (Claim-129.d) by a hybrid over the `n|E|` attempts and the multi-value hiding of
the commitment (`Commitment.multiHiding`).

Two layers (D2): the *concrete* layer works over typed coins (`Fin |E|`, `Equiv.Perm (Fin 3)`,
the distinct colour pairs, the commitment randomness `Fin n → Fin ℓ(n) → Bool`, and the coins
`ρ` of an arbitrary verifier `V*` given as its reply function); the *string* layer is the
simulator `colSim` run by a uniform `NUPPT` on the tape layout of `colSimBlock`.

**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT
(D8's definition of `ZK`); it makes at most `n|E|` attempts and outputs `⊥ = []` on failure, as
the text does (Algorithm 128.7, steps 4–5), and the failure costs the text's own term
`(1 − 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
rejection-sampled from the bit tapes; the hybrid over attempts has `n|E|` steps (the text says
`2n|E|`) and the text's `6|E|` sub-hybrid is replaced by a non-uniform choice of the worst
`(e', π)`; "`k ∈ [m] ∖ {i', j'}`" is read as `k ∈ [n]`; if `E = ∅` the simulator commits to
all-zero colours and succeeds at once.

## Main definitions

* `TCSlib.Cryptography.ColorPair`, `TCSlib.Cryptography.colorPairEquiv` — the distinct colour
  pairs and the bijection `S₃ ≃ ColorPair` (Lem-129.b).
* `TCSlib.Cryptography.colRealView` — the view of `V*` in one honest iteration (typed).
* `TCSlib.Cryptography.colSimAttempt`, `TCSlib.Cryptography.colSimAttemptW`,
  `TCSlib.Cryptography.colSimAttemptH` — one attempt of `S`, `S'`, `S''`;
  `TCSlib.Cryptography.colSimTrunc`, `colSimTruncW`, `colSimTruncH` — their `N`-fold truncations;
  `TCSlib.Cryptography.colSimHyb`, `TCSlib.Cryptography.colSimAttemptPlanted`,
  `TCSlib.Cryptography.colSimRed` — the hybrids and the hiding reduction (Claim-129.d).
* `TCSlib.Cryptography.colSim`, `TCSlib.Cryptography.colSimCoins` — the string simulator
  [PS10, Algorithm 128.7] (Alg-128.7).

## Main results

* `TCSlib.Cryptography.uprob_colSimTruncW_eq` — `S ≡ S'` (Claim-129.a, proved).
* `TCSlib.Cryptography.uprob_colSimAttemptH_none`, `uprob_colSimAttemptH_some`,
  `TCSlib.Cryptography.statClose_colSimTruncH` — `S''` fails with probability `(1 - 1/|E|)^N`
  and is perfect given success (Claim-129.c).
* `TCSlib.Cryptography.exists_colSimRed_ge` — `S' ≈ S''` by hybrids (Claim-129.d).
* `TCSlib.Cryptography.exists_colSimulator` — the simulator is a uniform PPT (Claim-128.a).
* `TCSlib.Cryptography.col_zk` — **[PS10, Proposition 128.8]**: the protocol is
  zero-knowledge for `R_3COL`; `TCSlib.Cryptography.col_zeroKnowledgeProof` — **[PS10,
  Proposition 127.6]** assembled (Prop-127.6).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6, Algorithm 128.7, Proposition 128.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (hybrid arguments at the concrete layer).
-/

namespace TCSlib.Cryptography

open Complexity Turing ColSimLemmas

/-! ### Distinct colour pairs (Lem-129.b) -/

/-- The ordered pairs of distinct colours, the simulator's guess `(c'_{i'}, c'_{j'})` of
[PS10, Algorithm 128.7, step 1]. -/
abbrev ColorPair : Type := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- There are six distinct colour pairs. -/
theorem card_colorPair : Fintype.card ColorPair = 6 := by decide

/-- A permutation of the three colours is determined by its values on two distinct colours. -/
theorem perm3_ext_of_ne : ∀ a b : Fin 3, a ≠ b → ∀ π σ : Equiv.Perm (Fin 3),
    π a = σ a → π b = σ b → π = σ := by
  decide

/-- **`π ↦ (π a, π b)` is a bijection from `S₃` to the distinct colour pairs** for `a ≠ b`
[PS10, proof of Proposition 128.8, "`S` and `S'` are identically distributed"] (Lem-129.b):
injective by `perm3_ext_of_ne`, bijective since both sides have six elements. -/
noncomputable def colorPairEquiv {a b : Fin 3} (hab : a ≠ b) : Equiv.Perm (Fin 3) ≃ ColorPair :=
  Equiv.ofBijective (fun π => ⟨(π a, π b), fun h => hab (π.injective h)⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun π σ h => perm3_ext_of_ne a b hab π σ (congrArg (fun p : ColorPair => p.1.1) h)
        (congrArg (fun p : ColorPair => p.1.2) h),
        by rw [Fintype.card_perm, Fintype.card_fin, card_colorPair]; rfl⟩)

/-- Unfolding of `colorPairEquiv`. -/
@[simp] theorem colorPairEquiv_apply {a b : Fin 3} (hab : a ≠ b) (π : Equiv.Perm (Fin 3)) :
    (colorPairEquiv hab π : Fin 3 × Fin 3) = (π a, π b) := rfl

/-! ### The typed views of one iteration -/

/-- The simulator's colouring [PS10, Algorithm 128.7, step 1]: the guessed pair at the
endpoints of the guessed edge `p = (i', j')`, the colour `0` ("`1`" in the text) elsewhere. -/
def simColors {n : ℕ} (p : Fin n × Fin n) (ab : ColorPair) : Fin n → Fin 3 :=
  fun k => if k = p.1 then ab.1.1 else if k = p.2 then ab.1.2 else 0

/-- The colouring of the hybrid simulator `S'` [PS10, proof of Proposition 128.8]: the
witness colours permuted by `π` at the endpoints of `p`, the colour `0` elsewhere. -/
def simColorsW {n : ℕ} (p : Fin n × Fin n) (π : Equiv.Perm (Fin 3)) (c : Fin n → Fin 3) :
    Fin n → Fin 3 :=
  fun k => if k = p.1 then π (c p.1) else if k = p.2 then π (c p.2) else 0

/-- `S'`'s colouring is `S`'s colouring at the pair `(π (c i'), π (c j'))`. -/
theorem simColorsW_eq {n : ℕ} (p : Fin n × Fin n) (π : Equiv.Perm (Fin 3)) {c : Fin n → Fin 3}
    (hp : c p.1 ≠ c p.2) : simColorsW p π c = simColors p (colorPairEquiv hp π) := rfl

/-- A typed view of `V*` in one iteration: its coins, the commitment message and the
prover's last message (the common input and `z` being fixed). -/
abbrev ColView (ρ : Type*) : Type _ := ρ × List Bool × List Bool

section Typed

variable (Com : List Bool → List Bool) {n : ℕ} (ℓn : ℕ) (G : Graph n) {ρ : Type*}

/-- The view of `V*` (reply function `V`, coins `ρ`) in one honest iteration of
[PS10, Protocol 127.5] with witness `c`, prover coins `(π, r)`: the commitments to `π (c i)`,
and the opening of the edge `V*` names (or `[]` if `E = ∅`). -/
def colRealView (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) : ColView ρ :=
  let c' : Fin n → Fin 3 := fun i => w.1.1 (c i)
  let com := colCommit Com n ℓn c' w.1.2
  (w.2, com, match edgeAt G (edgeIdxOfMsg (edgeCount G) (V com w.2)) with
    | some p => colOpen c' w.1.2 p
    | none => [])

/-- One attempt of the simulator [PS10, Algorithm 128.7] (Alg-128.7, typed) on the coins
`((e', (a, b)), r, r_{V*})`: commit to `simColors (edgeOf G e') (a, b)`, run `V*`, and output
the view if `V*` names the edge `e'`, `none` otherwise. -/
def colSimAttempt (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ) : Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' := simColors p w.1.1.2
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- One attempt of the hybrid simulator `S'` [PS10, proof of Proposition 128.8]: as
`colSimAttempt` with the colours `(π (c i'), π (c j'))` at the endpoints for a uniform `π`. -/
def colSimAttemptW (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' := simColorsW p w.1.1.2 c
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- One attempt of the hybrid simulator `S''` [PS10, proof of Proposition 128.8]: commit to
`π (c k)` for every `k` (like the honest prover), but output the view only if `V*` names the
guessed edge `e'`. -/
def colSimAttemptH (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' : Fin n → Fin 3 := fun i => w.1.1.2 (c i)
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- The coin bijection of Claim-129.a: `((e', π), r, ρ) ↦ ((e', (π (c i'), π (c j'))), r, ρ)`
for a proper colouring `c` (`colorPairEquiv` fibrewise over `e'`). -/
noncomputable def simCoinsEquiv {c : Fin n → Fin 3} (hc : ProperColoring G c) :
    ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ ≃
      ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ :=
  Equiv.prodCongr (Equiv.prodCongr
    (Equiv.prodCongrRight fun e => colorPairEquiv (hc.ne (edgeOf_adj G e))) (Equiv.refl _))
    (Equiv.refl ρ)

/-- **`S ≡ S'`, one attempt** [PS10, proof of Proposition 128.8, "it directly follows that
`S(x, z)` and `S'(x, z, y)` are identically distributed"] (Claim-129.a): for a proper colouring
`c` the attempts of `S'` and `S` have the same law — they agree pointwise along the coin
bijection `simCoinsEquiv` (`uprob_comp_equiv`). -/
theorem uprob_colSimAttemptW_eq [Fintype ρ] {c : Fin n → Fin 3} (hc : ProperColoring G c)
    (V : List Bool → ρ → List Bool) (T : Option (ColView ρ) → Prop) :
    uprob (fun w => T (colSimAttemptW Com ℓn G c V w)) =
      uprob (fun w => T (colSimAttempt Com ℓn G V w)) := by
  rw [← uprob_comp_equiv (simCoinsEquiv ℓn G (ρ := ρ) hc)]
  rfl

/-! ### The truncated simulators -/

/-- The first `some` among `N` optional values (the output of the first successful attempt). -/
def firstSome {α : Type*} {N : ℕ} (f : Fin N → Option α) : Option α :=
  (List.finRange N).findSome? f

/-- `firstSome` is `none` iff every attempt fails. -/
theorem firstSome_eq_none_iff {α : Type*} {N : ℕ} (f : Fin N → Option α) :
    firstSome f = none ↔ ∀ t, f t = none := by
  unfold firstSome
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- The simulator truncated at `N` attempts with independent coins [PS10, Algorithm 128.7,
steps 4–5] (Alg-128.7, typed): the first successful attempt's view, `none` (`fail`) if all
`N` fail. -/
def colSimTrunc (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttempt Com ℓn G V (w t)

/-- `S'` truncated at `N` attempts. -/
def colSimTruncW (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttemptW Com ℓn G c V (w t)

/-- `S''` truncated at `N` attempts. -/
def colSimTruncH (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttemptH Com ℓn G c V (w t)

/-- **`S ≡ S'`, `N` attempts** (Claim-129.a): the truncated `S'` and `S` have the same law
(`simCoinsEquiv` on every attempt, `Equiv.piCongrRight`). -/
theorem uprob_colSimTruncW_eq [Fintype ρ] {c : Fin n → Fin 3} (hc : ProperColoring G c)
    (V : List Bool → ρ → List Bool) (N : ℕ) (T : Option (ColView ρ) → Prop) :
    uprob (fun w => T (colSimTruncW Com ℓn G c V N w)) =
      uprob (fun w => T (colSimTrunc Com ℓn G V N w)) := by
  rw [← uprob_comp_equiv (Equiv.piCongrRight fun _ : Fin N => simCoinsEquiv ℓn G (ρ := ρ) hc)]
  rfl

/-- **An attempt of `S''` fails with probability exactly `1 - 1/|E|`** [PS10, proof of
Proposition 128.8, "as `i, j` and `i', j'` are independently chosen"] (Claim-129.c (i)).

**Proof sketch.** The commitment message and `V*`'s reply do not depend on `e'`, so after
reindexing the coins as `Fin |E| × ((S₃ × randomness) × ρ)` (`Equiv.prodAssoc`,
`uprob_comp_equiv`) and conditioning on the second component (`uprob_prod`), the failure event
is `e' ≠ f(rest)` for a fixed index, of probability `1 - 1/|E|`
(`OneWay.uprob_eq_one_div_card`, `uprob_not`, `edgeIdxOfMsg_lt`). -/
theorem uprob_colSimAttemptH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) :
    uprob (fun w => colSimAttemptH Com ℓn G c V w = none) = 1 - 1 / (edgeCount G : ℝ) := by
  rw [← uprob_comp_equiv (attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm]
  have key : ∀ z : ((Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) × Fin (edgeCount G),
      colSimAttemptH Com ℓn G c V
          ((attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm z) = none ↔
        ¬ edgeIdxOfMsg (edgeCount G)
          (V (colCommit Com n ℓn (fun i => z.1.1.1 (c i)) z.1.1.2) z.1.2) = (z.2 : ℕ) := by
    rintro ⟨⟨⟨π, r⟩, ρ₀⟩, e⟩
    show (if edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) = (e : ℕ)
        then some (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          colOpen (fun i => π (c i)) r (edgeOf G e)) else none) = none ↔ _
    by_cases h : edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
      (e : ℕ)
    · rw [if_pos h]
      exact ⟨fun h' => (Option.some_ne_none _ h').elim, fun h' => (h' h).elim⟩
    · rw [if_neg h]
      exact ⟨fun _ => h, fun _ => rfl⟩
  rw [OneWay.uprob_congr key]
  exact uprob_ne_idx hm (fun a : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
    edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => a.1.1 (c i)) a.1.2) a.2))
    (fun a => edgeIdxOfMsg_lt hm _)

/-- **Conditioned on success, an attempt of `S''` is the honest view** [PS10, proof of
Proposition 128.8, "the following distributions are identical"] (Claim-129.c (ii)): for every
test set `T`, the probability that an attempt succeeds with a view in `T` is `1/|E|` times the
probability that the real view lies in `T`.

**Proof sketch.** On the coins `((e', π), r, ρ)` the attempt commits exactly as the honest
prover with `(π, r)`; it succeeds iff `V*`'s reply decodes to `e'` and then outputs
`colRealView (π, r, ρ)` (`edgeAt_eq_some_edgeOf` identifies the opened edge). Reindex as in
`uprob_colSimAttemptH_none` and condition on `(π, r, ρ)`: the inner probability over `e'` is
`1/|E|` if `T (colRealView …)` holds and `0` otherwise (`OneWay.uprob_eq_one_div_card`,
`uprob_false`); `uprob_prod` and `uexp` linearity give the product. -/
theorem uprob_colSimAttemptH_some [Fintype ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (T : ColView ρ → Prop) :
    uprob (fun w => ∃ v, colSimAttemptH Com ℓn G c V w = some v ∧ T v) =
      1 / (edgeCount G : ℝ) *
        uprob (fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
          T (colRealView Com ℓn G c V w)) := by
  rw [← uprob_comp_equiv (attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm]
  have key : ∀ z : ((Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) × Fin (edgeCount G),
      (∃ v, colSimAttemptH Com ℓn G c V
          ((attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm z) = some v ∧ T v) ↔
        (edgeIdxOfMsg (edgeCount G)
          (V (colCommit Com n ℓn (fun i => z.1.1.1 (c i)) z.1.1.2) z.1.2) = (z.2 : ℕ) ∧
          T (colRealView Com ℓn G c V z.1)) := by
    rintro ⟨⟨⟨π, r⟩, ρ₀⟩, e⟩
    show (∃ v, (if edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
        (e : ℕ) then some (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          colOpen (fun i => π (c i)) r (edgeOf G e)) else none) = some v ∧ T v) ↔
      (edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) = (e : ℕ) ∧
        T (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          match edgeAt G (edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀))
            with
          | some p => colOpen (fun i => π (c i)) r p
          | none => []))
    by_cases h : edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
      (e : ℕ)
    · rw [if_pos h, h, edgeAt_eq_some_edgeOf]
      exact ⟨fun ⟨v, hv, hT⟩ => ⟨rfl, by rw [← Option.some.inj hv] at hT; exact hT⟩,
        fun ⟨_, hT⟩ => ⟨_, rfl, hT⟩⟩
    · rw [if_neg h]
      exact ⟨fun ⟨v, hv, _⟩ => (Option.noConfusion hv), fun ⟨h', _⟩ => (h h').elim⟩
  rw [OneWay.uprob_congr key]
  exact uprob_eq_idx_and hm (fun a : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
    edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => a.1.1 (c i)) a.1.2) a.2))
    (fun a => edgeIdxOfMsg_lt hm _) (fun a => T (colRealView Com ℓn G c V a))

/-- **The truncated `S''` fails with probability `(1 - 1/|E|)^N`** [PS10, proof of Proposition
128.8, "`S'` [sic: `S''`] fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the
attempts use disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability
`1 - 1/|E|` (`uprob_colSimAttemptH_none`). -/
theorem uprob_colSimTruncH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
    uprob (fun w => colSimTruncH Com ℓn G c V N w = none) = (1 - 1 / (edgeCount G : ℝ)) ^ N := by
  unfold colSimTruncH
  rw [OneWay.uprob_congr fun w => firstSome_eq_none_iff _,
    OneWay.uprob_pi_forall (ι := Fin N) (fun w => colSimAttemptH Com ℓn G c V w = none),
    uprob_colSimAttemptH_none Com ℓn G hm c V, Fintype.card_fin]

/-- **The truncated `S''` is statistically `(1 - 1/|E|)^N`-close to the honest view**
[PS10, proof of Proposition 128.8, "`view_{V*}` and `S''` can be distinguished with probability
at most `O(e^{-n})`"] (Claim-129.c): for every test set `T` of optional views,
`|Pr[T(S''_N)] - Pr[T(some view)]| ≤ (1 - 1/|E|)^N`.

**Proof sketch.** Decompose the event `T(S''_N)` by the index of the first successful attempt
(`firstSome`/`List.findSome?` on `List.finRange N`): the attempts have disjoint coins, so by
`uprob_prod`/`OneWay.uprob_update` the `t`-th term is `(1 - 1/|E|)^t · Pr[∃ v, attempt = some v ∧
T (some v)] = (1 - 1/|E|)^t (1/|E|) Pr[T (some view)]` (`uprob_colSimAttemptH_some`,
`uprob_colSimAttemptH_none`); the geometric sum gives
`Pr[T(S''_N)] = (1 - (1 - 1/|E|)^N) Pr[T (some view)] + (1 - 1/|E|)^N [T none]`
(`uprob_colSimTruncH_none`), within `(1 - 1/|E|)^N` of `Pr[T (some view)]`. -/
theorem statClose_colSimTruncH [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
    StatClose (colSimTruncH Com ℓn G c V N)
      (fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
        some (colRealView Com ℓn G c V w))
      ((1 - 1 / (edgeCount G : ℝ)) ^ N) := by
  have hθ : 0 ≤ 1 - 1 / (edgeCount G : ℝ) := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hm)]
    exact_mod_cast hm
  haveI : Nonempty (AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :=
    ⟨(((⟨0, hm⟩, 1), fun _ _ => false), Classical.arbitrary ρ)⟩
  exact statClose_truncAttempts (colSimAttemptH Com ℓn G c V) (colRealView Com ℓn G c V) hθ
    (uprob_colSimAttemptH_none Com ℓn G hm c V)
    (fun T => by rw [uprob_colSimAttemptH_some Com ℓn G hm c V T]; congr 1; ring) N

/-! ### The hybrids `S' ≈ S''` (Claim-129.d) -/

/-- The `k`-th hybrid simulator [PS10, proof of Proposition 128.8, "`S_k` proceeds as `S''` in
the first `k` iterations and like `S'` in the remaining ones"]: attempts `< k` are `S''`
attempts, the others `S'` attempts. -/
def colSimHyb (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N k : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => if (t : ℕ) < k then colSimAttemptH Com ℓn G c V (w t)
    else colSimAttemptW Com ℓn G c V (w t)

/-- The zeroth hybrid is `S'`. -/
theorem colSimHyb_zero (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    colSimHyb Com ℓn G c V N 0 w = colSimTruncW Com ℓn G c V N w := by
  simp [colSimHyb, colSimTruncW]

/-- The `N`-th hybrid is `S''`. -/
theorem colSimHyb_self (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    colSimHyb Com ℓn G c V N N w = colSimTruncH Com ℓn G c V N w := by
  simp [colSimHyb, colSimTruncH]

/-- The planted attempt of the hiding reduction: with the guessed edge `e₀` and permutation
`π₀` fixed, the commitments at the endpoints of `e₀` are made by the reduction itself (to
`π₀ (c i')`, `π₀ (c j')`, which `S'` and `S''` share) and all other commitments are read from
the challenger's vector `cv` (`msgAt`); the restart rule and the opening are as in the
attempts. -/
def colSimAttemptPlanted (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3)) (cv : List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G e₀
  let c' : Fin n → Fin 3 := fun i => π₀ (c i)
  let com := Strategy.encodeMsgs (List.ofFn fun i =>
    if i = p.1 ∨ i = p.2 then Com (pairEncode (List.ofFn (padColor n (c' i))) (List.ofFn (w.1.2 i)))
    else msgAt cv i)
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (e₀ : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- The hiding reduction at hybrid index `k` with the worst `(e₀, π₀)` planted
[PS10, proof of Proposition 128.8, the reduction to the hiding property] (Claim-129.d): on a
challenge commitment vector `cv` it runs attempts `< k` as `S''`, attempt `k` as the planted
attempt on `cv`, the later attempts as `S'`, and hands the first success to `D`. -/
def colSimRed {ρ' : Type*} (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (k : Fin N) (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3))
    (D : Option (ColView ρ) → ρ' → Bool) :
    List Bool →
      (Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) × ρ' →
        Bool :=
  fun cv z => D (firstSome fun t =>
    if (t : ℕ) < k then colSimAttemptH Com ℓn G c V (z.1 t)
    else if t = k then colSimAttemptPlanted Com ℓn G c V e₀ π₀ cv (z.1 t)
    else colSimAttemptW Com ℓn G c V (z.1 t)) z.2

/-- The `S'` colouring at an endpoint of `p` is the permuted witness colour. -/
private theorem simColorsW_of_mem {m : ℕ} (p : Fin m × Fin m) (π : Equiv.Perm (Fin 3))
    (c : Fin m → Fin 3) {i : Fin m} (hi : i = p.1 ∨ i = p.2) :
    simColorsW p π c i = π (c i) := by
  unfold simColorsW
  rcases hi with rfl | rfl
  · rw [if_pos rfl]
  · by_cases h : p.2 = p.1
    · rw [if_pos h, h]
    · rw [if_neg h, if_pos rfl]

/-- **The planted attempt on the `S'` commitment vector is an `S'` attempt** with the merged
randomness (the reduction's at the endpoints of the planted edge, the challenger's elsewhere)
and the planted `(e₀, π₀)`.

**Proof sketch.** The commitment messages agree position by position: at the endpoints both
commit to `π₀ (c i)` (`simColorsW_of_mem`) with the attempt's randomness, elsewhere the planted
attempt reads `Com ⟨pad (simColorsW … i), r' i⟩` off the challenge (`msgAt_multiCom`) and
`mergeAt` selects `r' i`; the openings agree since `mergeAt` is the attempt's randomness at the
endpoints (`mergeAt_fst`, `mergeAt_snd`); the success test and the output then coincide. -/
private theorem colSimAttemptPlanted_W (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (ep : Fin (edgeCount G) × Equiv.Perm (Fin 3)) (r' : Fin n → Fin ℓn → Bool)
    (w : AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :
    colSimAttemptPlanted Com ℓn G c V ep.1 ep.2
        (multiCom Com (fun i => padColor n (simColorsW (edgeOf G ep.1) ep.2 c i)) r') w =
      colSimAttemptW Com ℓn G c V ((ep, mergeAt (edgeOf G ep.1) w.1.2 r'), w.2) := by
  set p := edgeOf G ep.1 with hp
  have hcom : Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i) =
      colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r') := by
    show _ = Strategy.encodeMsgs (List.ofFn fun i =>
      Com (pairEncode (List.ofFn (padColor n (simColorsW p ep.2 c i)))
        (List.ofFn (mergeAt p w.1.2 r' i))))
    congr 2
    funext i
    by_cases hi : i = p.1 ∨ i = p.2
    · rw [if_pos hi, simColorsW_of_mem p ep.2 c hi]
      simp only [mergeAt, hi, if_true]
    · rw [if_neg hi, msgAt_multiCom]
      simp only [mergeAt, hi, if_false]
  have hopen : colOpen (fun i => ep.2 (c i)) w.1.2 p =
      colOpen (simColorsW p ep.2 c) (mergeAt p w.1.2 r') p := by
    unfold colOpen
    rw [mergeAt_fst, mergeAt_snd, simColorsW_of_mem p ep.2 c (Or.inl rfl),
      simColorsW_of_mem p ep.2 c (Or.inr rfl)]
  show (if edgeIdxOfMsg (edgeCount G) (V (Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i)) w.2) =
        (ep.1 : ℕ) then
      some (w.2, Strategy.encodeMsgs (List.ofFn fun i =>
        if i = p.1 ∨ i = p.2 then
          Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
        else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i),
        colOpen (fun i => ep.2 (c i)) w.1.2 p)
    else none) =
    (if edgeIdxOfMsg (edgeCount G)
        (V (colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r')) w.2) = (ep.1 : ℕ) then
      some (w.2, colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r'),
        colOpen (simColorsW p ep.2 c) (mergeAt p w.1.2 r') p)
    else none)
  rw [hcom, hopen]

/-- **The planted attempt on the `S''` commitment vector is an `S''` attempt** with the merged
randomness and the planted `(e₀, π₀)`.

**Proof sketch.** As `colSimAttemptPlanted_W`: every position of the challenge commits to
`π₀ (c i)` (`msgAt_multiCom`), so the planted message is `colCommit (π₀ ∘ c)` with the merged
randomness, and the openings agree by `mergeAt_fst`, `mergeAt_snd`. -/
private theorem colSimAttemptPlanted_H (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (ep : Fin (edgeCount G) × Equiv.Perm (Fin 3)) (r' : Fin n → Fin ℓn → Bool)
    (w : AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :
    colSimAttemptPlanted Com ℓn G c V ep.1 ep.2
        (multiCom Com (fun i => padColor n (ep.2 (c i))) r') w =
      colSimAttemptH Com ℓn G c V ((ep, mergeAt (edgeOf G ep.1) w.1.2 r'), w.2) := by
  set p := edgeOf G ep.1 with hp
  have hcom : Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i) =
      colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') := by
    show _ = Strategy.encodeMsgs (List.ofFn fun i =>
      Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (mergeAt p w.1.2 r' i))))
    congr 2
    funext i
    by_cases hi : i = p.1 ∨ i = p.2
    · rw [if_pos hi]
      simp only [mergeAt, hi, if_true]
    · rw [if_neg hi, msgAt_multiCom]
      simp only [mergeAt, hi, if_false]
  have hopen : colOpen (fun i => ep.2 (c i)) w.1.2 p =
      colOpen (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') p := by
    unfold colOpen
    rw [mergeAt_fst, mergeAt_snd]
  show (if edgeIdxOfMsg (edgeCount G) (V (Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i)) w.2) =
        (ep.1 : ℕ) then
      some (w.2, Strategy.encodeMsgs (List.ofFn fun i =>
        if i = p.1 ∨ i = p.2 then
          Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
        else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i),
        colOpen (fun i => ep.2 (c i)) w.1.2 p)
    else none) =
    (if edgeIdxOfMsg (edgeCount G)
        (V (colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r')) w.2) = (ep.1 : ℕ) then
      some (w.2, colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r'),
        colOpen (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') p)
    else none)
  rw [hcom, hopen]

/-- **`S' ≈ S''` by hybrids and multi-value hiding** [PS10, proof of Proposition 128.8,
"by the hybrid lemma … `D` distinguishes `S_k` and `S_{k+1}`"] (Claim-129.d, concrete): for
every distinguisher `D` of optional views there are a hybrid index `k < N`, an edge `e₀` and a
permutation `π₀` such that the advantage of `D` between the truncated `S'` and `S''`, divided
by `N`, is at most the advantage of the explicit reduction `colSimRed … k e₀ π₀ D` between the
commitment vectors (`multiCom`) to the `S'` colours `simColorsW (edgeOf G e₀) π₀ c` and to the
`S''` colours `π₀ ∘ c`.

**Deviation:** `N` hybrid steps (the text's `2n|E|`), the `6|E|` sub-hybrid replaced by the
non-uniform choice of `(e₀, π₀)`.

**Proof sketch.** `exists_hybrid_gap` on `k ↦ acceptProb (colSimHyb … N k) D`
(`colSimHyb_zero`, `colSimHyb_self` are the ends) gives `k` with gap `≥ distAdv / N`. The gap at
`k` is the average over attempt `k`'s `(e', π)` (`uprob_prod` on the `k`-th block,
`acceptProb_update`) of the difference between the planted attempt fed the `S'` vector and
fed the `S''` vector: on `cv = multiCom (pad ∘ simColorsW p π) r'` the planted attempt's
message is `colCommit (simColorsW p π) r''` for the randomness `r''` equal to `r'` off the
endpoints and to `w`'s randomness at the endpoints (`msgAt_encodeMsgs`, `List.getElem_ofFn`),
whose law is uniform (`OneWay.uprob_update` twice), so the acceptance probability is that of
hybrid `k`; likewise the `S''` vector gives hybrid `k + 1`. An average of absolute values
bounds the absolute value of the average, so some `(e₀, π₀)` attains at least the gap
(`Finset.exists_le_of_sum_le` / `uexp` averaging as in `Protocol.exists_proverCoins_le`). -/
theorem exists_colSimRed_ge [Fintype ρ] {ρ' : Type*} [Fintype ρ'] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) (hN : 0 < N)
    (D : Option (ColView ρ) → ρ' → Bool) :
    ∃ (k : Fin N) (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3)),
      distAdv (colSimTruncW Com ℓn G c V N) (colSimTruncH Com ℓn G c V N) D / N ≤
        distAdv
          (fun r : Fin n → Fin ℓn → Bool =>
            multiCom Com (fun i => padColor n (simColorsW (edgeOf G e₀) π₀ c i)) r)
          (fun r : Fin n → Fin ℓn → Bool => multiCom Com (fun i => padColor n (π₀ (c i))) r)
          (colSimRed Com ℓn G c V N k e₀ π₀ D) := by
  obtain ⟨k, ep, h⟩ := exists_hybRed_ge hm hN (colSimAttemptH Com ℓn G c V)
    (colSimAttemptW Com ℓn G c V) D (edgeOf G)
    (fun ep cv => colSimAttemptPlanted Com ℓn G c V ep.1 ep.2 cv)
    (fun ep r => multiCom Com (fun i => padColor n (simColorsW (edgeOf G ep.1) ep.2 c i)) r)
    (fun ep r => multiCom Com (fun i => padColor n (ep.2 (c i))) r)
    (fun ep r' w => colSimAttemptPlanted_W Com ℓn G c V ep r' w)
    (fun ep r' w => colSimAttemptPlanted_H Com ℓn G c V ep r' w)
  refine ⟨k, ep.1, ep.2, ?_⟩
  have h0 : acceptProb (colSimTruncW Com ℓn G c V N) D =
      acceptProb (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N 0) D := by
    simp only [acceptProb_def]
    exact congrArg uprob (funext fun z => by rw [← colSimHyb_zero Com ℓn G c V N z.1]; rfl)
  have hN' : acceptProb (colSimTruncH Com ℓn G c V N) D =
      acceptProb (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N N) D := by
    simp only [acceptProb_def]
    exact congrArg uprob (funext fun z => by rw [← colSimHyb_self Com ℓn G c V N z.1]; rfl)
  calc distAdv (colSimTruncW Com ℓn G c V N) (colSimTruncH Com ℓn G c V N) D / N
      = distAdv (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N 0)
          (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N N) D / N := by
        rw [distAdv, distAdv, h0, hN']
    _ ≤ _ := h

end Typed

/-! ### The fill ladder of `col_zk` -/

section ColZKLadder

variable {Com : List Bool → List Bool} {ℓ : PolyExpr}

/-- **The hiding reduction with its attempt table fixed** [PS10, proof of Proposition 128.8,
the reduction to the hiding property] (Claim-129.d, step (4) of `col_zk`'s sketch): for `m > 0`
and `N > 0` attempts there are a hybrid index `k`, a planted `(e₀, π₀)` and a table `w₀` of the
other attempts' coins such that the advantage of `D'` between the truncated `S'` and `S''`,
divided by `N`, is at most the advantage between the commitment vectors to the `S'` and `S''`
colours of the reduction `colSimRed … k e₀ π₀ D'` with its attempt table fixed to `w₀`.

**Proof sketch.** `exists_colSimRed_ge` gives `k, e₀, π₀`; averaging over the reduction's attempt
table (`CommitmentLemmas.exists_fixCoins`, the table being nonempty as `m > 0` and `ρ ≠ ∅`)
fixes some `w₀` without loss. -/
theorem exists_colSimRed_fixCoins {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (c : Fin n → Fin 3)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (V : List Bool → ρ → List Bool) (N : ℕ) (hN : 0 < N)
    {ρ' : Type*} [Fintype ρ'] (D' : Option (ColView ρ) → ρ' → Bool) :
    ∃ (k : Fin N) (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3))
      (w₀ : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin (ℓ.eval n) → Bool)) × ρ),
      distAdv (colSimTruncW Com (ℓ.eval n) G c V N) (colSimTruncH Com (ℓ.eval n) G c V N) D' / N ≤
        distAdv (fun r : Fin n → Fin (ℓ.eval n) → Bool =>
            multiCom Com (fun i => padColor n (simColorsW (edgeOf G e₀) π₀ c i)) r)
          (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com (fun i => padColor n (π₀ (c i))) r)
          (fun cv c' => colSimRed Com (ℓ.eval n) G c V N k e₀ π₀ D' cv (w₀, c')) := by
  obtain ⟨k, e₀, π₀, h⟩ := exists_colSimRed_ge Com (ℓ.eval n) G hm c V N hN D'
  haveI : Nonempty (Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) ×
      (Fin n → Fin (ℓ.eval n) → Bool)) × ρ) :=
    ⟨fun _ => (((⟨0, hm⟩, 1), fun _ _ => false), Classical.arbitrary ρ)⟩
  obtain ⟨w₀, hw₀⟩ := CommitmentLemmas.exists_fixCoins
    (fun r : Fin n → Fin (ℓ.eval n) → Bool =>
      multiCom Com (fun i => padColor n (simColorsW (edgeOf G e₀) π₀ c i)) r)
    (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com (fun i => padColor n (π₀ (c i))) r)
    (colSimRed Com (ℓ.eval n) G c V N k e₀ π₀ D')
  exact ⟨k, e₀, π₀, w₀, h.trans hw₀⟩

/-- **With the attempt table fixed only attempt `k` reads the challenge** (Claim-129.d): the
fixed reduction is `cv ↦ D'(pre <|> planted cv <|> post)`, where `pre` and `post` are the first
successes among the `S''` attempts before `k` and the `S'` attempts after `k`.

**Proof sketch.** Split the search of `colSimRed` at `k` (`List.finRange N` as the indices
before `k`, then `k`, then those after it, `CommitmentLemmas.ofFn_eq_append_cons`); on each part
the case split of `colSimRed` selects the `S''`, planted or `S'` attempt. -/
theorem colSimRed_fixed_eq {n : ℕ} (G : Graph n) (c : Fin n → Fin 3) {ρ : Type*}
    (V : List Bool → ρ → List Bool) (N : ℕ) (k : Fin N) (e₀ : Fin (edgeCount G))
    (π₀ : Equiv.Perm (Fin 3)) {ρ' : Type*} (D' : Option (ColView ρ) → ρ' → Bool) (cv : List Bool)
    (w₀ : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin (ℓ.eval n) → Bool)) × ρ)
    (c' : ρ') :
    colSimRed Com (ℓ.eval n) G c V N k e₀ π₀ D' cv (w₀, c') =
      D' ((firstSome fun t : Fin N => if (t : ℕ) < k then colSimAttemptH Com (ℓ.eval n) G c V (w₀ t) else none) <|>
          colSimAttemptPlanted Com (ℓ.eval n) G c V e₀ π₀ cv (w₀ k) <|>
          (firstSome fun t : Fin N => if k < t then colSimAttemptW Com (ℓ.eval n) G c V (w₀ t) else none)) c' := by
  unfold colSimRed firstSome
  dsimp only
  rw [ColZK.findSome?_finRange_split_lt _ k, if_neg (lt_irrefl (k : ℕ)), if_pos rfl]
  have h1 : (fun t : Fin N => if (t : ℕ) < k then
      (if (t : ℕ) < k then colSimAttemptH Com (ℓ.eval n) G c V (w₀ t)
        else if t = k then colSimAttemptPlanted Com (ℓ.eval n) G c V e₀ π₀ cv (w₀ t)
        else colSimAttemptW Com (ℓ.eval n) G c V (w₀ t)) else none) =
      fun t : Fin N => if (t : ℕ) < k then colSimAttemptH Com (ℓ.eval n) G c V (w₀ t) else none := by
    funext t
    by_cases ht : (t : ℕ) < k
    · rw [if_pos ht, if_pos ht, if_pos ht]
    · rw [if_neg ht, if_neg ht]
  have h2 : (fun t : Fin N => if k < t then
      (if (t : ℕ) < k then colSimAttemptH Com (ℓ.eval n) G c V (w₀ t)
        else if t = k then colSimAttemptPlanted Com (ℓ.eval n) G c V e₀ π₀ cv (w₀ t)
        else colSimAttemptW Com (ℓ.eval n) G c V (w₀ t)) else none) =
      fun t : Fin N => if k < t then colSimAttemptW Com (ℓ.eval n) G c V (w₀ t) else none := by
    funext t
    by_cases ht : k < t
    · rw [if_pos ht, if_pos ht, if_neg (by rw [Fin.lt_def] at ht; omega), if_neg (ne_of_gt ht)]
    · rw [if_neg ht, if_neg ht]
  rw [h1, h2]
/-- **The real view is `(1/4)^{|x|}`-close to the typed honest view** [PS10, proof of
Proposition 128.8, "the view of `V*`"] (step (1) of `col_zk`'s sketch): the encoded view of `V'`
in `P(encGraph G, encColoring c) ↔ V'(·, z)` is within `(1/4)^{|x|}` of the encoded
`colRealView` with a uniform colour permutation, uniform commitment randomness and a uniform
tape of `V'`.

**Proof sketch.** The prover's tape of `3|x| + |x| ℓ(|x|)` bits (`Strategy.coinLen_eq`,
`colProver_coins`) carries the permutation trials in its first `3|x|` bits and the commitment
randomness `r_i j` at `3|x| + i ℓ(n) + j` (inside the tape: `n ≤ n² = |x|`,
`PolyExpr.eval_mono`); these fields are independent and uniform
(`ColZK.pushesUniform_offsetTable`, `StatClose.comp_pushesUniform`), the permutation sampler is
`(1/4)^{|x|}`-close to uniform (`statClose_samplePerm3`), and `V'`'s tape is carried by
`withV_vCoinsEquiv` (`StatClose.prod`, `StatClose.map`). The three moves unfold by
`Protocol.viewV_withV`, `exec_succ` and the public `colProver` equations (`decGraph_encGraph`,
`decColoring_encColoring`, `ColMachines.edgeAt_eq_some_of_pos`) to the encoded
`colRealView`. -/
theorem statClose_colRealView (V' : Strategy) {n : ℕ} (G : Graph n) (c : Fin n → Fin 3)
    (_hc : ProperColoring G c) (z : List Bool) :
    StatClose (fun r => (((colProtocol Com ℓ).withV V').viewV (encGraph G) (encColoring c) z r).encode)
      (fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin (ℓ.eval n) → Bool)) × V'.Coins (encGraph G).length =>
        (some (colRealView Com (ℓ.eval n) G c
            (fun com ρ => V'.next (encGraph G) z (List.ofFn ρ) [com]) w)).elim []
          fun v => View.encode ⟨encGraph G, z, List.ofFn v.1, [v.2.1, v.2.2]⟩)
      ((1 / 4 : ℝ) ^ (encGraph G).length) := by
  set N := (encGraph G).length with hN
  set Ψ := fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin (ℓ.eval n) → Bool)) × V'.Coins N =>
    (some (colRealView Com (ℓ.eval n) G c
      (fun com ρ => V'.next (encGraph G) z (List.ofFn ρ) [com]) w)).elim []
        fun v => View.encode ⟨encGraph G, z, List.ofFn v.1, [v.2.1, v.2.2]⟩ with hΨ
  have hNn : N = n * n := length_encGraph G
  have hnN : n ≤ N := hNn ▸ Nat.le_mul_self n
  have hL : ((colProtocol Com ℓ).withV V').P.coinLen N = 3 * N + N * ℓ.eval N := by
    rw [Protocol.withV_P, colProtocol_P, Strategy.coinLen_eq, colProver_coins, PolyExpr.eval_add,
      PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, PolyExpr.eval_mul, PolyExpr.eval_var]
  have hsz : N * 3 + n * ℓ.eval n ≤ ((colProtocol Com ℓ).withV V').P.coinLen N := by
    rw [hL]
    have := Nat.mul_le_mul hnN (PolyExpr.eval_mono ℓ hnN)
    omega
  have hF := ColZK.pushesUniform_offsetTable hsz
  have h1 := ((statClose_samplePerm3 N).prod
    (StatClose.refl (fun r : Fin n → Fin (ℓ.eval n) → Bool => r))).comp_pushesUniform hF
  have h2 : StatClose (fun r : ((colProtocol Com ℓ).withV V').V.Coins N =>
      (colProtocol Com ℓ).withV_vCoinsEquiv V' N r) id 0 :=
    statClose_of_pushesUniform (HardcoreBit.pushesUniform_equiv _)
  have h := (h1.prod h2).map Ψ
  rw [add_zero, add_zero] at h
  convert h using 1
  funext r
  obtain ⟨rP, rV⟩ := r
  rw [Protocol.viewV_withV, colProtocol_P, colProtocol_verifierFirst, colProtocol_rounds,
    PolyExpr.eval_const]
  simp only [exec_succ, exec_zero, moverIsV_false, Nat.reduceMod, decide_eq_true_eq,
    zero_ne_one, ↓reduceIte, List.nil_append, List.cons_append]
  have hπ : samplePerm3 N ((List.ofFn rP).take (3 * N)) =
      samplePerm3 N (List.ofFn fun i : Fin (N * 3) => rP (Fin.castLE (le_trans (Nat.le_add_right _ _) hsz) i)) := by
    rw [Nat.mul_comm 3 N, OneWay.ofFn_castLE_eq_take]
  have hr : (fun (i : Fin n) (j : Fin (ℓ.eval n)) =>
      (List.ofFn rP).getD (3 * N + i * ℓ.eval n + j) false) =
      fun (i : Fin n) (j : Fin (ℓ.eval n)) => rP ⟨N * 3 + (i * ℓ.eval n + j), lt_of_lt_of_le
        (by have := ColZK.table_index_lt i j; omega) hsz⟩ := by
    funext i j
    have hlt : 3 * N + i * ℓ.eval n + j < ((colProtocol Com ℓ).withV V').P.coinLen N := by
      have := ColZK.table_index_lt i j
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt, Option.getD_some]
    congr 1
    exact Fin.ext (by simp only; ring)
  rw [colProver_next_nil Com ℓ (decGraph_encGraph G), decColoring_encColoring, hπ, hr, hΨ]
  simp only [Option.elim_some]
  unfold colRealView
  simp only [Protocol.withV_vCoinsEquiv_ofFn]
  rcases Nat.eq_zero_or_pos (edgeCount G) with hm | hm
  · rw [colProver_next_cons_of_edgeCount_eq_zero Com ℓ (decGraph_encGraph G) hm,
      (edgeAt_eq_none_iff G _).2 hm]
  · rw [colProver_next_cons Com ℓ (decGraph_encGraph G) hm, decColoring_encColoring, hπ, hr,
      ColMachines.edgeAt_eq_some_of_pos G hm]
end ColZKLadder

/-! ### The string simulator [PS10, Algorithm 128.7] (Alg-128.7, Claim-128.a) -/

/-- The coin block of one attempt of the string simulator against `V'` at instance length
`N`: `(N+1)²` bits for the edge sampler, `3N` bits for the colour-pair sampler, `N ℓ(N)` bits
of commitment randomness and the tape of `V'`. -/
def colSimBlock (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .add (.add (.add (.normal 1 2) (.mul (.const 3) .var)) (.mul .var ℓ)) V'.coins

/-- The coin polynomial of the string simulator: `N²` blocks (at most `n|E| ≤ N²` attempts
are made). -/
def colSimCoins (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .mul (.mul .var .var) (colSimBlock ℓ V')

/-- The six distinct colour pairs enumerated by `Fin 6`. -/
noncomputable def pair6Equiv : Fin 6 ≃ ColorPair := (Fintype.equivFinOfCardEq card_colorPair).symm

/-- The simulator's distinct colour pair from `3T` tape bits: `T` rejection trials of three
bits, the pair `(0, 1)` on failure (D10). -/
noncomputable def sampleColorPair (T : ℕ) (r : List Bool) : ColorPair :=
  ((sampleIdx 6 3 T r).map pair6Equiv).getD ⟨(0, 1), by decide⟩

/-- One attempt of the string simulator [PS10, Algorithm 128.7, steps 1–4] on `(x, z)` with
the coin block `blk`: sample `e'` and the colour pair, commit to `simColors (edgeAt G e') (a, b)`
with the randomness read from the block, run `V'` on `[com]` with the rest of the block as its
tape, and output the encoded view `⟨⟨x, z⟩, ⟨r_{V'}, [com, opening]⟩⟩` if `V'` names `e'`;
if `E = ∅`, commit to all-zero colours and output the view with the empty opening. -/
noncomputable def colSimAttemptStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : Option (List Bool) :=
  let n := (decGraph x).1
  let G : Graph n := (decGraph x).2
  let m := edgeCount G
  let N := x.length
  let e' := sampleEdgeIdx m N blk
  let ab := sampleColorPair N (blk.drop ((N + 1) ^ 2))
  let rr : Fin n → Fin (ℓ.eval n) → Bool :=
    fun i j => blk.getD ((N + 1) ^ 2 + 3 * N + i * ℓ.eval n + j) false
  let rV := blk.drop ((N + 1) ^ 2 + 3 * N + N * ℓ.eval N)
  match edgeAt G e' with
  | none => some (View.encode ⟨x, z, rV, [colCommit Com n (ℓ.eval n) (fun _ => 0) rr, []]⟩)
  | some p =>
    let c' := simColors p ab
    let com := colCommit Com n (ℓ.eval n) c' rr
    if edgeIdxOfMsg m (V'.next x z rV [com]) = e' then
      some (View.encode ⟨x, z, rV, [com, colOpen c' rr p]⟩)
    else none

/-- The string simulator [PS10, Algorithm 128.7] (Alg-128.7): up to `n|E|` attempts
(`colIterations x`, with `|E| = edgeCount G` counting ordered edge pairs; run-3 audit P11-3) on
the consecutive coin blocks of the tape `r`, the first successful attempt's view, or `⊥ = []`
after `n|E|` failures; a single attempt if `E = ∅`.

As in [PS10, Algorithm 128.7, steps 4–5], at most `n|E|` attempts, then `fail` (`⊥ = []`).
**Deviation (D10):** `e'` and the colour pair are rejection-sampled from the tape (defaults `0`
and `(0, 1)`). -/
noncomputable def colSim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z r : List Bool) : List Bool :=
  let B := (colSimBlock ℓ V').eval x.length
  let att : ℕ → Option (List Bool) := fun t => colSimAttemptStr Com ℓ V' x z (colCoinSlice B t r)
  if edgeCount (decGraph x).2 = 0 then (att 0).getD []
  else ((List.range (colIterations x)).findSome? att).getD []

/-- **The simulator is a uniform PPT** [PS10, p. 128, "by construction it directly follows that
`S` is a p.p.t."] (Claim-128.a): for a polynomial-time `Com` and an efficient `V'` there is a
uniform `NUPPT` with coin polynomial `colSimCoins ℓ V'` whose activation on `⟨x, z⟩` at
parameter `|x|` is `colSim Com ℓ V' x z r`.

**Proof sketch.** `V'.Efficient` gives a uniform machine `A` with
`V'.next x z rV [com] = A.runAtL |x| ⟨⟨x, z⟩, encodeMsgs [com]⟩ rV` (`Strategy.ofNUPPT_next`),
polynomial-time by `A.polyTimeComputable_output` and the pairing calculus. One attempt on the
raw layout is polynomial-time: the block is cut by `polyTimeComputable_pairTakePoly`/
`pairDropPoly` with the unary block length (`polyTimeComputable_unaryPoly`); the two samplers
by `polyTimeComputable_iterateFind` over the trials; the `n` commitments by
`polyTimeComputable_blockMap ℓ` composed with `hCom` and `polyTimeComputable_iterateEmit`
for the `encodeMsgs` fold (the colour at position `i` by `polyTimeComputable_ite` on the
comparison with the two endpoints); the comparison of `V'`'s reply with `e'` by
`polyTimeComputable_lenLe`-based modular arithmetic in unary; the view by
`PolyTimeComputable.pairEncode`. The loop over `t < n|E|` is
`Complexity.polyTimeComputable_iterateFind` with the attempt index in the state and the
accepting test "the attempt succeeded" (`R := mul var var`, `P :=` the layout length), the
`E = ∅` case by `polyTimeComputable_ite`; the result is packaged by `NUPPT.ofPolyTimeUniform`
with coins `colSimCoins ℓ V'` (`NUPPT.runAtL_ofPolyTimeUniform`,
`NUPPT.ofPolyTimeUniform_uniform`). -/
theorem exists_colSimulator {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) (V' : Strategy) (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = colSimCoins ℓ V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = colSim Com ℓ V' x z (List.ofFn r) := by
  obtain ⟨S, hS, hc, hsim⟩ := ColSimMachine.exists_simulator hCom ℓ hV'
  exact ⟨S, hS, hc, fun x z r => (hsim x z r).trans rfl⟩

/-! ### Proposition 128.8 -/

/-- A negligible function of `√N` is negligible in `N` (the bookkeeping converting the
commitment's hiding error `ε(n)` at the vertex count `n = √|x|` into a function of `|x|`,
Inf-4.4).

**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)`, `K := max (n₀, 4^c, 1)` and `N ≥ K²`:
`n := Nat.sqrt N ≥ K` (`Nat.le_sqrt`), so `n ≥ n₀`, `n ≥ 4^c`, `n ≥ 1`, and
`N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`); hence `N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` and
`|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
theorem Negligible.comp_sqrt {μ : ℕ → ℝ} (hμ : Negligible μ) :
    Negligible fun N => μ (Nat.sqrt N) := by
  intro c
  obtain ⟨n₀, hn₀⟩ := hμ (2 * c + 1)
  set K := max (max n₀ (4 ^ c)) 1 with hK
  refine ⟨K * K, fun N hN => ?_⟩
  set n := Nat.sqrt N with hn
  have hKn : K ≤ n := Nat.le_sqrt.2 hN
  have hn₀n : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hKn
  have h4n : 4 ^ c ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hKn
  have h1n : 1 ≤ n := le_trans (le_max_right _ _) hKn
  have hNlt : N < (n + 1) * (n + 1) := Nat.lt_succ_sqrt N
  have hN2 : N ≤ 4 * (n * n) := by nlinarith
  have hNr : (N : ℝ) ≤ 4 * ((n : ℝ) * n) := by exact_mod_cast hN2
  have hμn : |μ n| < 1 / (n : ℝ) ^ (2 * c + 1) := hn₀ n hn₀n
  show |μ n| < 1 / (N : ℝ) ^ c
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h1n
  have h4r : (4 : ℝ) ^ c ≤ n := by exact_mod_cast h4n
  have hNc : (N : ℝ) ^ c ≤ (n : ℝ) ^ (2 * c + 1) := by
    calc (N : ℝ) ^ c ≤ (4 * ((n : ℝ) * n)) ^ c := pow_le_pow_left₀ (Nat.cast_nonneg N) hNr c
      _ = 4 ^ c * (n : ℝ) ^ (2 * c) := by rw [_root_.mul_pow, pow_mul, sq]
      _ ≤ n * (n : ℝ) ^ (2 * c) := by gcongr
      _ = (n : ℝ) ^ (2 * c + 1) := by ring
  have hN1 : 1 ≤ N := by
    have hK1 : 1 ≤ K := le_max_right _ _
    have := Nat.mul_le_mul hK1 hK1
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  exact hμn.trans_le (one_div_le_one_div_of_le hNpos hNc)

/-- **One iteration of [PS10, Protocol 127.5] is zero-knowledge for `R_3COL`** [PS10,
Proposition 128.8 and Proposition 127.6, zero-knowledge half] (Prop-128.8, Prop-127.6 (b)):
for a commitment scheme `(Com, ℓ)`, for every efficient verifier `V'` there is a uniform PPT
simulator `S` such that for every auxiliary-input bound `Lz` and every non-uniform PPT `D`
there is a negligible `ε` with, for all `x`, witnesses `y` and `z` with `|z| ≤ Lz(|x|)`, the
advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
`ε(|x|)`.

**Deviation (D8, D10):** strict PPT simulator (D8's definition of `ZK`), rejection-sampled
`π`, `e'` and colour pairs; the error bound is in `|x|` (the text's `e(n)` with `n`
undefined); one iteration (the `n|E|`-fold protocol's zero-knowledge is sequential
composition, [PS10, §7.2.1], out of scope).

**Proof sketch.** Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy`, and fix `Lz`
and `D`. For `x = encGraph G`, `y = encColoring c` with `c` proper and `|z| ≤ Lz |x|`, let `n` be
the vertex count, `m = |E|`, `K = n m ≤ n³`, and `D'` the distinguisher `D.distinguisherL |x|`
on the encoded optional view (`⊥ ↦ []`).

(1) The real view, with `π = samplePerm3 |x| …`, is within `(1/4)^{|x|}` of the view with a
uniform `π`: `statClose_samplePerm3`, `StatClose.prod`/`StatClose.refl` for the prover's
randomness and `V'`'s tape, and `StatClose.map`. `exec_succ` three times, `decGraph_encGraph`,
`decColoring_encColoring`, and `colProver` with `V com r_V := V'.next x z r_V [com]` unfold it to
`some ∘ colRealView`.

If `m > 0`:
(2) `colSim` is within `K((1/2)^{|x|} + (1/4)^{|x|})` of `colSimTrunc … K`, with uniform
`(e'_t, (a_t, b_t))` read from disjoint fields of the `t`-th block (`statClose_sampleEdgeIdx`,
`statClose_sampleColorPair` — the colour-pair analogue of `statClose_samplePerm3`, still to be
added: the fill ladder's first step, gate 03g review M3 — and `StatClose.prod` over the blocks).
(3) `uprob_colSimTruncW_eq`.
(4) `exists_colSimRed_ge` with `N := K` gives `k, e₀, π₀` with
`distAdv truncW truncH D' ≤ K · distAdv X Y (colSimRed … k e₀ π₀ D')`.
`CommitmentLemmas.exists_fixCoins` fixes the reduction's attempt table `w₀` without loss.
With `w₀` fixed, only attempt `k` reads the challenge `cv`, so the fixed reduction is
`cv ↦ D'(pre <|> planted cv <|> post)` for two constant optional views.
(5) `statClose_colSimTruncH` and `one_sub_inv_pow_mul_le_exp` give
`distAdv truncH (some ∘ colRealView) D' ≤ e^{−n}`.

If `m = 0` and `n ≥ 1`, the two views differ only in the commitment vector (`π ∘ c` against
`0`). For each fixed `π`, `D`'s advantage is the hiding gap of
`cv ↦ D(encode ⟨x, z, r_V, [cv, []]⟩)`, with `r_V` fixed by `exists_fixCoins`. Average over `π`.
If `n = 0`, bound the advantage by `1`: the simulator's tape is empty, so its `r_V = []` differs
from the real tape when `V'.coinLen 0 > 0`.

The machine `B` at parameter `n`: among the finitely many data at vertex count `n` (finite
because `|z| ≤ Lz(n²)`: this is where the bound `Lz` is used, see the `Defs.lean` module
docstring), take those whose fixed reduction (either case) has the largest gap on its own
vectors. Hard-wire `x`, `z`, the case, `ρ_k`, `e₀`, the two endpoint commitments and openings,
`pre`, `post` and `D.advice (n²)` as advice (`NUPPT.exists_withAdvice`; polynomially bounded by
`hC.easy.output_length_le` and `colProtocol_proverBounded`). Call `V'`'s uniform machine once
(`Strategy.Efficient`) and `D` at parameter `n²` on `B`'s coins (`NUPPT.exists_reparam_advice`,
`φ n = n²`). Its acceptance probabilities on `multiCom` samples are the fixed reduction's (coin
transport along `finCongr`). `hC.multiHiding var B` gives a negligible `ε_B ≥ 0` (it bounds a
`distAdv` at every `n`), so the hiding terms are at most
`K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`.

Put `ε N := N² ε_B (Nat.sqrt N) + exp (−Nat.sqrt N) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`. It is
negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div`
(`C = 1`), `negligible_two_pow_neg` and `Negligible.add`. At `N = 0` its exponential term is
`1`. Use the triangle inequality for `distAdv` (`abs_sub_le`), and `Nat.sqrt |x| = n`
(`length_encGraph`, `Nat.sqrt_eq`). -/
theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
    ZK (colProtocol Com ℓ) R3COL := by
  sorry

/-- One iteration of [PS10, Protocol 127.5] is honest-verifier zero-knowledge for `R_3COL`
[PS10, Proposition 128.8 with the honest verifier] (`ZK.hvzk`, `colVerifier_efficient`). -/
theorem col_hvzk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
    HVZK (colProtocol Com ℓ) R3COL :=
  (col_zk hC).hvzk (colVerifier_efficient hC.easy ℓ)

/-- **[PS10, Proposition 127.6]: Protocol 127.5 is a zero-knowledge proof for `3COL`**
(Prop-127.6), assembled from its parts: one iteration is an interactive proof with efficient
prover and soundness error `1 - 1/|x| + (1/2)^{|x|}` (`col_efficientProverProofErr`) and is
zero-knowledge (`col_zk`), and the `n|E|`-fold repetition is an interactive proof with
efficient prover and negligible soundness error (`colRep_efficientProverProof`).

**Deviation (DQ5):** the zero-knowledge of the repeated protocol is sequential composition
[PS10, §7.2.1], outside Chapters 2–4, and is not claimed. -/
theorem col_zeroKnowledgeProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) :
    EfficientProverProofErr (colProtocol Com ℓ) L3COL R3COL
        (fun N => 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) ∧
      ZK (colProtocol Com ℓ) R3COL ∧
      EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL :=
  ⟨col_efficientProverProofErr hC, col_zk hC, colRep_efficientProverProof hC⟩

end TCSlib.Cryptography
