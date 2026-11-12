/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
/- DLC-SEAL Encryption_PrivateKey_OracleFromPRF_Games: whole-file closure seal of `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Games.lean`. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL Encryption_PrivateKey_OracleFromPRF_Games: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The CPA and CCA1 games of the §3.9 scheme with an arbitrary pad function

The scheme of [PS10, Algorithm 99.1] encrypts `m` as `⟨r, m ⊕ f(r)⟩` with a fresh `n`-bit `r`,
where `f = f_k` is the keyed function. The proof of [PS10, Theorem 168.2] replaces `f_k` by other
functions; this file states the IND experiment's oracles with `f` an arbitrary function
`{0,1}^n → {0,1}^n`, on bit-string oracles of arbitrary lengths (`bitSpec ins outs`; oracle `0` is
`Enc`, `1` is `Dec`, `2` is `Challenge`), with ciphertexts read at width `d`.

* `fImpl … f` samples a fresh `r` for every encryption and for the first challenge (the
  experiment of Definition 168.1 with `f` in place of `f_k`).
* `eImpl … f T` takes the `j`-th fresh `r` from the tape `T j` given in advance (the run of the
  reduction, whose seed holds the tapes); the state counts the tapes used.

Drawing `κ` tapes uniformly gives the distribution of `fImpl` for every computation with at most
`κ` queries (`expect_eImpl`); the proof resamples one tape at a time
(`AdaptiveCPA.expect_sample_update`), using that the run from the counter `j` ignores the tapes
below `j` (`simulate_eImpl_congr`).

## Main definitions

* `PRFGame.ctOf`: the ciphertext `⟨r, m ⊕ y⟩`.
* `PRFGame.decAns`: the decryption answer `⟨1, v ⊕ f(x)⟩` on a well-formed `⟨x, v⟩`, else `⊥`.
* `PRFGame.fImpl`, `PRFGame.eImpl`: the oracles with fresh and with given nonces.

## Main results

* `PRFGame.fImpl_enc`, `_dec`, `_challenge_none`, `_challenge_some` and the same for `eImpl`.
* `PRFGame.simulate_eImpl_congr`: the run from counter `j` ignores the tapes below `j`.
* `PRFGame.expect_eImpl`: tapes in advance have the distribution of fresh nonces.
* `PRFGame.expect_simulate_congr`: implementations with the same laws simulate alike.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1 and Theorem 168.2 (book pp. 99, 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Ciphertexts and decryption answers -/

/-- **The ciphertext** `⟨r, m ⊕ y⟩` of the message list `m` with nonce `r` and pad `y`. -/
def ctOf {n : ℕ} (r : Fin n → Bool) (m : List Bool) (y : Fin n → Bool) : List Bool :=
  pairEncode (List.ofFn r) (List.zipWith xor m (List.ofFn y))

/-- `ctOf r m y = pairEncode ⟦r⟧ (m ⊕ ⟦y⟧)`. -/
theorem ctOf_eq {n : ℕ} (r : Fin n → Bool) (m : List Bool) (y : Fin n → Bool) :
    ctOf r m y = pairEncode (List.ofFn r) (List.zipWith xor m (List.ofFn y)) :=
  rfl

/-- A ciphertext of an `n`-bit message has `3n + 2` bits: `|ctOf r m y| = 3n + 2` when
`|m| = n`. -/
theorem length_ctOf {n : ℕ} (r : Fin n → Bool) {m : List Bool} (hm : m.length = n)
    (y : Fin n → Bool) : (ctOf r m y).length = 3 * n + 2 := by
  rw [ctOf_eq, length_pairEncode, List.length_ofFn, List.length_zipWith, List.length_ofFn, hm,
    Nat.min_self]
  omega

/-- **Well-formedness of a decryption query** `w`: both components of the pair have `n` bits,
`decWF n w = (|pairFstD w| = n && |pairSndD w| = n)`. -/
def decWF (n : ℕ) (w : List Bool) : Bool :=
  decide ((pairFstD w).length = n) && decide ((pairSndD w).length = n)

/-- `decWF n w = (decide (|pairFstD w| = n) && decide (|pairSndD w| = n))`. -/
theorem decWF_eq (n : ℕ) (w : List Bool) :
    decWF n w = (decide ((pairFstD w).length = n) && decide ((pairSndD w).length = n)) :=
  rfl

/-- **The decryption answer** with pad function `f`, when the oracle is open (`op`): on a
well-formed `w = ⟨x, v⟩` it is `true :: (v ⊕ f(x))`, and otherwise the empty list (read as `⊥`,
all-`false`). -/
def decAns (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (op : Bool) (w : List Bool) :
    List Bool :=
  if op && decWF n w then
    true :: List.zipWith xor (pairSndD w) (List.ofFn (f (padFin n (pairFstD w))))
  else []

/-- `decAns n f op w = if op && decWF n w then true :: (pairSndD w ⊕ ⟦f (padFin n (pairFstD w))⟧)
else []`. -/
theorem decAns_eq (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (op : Bool) (w : List Bool) :
    decAns n f op w =
      if op && decWF n w then
        true :: List.zipWith xor (pairSndD w) (List.ofFn (f (padFin n (pairFstD w))))
      else [] :=
  rfl

/-! ### Simulation congruence -/

/-- **Implementations with the same laws simulate alike:** if every call of `impl₀` and `impl₁`
has the same expectation of every function `g` of the answer and the new state, the simulations
of every computation have the same expectation of every function `G` of the output and the final
state: `𝔼[G] (simulate impl₀ c s) = 𝔼[G] (simulate impl₁ c s)`.

**Proof sketch.** Induction on `c`; at a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`), equal by induction and the
hypothesis. -/
theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h]
    exact congrArg _ (funext fun p => ih p.1 p.2)

/-! ### The oracles with fresh nonces -/

section Oracles

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack) (b : Bool)
  (f : (Fin n → Bool) → (Fin n → Bool))

/-- **The oracles of `IND_b` with pad function `f`** and fresh nonces: `Enc` on `m` samples `r` and
answers `⟨r, m ⊕ f(r)⟩`; `Dec` answers `decAns` when `decOpen atk` lets it; `Challenge` on
`⟨m₀, m₁⟩` the first time samples `r`, answers `c = ⟨r, m_b ⊕ f(r)⟩` and records it, and later
repeats `c`. Lengths are adjusted with `padFin`; the state is the recorded challenge. These are the
oracles of `IND_b` under CPA and CCA1 (`expect_indImpl_fImpl`); under CCA2 `Dec` here does not
refuse the challenge ciphertext. -/
noncomputable def fImpl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec
  | 0, m, s => (ProbComp.sample (Fin n → Bool)).bind fun r =>
      .pure (padFin _ (ctOf r (List.ofFn m) (f r)), s)
  | 1, c, s => .pure (padFin _ (decAns n f (FixedLengthScheme.decOpen atk s.isSome)
      (List.ofFn c)), s)
  | 2, mm, s =>
    match s with
    | some c => .pure (padFin _ (List.ofFn c), some c)
    | none => (ProbComp.sample (Fin n → Bool)).bind fun r =>
        .pure (padFin _ (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f r)),
          some (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f r))))

/-- An encryption query samples a nonce `r` and answers `⟨r, m ⊕ f(r)⟩`. -/
theorem fImpl_enc (m : Fin (ins 0) → Bool) (s : Option (Fin d → Bool)) :
    fImpl ins outs d n atk b f 0 m s = (ProbComp.sample (Fin n → Bool)).bind fun r =>
      .pure (padFin _ (ctOf r (List.ofFn m) (f r)), s) :=
  rfl

/-- A decryption query is answered by `decAns`, open as `decOpen atk` says, and keeps the state. -/
theorem fImpl_dec (c : Fin (ins 1) → Bool) (s : Option (Fin d → Bool)) :
    fImpl ins outs d n atk b f 1 c s =
      .pure (padFin _ (decAns n f (FixedLengthScheme.decOpen atk s.isSome) (List.ofFn c)), s) :=
  rfl

/-- The first challenge `mm` samples `r`, answers `c = ⟨r, m_b ⊕ f(r)⟩` and records it. -/
theorem fImpl_challenge_none (mm : Fin (ins 2) → Bool) :
    fImpl ins outs d n atk b f 2 mm none = (ProbComp.sample (Fin n → Bool)).bind fun r =>
      .pure (padFin _ (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f r)),
        some (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f r)))) :=
  rfl

/-- A later challenge repeats the recorded ciphertext `c`. -/
theorem fImpl_challenge_some (mm : Fin (ins 2) → Bool) (c : Fin d → Bool) :
    fImpl ins outs d n atk b f 2 mm (some c) = .pure (padFin _ (List.ofFn c), some c) :=
  rfl

/-! ### The oracles with nonces given in advance -/

/-- **The oracles of `IND_b` with pad function `f` and the nonces `T` in advance:** as `fImpl`, but
the `j`-th fresh nonce (an encryption or the first challenge) is `T j`; the state is the counter
`j` and the recorded challenge. All answers are deterministic. -/
noncomputable def eImpl (T : ℕ → Fin n → Bool) :
    QueryImpl (bitSpec ins outs) (ℕ × Option (Fin d → Bool)) unifSpec
  | 0, m, s => .pure (padFin _ (ctOf (T s.1) (List.ofFn m) (f (T s.1))), (s.1 + 1, s.2))
  | 1, c, s => .pure (padFin _ (decAns n f (FixedLengthScheme.decOpen atk s.2.isSome)
      (List.ofFn c)), s)
  | 2, mm, s =>
    match s.2 with
    | some c => .pure (padFin _ (List.ofFn c), s)
    | none => .pure (padFin _ (ctOf (T s.1) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f (T s.1))),
        (s.1 + 1, some (padFin d (ctOf (T s.1) (AdaptiveCPA.msgOf n b (List.ofFn mm))
          (f (T s.1))))))

variable (T : ℕ → Fin n → Bool)

/-- An encryption query uses the nonce `T j` and advances the counter `j`. -/
theorem eImpl_enc (m : Fin (ins 0) → Bool) (j : ℕ) (s : Option (Fin d → Bool)) :
    eImpl ins outs d n atk b f T 0 m (j, s) =
      .pure (padFin _ (ctOf (T j) (List.ofFn m) (f (T j))), (j + 1, s)) :=
  rfl

/-- A decryption query is answered by `decAns` and keeps the state. -/
theorem eImpl_dec (c : Fin (ins 1) → Bool) (j : ℕ) (s : Option (Fin d → Bool)) :
    eImpl ins outs d n atk b f T 1 c (j, s) =
      .pure (padFin _ (decAns n f (FixedLengthScheme.decOpen atk s.isSome) (List.ofFn c)),
        (j, s)) :=
  rfl

/-- The first challenge uses the nonce `T j`, records the ciphertext and advances the counter. -/
theorem eImpl_challenge_none (mm : Fin (ins 2) → Bool) (j : ℕ) :
    eImpl ins outs d n atk b f T 2 mm (j, none) =
      .pure (padFin _ (ctOf (T j) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f (T j))),
        (j + 1, some (padFin d (ctOf (T j) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f (T j)))))) :=
  rfl

/-- A later challenge repeats the recorded ciphertext and keeps the state. -/
theorem eImpl_challenge_some (mm : Fin (ins 2) → Bool) (j : ℕ) (c : Fin d → Bool) :
    eImpl ins outs d n atk b f T 2 mm (j, some c) = .pure (padFin _ (List.ofFn c), (j, some c)) :=
  rfl

/-- **The run from the counter `j` ignores the tapes below `j`:** if `T m = T' m` for every
`m ≥ j`, the runs of `eImpl` with `T` and `T'` from `(j, s)` agree.

**Proof sketch.** Induction on the computation: a fresh nonce at counter `j' ≥ j` reads `T j'`
and moves to `j' + 1`; the other queries keep the counter. -/
theorem simulate_eImpl_congr (T' : ℕ → Fin n → Bool) {α : Type}
    (c : OracleComp (bitSpec ins outs) α) (j : ℕ) (s : Option (Fin d → Bool))
    (hT : ∀ m, j ≤ m → T m = T' m) :
    simulate (eImpl ins outs d n atk b f T) c (j, s) =
      simulate (eImpl ins outs d n atk b f T') c (j, s) := by
  induction c generalizing j s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, simulate_query, eImpl_enc, eImpl_enc, OracleComp.pure_bind,
        OracleComp.pure_bind, hT j le_rfl]
      exact ih _ _ _ fun m hm => hT m (by omega)
    | 1, x, k, ih =>
      rw [simulate_query, simulate_query, eImpl_dec, eImpl_dec, OracleComp.pure_bind,
        OracleComp.pure_bind]
      exact ih _ _ _ hT
    | 2, x, k, ih =>
      cases s with
      | some c =>
        rw [simulate_query, simulate_query, eImpl_challenge_some, eImpl_challenge_some,
          OracleComp.pure_bind, OracleComp.pure_bind]
        exact ih _ _ _ hT
      | none =>
        rw [simulate_query, simulate_query, eImpl_challenge_none, eImpl_challenge_none,
          OracleComp.pure_bind, OracleComp.pure_bind, hT j le_rfl]
        exact ih _ _ _ fun m hm => hT m (by omega)

/-- **Nonces in advance have the distribution of fresh nonces:** for a computation with at most
`m` queries, a counter `j` with `j + m ≤ κ`, and every function `G` of the output,
`𝔼_{T ← ({0,1}^n)^κ} 𝔼[G (simulate (eImpl (extTape T)) c (j, s))] =
𝔼[G (simulate (fImpl) c s)]`.

**Proof sketch.** Induction on `c`, generalizing the counter, the state and the budget. A query
costs one unit, so a fresh nonce is read at a counter `j < κ`. There it reads `T j`, and the
continuation runs from `j + 1`, so it ignores `T j` (`simulate_eImpl_congr`, `extTape_update`);
`AdaptiveCPA.expect_sample_update` replaces `T j` by the fresh sample of `fImpl`. The other
queries are answered alike. -/
theorem expect_eImpl (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (j : ℕ) (hj : j + m ≤ κ)
    (s : Option (Fin d → Bool)) :
    expect (ProbComp.sample (Fin κ → Fin n → Bool))
        (fun T => expect (simulate (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T)) c (j, s))
          (fun p => G p.1)) =
      expect (simulate (fImpl ins outs d n atk b f) c s) (fun p => G p.1) := by
  induction c generalizing m j s with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    have hjk : j < κ := by omega
    have hrest : j + 1 + (m - 1) ≤ κ := by omega
    -- a fresh nonce at counter `j`: resample the tape `j`
    have fresh : ∀ (ans : (Fin n → Bool) → (bitSpec ins outs).rng i)
        (st : (Fin n → Bool) → Option (Fin d → Bool)),
        (∀ r, expect (ProbComp.sample (Fin κ → Fin n → Bool)) (fun T =>
          expect (simulate (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T)) (k (ans r))
            (j + 1, st r)) (fun p => G p.1)) =
          expect (simulate (fImpl ins outs d n atk b f) (k (ans r)) (st r)) (fun p => G p.1)) →
        expect (ProbComp.sample (Fin κ → Fin n → Bool)) (fun T =>
          expect (simulate (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T))
            (k (ans (AdaptiveCPA.extTape T j))) (j + 1, st (AdaptiveCPA.extTape T j)))
              (fun p => G p.1)) =
          expect (ProbComp.sample (Fin n → Bool)) (fun r =>
            expect (simulate (fImpl ins outs d n atk b f) (k (ans r)) (st r))
              (fun p => G p.1)) := by
      intro ans st hih
      let jj : Fin κ := ⟨j, hjk⟩
      have hT : ∀ T : Fin κ → Fin n → Bool, AdaptiveCPA.extTape T j = T jj :=
        fun T => AdaptiveCPA.extTape_of_lt T hjk
      simp only [hT]
      refine (AdaptiveCPA.expect_sample_update jj (fun r T => expect (simulate
        (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T)) (k (ans r)) (j + 1, st r))
          (fun p => G p.1)) ?_).trans ?_
      · intro r r' T
        refine congrArg (fun c => expect c (fun p => G p.1))
          (simulate_eImpl_congr ins outs d n atk b f _ _ _ _ _ fun m' hm' => ?_)
        exact AdaptiveCPA.extTape_update T jj r' (by
          intro h
          have : m' = j := h
          omega)
      · exact congrArg _ (funext hih)
    match i, x, k, ih, hk with
    | 0, x, k, ih, hk =>
      rw [simulate_query, fImpl_enc, OracleComp.bind_assoc, expect_bind]
      simp only [simulate_query, eImpl_enc, OracleComp.pure_bind]
      exact fresh (fun r => padFin _ (ctOf r (List.ofFn x) (f r))) (fun _ => s)
        fun r => ih _ (m - 1) (hk _) (j + 1) hrest s
    | 1, x, k, ih, hk =>
      simp only [simulate_query, eImpl_dec, fImpl_dec, OracleComp.pure_bind]
      exact ih _ (m - 1) (hk _) j (by omega) s
    | 2, x, k, ih, hk =>
      cases s with
      | some c =>
        simp only [simulate_query, eImpl_challenge_some, fImpl_challenge_some,
          OracleComp.pure_bind]
        exact ih _ (m - 1) (hk _) j (by omega) (some c)
      | none =>
        rw [simulate_query, fImpl_challenge_none, OracleComp.bind_assoc, expect_bind]
        simp only [simulate_query, eImpl_challenge_none, OracleComp.pure_bind]
        exact fresh (fun r => padFin _ (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn x)) (f r)))
          (fun r => some (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn x)) (f r))))
          fun r => ih _ (m - 1) (hk _) (j + 1) hrest _

end Oracles

end TCSlib.Cryptography.Composability.PRFGame
