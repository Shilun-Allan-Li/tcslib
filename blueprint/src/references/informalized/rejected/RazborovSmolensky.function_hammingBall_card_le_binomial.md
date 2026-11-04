<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: function_hammingBall_card_le_binomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Volume bound for a Hamming ball of functions

**Claim.** Let `α`, `β` be finite with `DecidableEq β`, let `center : α → β` and `e : ℕ`.
The number of `f : α → β` that disagree with `center` on at most `e` points, i.e.
`(univ.filter fun f => (univ.filter fun a => center a ≠ f a).card ≤ e).card`, is at most
`∑ t ∈ range (e + 1), (Fintype.card α).choose t * Fintype.card β ^ t`.

**Proof.** Encode a ball element by its disagreement set together with its values there.
Write `Ball` for the subtype of functions in the ball and
`Enc = Σ t : Fin (e + 1), Σ S : {S : Finset α // S.card = t.1}, ({a // a ∈ S.1} → β)`.

1. `decode : Enc → Ball` sends `⟨t, S, vals⟩` to `g a = if ha : a ∈ S.1 then vals ⟨a, ha⟩ else center a`.
   Membership in the ball holds because the disagreement set of `g` is contained in `S.1`
   (`Finset.mem_filter`, then `Finset.card_le_card`), and `S.card = t.1 ≤ e` by
   `Nat.le_of_lt_succ t.2`.
2. `hdecode_surj`: `decode` is surjective. Given `f` in the ball, take `S0` its actual
   disagreement set, `t = ⟨S0.card, Nat.lt_succ_of_le _⟩` and `vals = f.1` restricted to `S0`;
   `Subtype.ext` + `funext` with `by_cases a ∈ S0` recovers `f` (off `S0`, `f` agrees with
   `center`).
3. `hball_card`: the filtered `Finset` card equals `Fintype.card Ball`, by
   `Fintype.card_subtype`. Hence `Fintype.card Ball ≤ Fintype.card Enc` from
   `Fintype.card_le_of_surjective`.
4. `hEnc_card` computes `Fintype.card Enc` by two `Fintype.card_sigma` steps: for fixed `t`
   each summand is `Fintype.card β ^ Fintype.card {a // a ∈ S.1} = Fintype.card β ^ t.1`
   (`Fintype.card_fun`, `Fintype.card_subtype`, `S.2`), and the number of such `S` is
   `(Fintype.card α).choose t.1` by `Fintype.card_finset_len`, so
   `Finset.sum_const` gives `choose … t.1 * card β ^ t.1`.
5. `hFinRange` converts `∑ t : Fin (e + 1)` into `∑ t ∈ range (e + 1)` via
   `Fin.sum_univ_eq_sum_range`, and a `calc` chains 3–5.

**Remark.** The sharper classical bound uses `(card β - 1) ^ t`; the coarser `card β ^ t`
here is enough for the Smolensky counting step and is stated for arbitrary finite `α`, `β`
(no field structure). Specialized to the root cube in `rootCubeBall_card_le_binomial`.
