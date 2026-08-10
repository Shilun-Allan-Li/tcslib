<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean :: width_le_iff_forall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A folded max of term widths is bounded iff every term is

**Claim.** For a list of terms `ts : List (Term n)` and a bound `l : ℕ`,

`(ts.map Term.width).foldr max 0 ≤ l ↔ ∀ t ∈ ts, t.width ≤ l`.

The left side is literally the definition of `DNF.width ts` (and of
`CNF.width ts`, which is the same function), so this is the "width ≤ l means
every term/clause has ≤ l literals" unfolding lemma. Note the `0` seed makes the
empty list have width `0`, so the empty formula satisfies every bound.

**Proof.** Induction on `ts` (`induction' ts with t ts ih`).

1. Empty list: the fold is `0`, and the right-hand `∀` is vacuous, so both sides
   are `True` — closed by `norm_num +zetaDelta at *`.
2. Cons: the fold is `max t.width ((ts.map Term.width).foldr max 0)`, and
   `max a b ≤ l ↔ a ≤ l ∧ b ≤ l` splits it into the head bound plus the
   inductive hypothesis; membership in `t :: ts` splits the same way. Discharged
   by `grind +splitImp`.

**Note.** This is a `private lemma` and, as of this file, is not referenced
anywhere — including by `cnf_concat_width_le`, which re-derives the same fact
inline via `unfold CNF.width` and `aesop`. It is a leftover helper.
