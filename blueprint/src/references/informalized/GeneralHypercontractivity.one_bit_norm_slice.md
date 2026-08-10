<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: one_bit_norm_slice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The one-bit `L^p` norm of a slice

**Claim.** For `p > 0`, `f : BooleanFunc (n + 1)` and `x' : BoolCube n`,
`(expect (fun t : BoolCube 1 => |f (Fin.snoc x' (t 0))| ^ p)) ^ (1/p)`
equals `((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1/p)`.
A bookkeeping lemma: it just evaluates the one-bit expectation of the slice
`t ↦ f (snoc x' (t 0))` as the two-point average of the two values.

**Proof.** Enumeration of `BoolCube 1`.

1. `unfold expect` and `uniformWeight`, `norm_num [Finset.card_univ]; ring_nf`.
2. `rw [show (Finset.univ : Finset (Fin 1 → Bool)) = {fun _ => false, fun _ => true} by decide, Finset.sum_pair]`
   turns the expectation into `(|f (snoc x' false)| ^ p + |f (snoc x' true)| ^ p) / 2`.
3. `decide +revert` discharges the remaining `Fin 1`/`Bool` side goal.

**Remark.** `_hp : 0 < p` is unused. This lemma is currently **dead code** — no
other declaration in the repository references it; the induction step
`two_func_hyp_succ` performs the same slice-norm evaluation inline (in
`h_pointwise`) rather than calling it.
