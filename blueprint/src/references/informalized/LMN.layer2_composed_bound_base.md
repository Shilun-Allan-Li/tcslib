<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CompressionStep.lean :: layer2_composed_bound_base -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Base case of the layer-2 composed bound (inner depth 2)

**Claim.** Let `data : Layer2Data n` package `data.numGates` DNF gates of width
`≤ data.width`, and let `c_top : Circuit data.numGates` be the top circuit, with
`c_top.depth + 2 ≤ 2` (so `c_top` has depth `0`), `c_top.size ≤ s_rem`,
`0 < s_rem`, `data.width ≤ l`, `0 < l`, `0 < n`. Then under a
`composedDelta l l 2`-Bernoulli restriction,

`Pr[ dtDepth (restrictFn (fun x => c_top.eval (fun i => (data.gates i).eval x)) ρ) > t ]`
`≤ s_rem·(1/2)^l + (1/2)^t + s_rem·exp(−n/(120l)) + exp(−n/(120l))`.

Note `composedDelta l (↑l) 2 = 1/(40l)`, the plain switching-lemma rate; the
extra `s_rem·(1/2)^l` and `s_rem·exp(−n/(120l))` terms are slack, carried only so
the statement matches the inductive step's shape.

**Proof.**

1. `circuit_depth_zero_is_lit c_top` (with `by linarith` from `hd_depth`) gives
   `c_top = Circuit.lit l'`, so the composed function is a single gate
   `(data.gates l'.idx).eval`, possibly negated according to `l'.sign`.
2. `have h_switching`: the Bernoulli switching lemma
   `switching_bernoulli_dtDepth_dnf_general` applied to `data.gates l'.idx` with
   width bound `l` (from `data.widthBound` chained through `hwl` by `le_trans`)
   and rate `1/(40l)` bounds `Pr[dtDepth > t] ≤ (1/2)^t + exp(−n/(120l))`. The
   rate-side obligations are `positivity`, `norm_num` and `div_le_iff₀`; the
   tail-exponent shapes are reconciled with `ring_nf`.
3. `by_cases h : l'.sign`, then `simp_all [Circuit.eval]`.
   - Positive-literal branch: after `unfold composedDelta` and `norm_num`, the
     goal follows by `linarith` from step 2 plus nonnegativity of the two slack
     terms `s_rem·(2^l)⁻¹` and `s_rem·exp(−n/(120l))` (`positivity`).
   - Negated branch: chain through `h_switching` on both sides. Negation does not
     change decision-tree depth (`dtDepth_neg`, after `unfold restrictFn`), and
     absorbing the slack uses `nlinarith` with `(s_rem : ℝ) ≥ 1` (from `hs_pos`)
     and nonnegativity of `(2^l)⁻¹` and `exp(−n/(120l))`.

**Note.** Advertised as the `d_inner = 2` base case of `layer2_composed_bound`,
but it has no callers in the library at present.
