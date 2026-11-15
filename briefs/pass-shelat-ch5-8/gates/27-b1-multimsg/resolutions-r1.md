# Gate 27 · resolutions, round 1 · IN PROGRESS

Codex's verdict is **CLEAR for the statement gate**: 0 blockers, 0 majors, 1 minor and 0 notes.
- **Findings:** `findings/gate27-b1-multimsg-findings.md`.
- **Audited head:** `46b780dc1b286f59da18e2d10f188b0faaab8088`.

| # | Severity | Disposition |
|---|---|---|
| G27-01 | minor | **To fix by a docstring-only resolution edit, LE-gate27.** The docstring of `sliceMultiMessageSecure_of_prfOut` says "Both fit exactly". It will read: "Both shapes fit; the outer slice fits exactly." The edit is rebuilt before #311 is marked ready. |

## What Codex verified
Codex ran no Lean.

- **Truth of the statement.** It gave a full mathematical proof of the statement as written, including the
  quantifier order (slices chosen after `ε`, which is valid because `L = ℓ.eval` is polynomial). One convention is
  needed: the maximum advantage is 0 when no slice vector fits.
- **Sufficiency for Yao step 3.** It confirmed both slice shapes, `(0,n)` and `(2n,4n+2)`, and that the
  non-adaptive interface is enough, using `g.args.Nodup`.
- **The frozen corollary.** It confirmed the corollary.
- **Readers and bridges.** The readers and bridges are Rule-10 clean.
- **Duplication.** It found none.

## Hand-off to the proof jobs (Codex; obligations, not findings)

1. **prf-long.** Answer lengths must be `ℓ`-bit while queries, keys and nonces stay `n`-bit. The job must publish
   a query-tree evaluation identity for arbitrary oracles, together with its coin equivalence and its advice and
   query bounds. The consumer must be able to post-process the full answer transcript in polynomial time.
   - *Maintainer check against the issued prf-long brief (D1–D4):* D3's `exists_queryChainOut_nuppt` evaluates
     `D` on the flattened transcript `⟨⟨ρ_j, v_j ⊕ g(ρ_j)⟩⟩` for arbitrary `D`. The consumer's slice
     post-processor `P` is folded into `D' = D ∘ P` with the slices as advice, as the brief's B1 map records. This
     is an "equivalent sufficiently general API" in Codex's sense.
   - It will be re-checked at the prf-long review.
2. **Reuse.** These existing generic readers can be reused: `OracleEnsemble.keyed_O`, `random_O`,
   `acceptProb_random_eq`, `MultiMsg.chainTree`, `uprob_not_injective_le`, `pushesUniform_comp_injective` and
   `negligible_choose_div_two_pow`.
3. **sc-garble.** It must:
   - build the maximizing advice, with the empty-set convention;
   - build the slice post-processor;
   - prove the random-function slice law;
   - close the triangle bound;
   - prove the frozen theorem via the corollary;
   - meet the B2 requirement.

   These go into the `sc-garble` brief.
4. **sc-yao.** It must formalize the gate and row sub-hybrids, the enumeration of all occurrences with padding, the
   no-dependence argument, the sampler identities, and polynomial-time reconstruction. These go into the `sc-yao`
   brief.
