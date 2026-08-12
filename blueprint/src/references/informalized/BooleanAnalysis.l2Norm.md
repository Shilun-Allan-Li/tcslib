<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: l2Norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The L² norm of a Boolean function

**Definition.** For `f : BooleanFunc n`,

```
l2Norm f = Real.sqrt (innerProduct f f)
```

the `L²(uniform)` norm `‖f‖ = √𝔼[f²]`. A plain `noncomputable def` with no
proof content.

**Remark.** Well-behaved by construction rather than by hypothesis: the
radicand is non-negative by `innerProduct_self_nonneg`, so the `Real.sqrt` is
never in its junk branch.

**Used in.** Nothing — no other declaration in the repository references it.
The development consistently works with the *squared* norm instead, either as
`innerProduct f f` (so that `parseval` applies directly) or as `l2DistSq`
in `KKL.lean`, which avoids carrying a square root through the estimates. The
file's module docstring advertises `‖f‖² = ∑_S f̂(S)²` as a main result, and
that result (`parseval`) is stated in terms of `innerProduct`, not `l2Norm`.
