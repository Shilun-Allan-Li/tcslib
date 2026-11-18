# Stretch final overlap goals — UNRUN

Five goal-only templates cover existing Params.seedBitsAt_le and jls_hasPolyStretch,
and proposed Internal.w_lower, stretch_gaps, eventually_seed_relative_gap.
`mapping.tsv` identifies source/header and preferred corrected candidate.
The materializer is byte-identical to the earlier overlap materializer; it was not run.
Root may materialize one named exact? or apply? test at a time, then compile serially.

Every numerical field is expanded through the current reader equations: D=(d+1)/2,
ell=kappa^E, n=ell^D, m=outLen n, w=max1 floor(ell^(delta/2)), W=w^2,
B=max1((m*kappa+W-1)/W), rc=kappa*w, exact tensor/factor count, and the actual
public/private bit count. The final goal expands both HasPolyStretch conjuncts.
No result about that count or helper conclusion is assumed. Primitive outLen,
pointwise input stretch and the supplied PolyExpr output bound remain arbitrary
scalar data; irrelevant sampler, index, machine, polynomial-representation and
prime-schedule data disappear. This abstraction removes hypotheses, never adds
an invented positivity/monotonicity/rounding assumption. The two new exponent
premises in helper05 are exactly its current proposed header premises.

Current-source import closure excludes every Obfuscation module, so neither the
original nor proposed owned constants can self-match. Core toolchain modules are
terminal; no compilation/cache step was used. `static-checks.json` records only
text facts. Name/shape/public reuse details are in name-shape-searches.log.

Preferred coefficient retention is preserved. No old02/06 goal/body, generic
monic-normalization helper, new import, implementation edit, Lean, git, cache or
agent spawn. Exact?/apply?, elaboration and kernel results remain root's work.
