# Constant-shift normalization for the concrete PKE routes

Internal source-level design, 2026-11-07 PST. Not a Lean theorem, issued gate, or fill brief.
Reviewed source: integration `e9d64158461bfe24ddc88ab885bc4017899b4c16`, with the candidate
sources unchanged from the merged S1 tree. A maintainer subagent inspected the available
APIs; the maintainer checked the collection fields and machine reparameterization contracts.

## A smaller sufficient route

The current GL API needs an exact syntactic-polynomial width, not just an upper bound.
The concrete candidate width schedules have a small-parameter maximum. A fixed shift can
remove that maximum at every new parameter:

| Candidate | Original parameter used at new n | Generated-domain width | Syntactic polynomial |
|---|---|---|---|
| RSA | n+2 | 2 max(n+2,2) = 2(n+2) | mul (const 2) (add var (const 2)) |
| Blum Rabin | n+3 | 2 max(n+3,3) = 2(n+3) | mul (const 2) (add var (const 3)) |

A common shift of 3 would also work. These arithmetic equalities alone do not produce a
formalized normalized collection or transport its hardness. The obstruction remains open
until the missing APIs and proofs below are present. A generalized per-index GL construction
is not necessary for these two schedules, although it may be useful for other collections.

## Proposed supporting contract

For a trapdoor collection T and a fixed natural c, construct a public shifted collection U.
Keep the domain family, encodings, decoder, permutations and polynomial-time evaluator. Shift
**gen, sample and inv together** so that an activation at n agrees with the corresponding T
activation at n+c, with published raw-run equations and typed coin transports. Publish field
readers and domain equivalences beside the new construction; no consumer reads its body.

Required results:

1. Sampler membership and trapdoor inversion correctness transfer through the public run
   equations and coin transports, yielding an actual TrapdoorCollection.
2. T.SampleClose δ gives U.SampleClose (fun n => δ(n+c)).
3. T.OneWay gives U.OneWay. For an adversary A against U, construct an adversary B against T
   running A at m-c. At m=n+c this recovers n exactly. The larger coin schedule of B leaves
   a uniform suffix unread; prove the inversion-probability equality by averaging that
   suffix. The initial finite parameter range does not change negligibility.
4. A public constant-shift closure lemma for negligible functions serves both the sampler
   error and inversion bound. Prove it once rather than copy it in the two transports.
5. If generated domains of T have width 2 max(n,c), generated domains of U have the exact
   width 2(n+c), including n=0. Candidate-home width lemmas must certify every generated
   index and every generator tape, including fallback behavior.

This is deliberately a **constant-shift** transport. Arbitrary polynomial parameter changes
can be constant or shrink the security parameter and do not automatically preserve one-wayness.
Machine-level reparameterization alone is not a hardness theorem.

## Existing ingredients and missing APIs

| Existing API | Source | What it supplies |
|---|---|---|
| NUPPT.exists_reparam | Complexity/Randomized/Closure.lean:295 | Exact polynomial parameter change, coin polynomial substitution, uniformity preservation and raw-run equation. |
| NUPPT.exists_reparam_advice | Complexity/Randomized/Closure.lean:328 | An arbitrary polynomially bounded inverse parameter map m↦m-c; extra coins are discarded. |
| NUPPT.reparam, coins_reparam, runAtL_reparam, coinLen_reparam, reparamCoins, runAt_reparam | Cryptography/Asymptotic/HardCoreLemmas.lean:882 onwards | Named reparameterized machines and typed activation equations. |
| EnsembleLemmas.acceptProb_reparam_advice | Cryptography/Asymptotic/EnsemblesLemmas.lean:260 | The existing unused-coin averaging pattern; not itself the required collection inversion theorem. |
| Collection.sample_eq_encD, TrapdoorCollection.inv_eq_encD | Cryptography/Asymptotic/Collections.lean | Canonical sampler/inverter outputs, to be consumed through public APIs. |

No Collection/TrapdoorCollection parameter-shift constructor or one-wayness transport was
found, nor a constant-shift negligibility lemma. The candidate encoding/index equations are
available, but generated-domain width readers are still needed beside the candidate definitions.
The evaluator is a polynomial-time function independent of the activation parameter; it can
stay unchanged. The three parameterized NUPPT machines must shift together.

## End-to-end use and honest assumptions

After this supporting bridge is proved, use the existing GL single-bit theorem, bitwise
construction and many-message lifting. This would keep the hypothesis sets
`ArithmeticFP + RSAAssumption` and `ArithmeticFP + BlumDensity + FactoringAssumption`.
It would not assume an impossible width equality, and would not add hard-core security as
an unexplained new number-theoretic assumption.

That legacy multi-message endpoint is still separate from the selected exact IND-CPA oracle
endpoint. Gate 06's admitted `SingleBitSecure.padded_cpa` and the precise multi-message game
conversion remain their own dependencies. No public-key CCA2 construction follows from this
normalization design alone.

## Execution boundary

This is supporting infrastructure below Implications, not another first-class catalog entry.
It needs a precise public statement/reader design and checked transport proofs. Do not modify
S2's five exclusively owned candidate files while the fill is active; candidate-home width
readers must use a post-S2 baseline. No new external audit/fill is prepared here. Ask the user
Codex or Claude before preparing either external job if that route is selected.

**Not yet clear to merge — normalization is a source-level design with unproved transports.**
