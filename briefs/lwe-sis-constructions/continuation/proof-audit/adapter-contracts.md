# Next binary representation and sampling adapters

This is records-only design while the user-dispatched proof audit runs. No Lean
definition, theorem, import or owner API is changed. Root checked the key source
contracts; one authorized internal agent supplied read-only research. No native
probe, cache job, external job or worker checkout mutation was performed.

## Reuse inventory

Locations are in the frozen checkout, relative to `TCSlib/`. These declarations
have filled source bodies; that alone does not certify their transitive axiom
dependencies.

| Public contract | Source location | Consumer role |
|---|---|---|
| `BinArith.polyTimeComputable_reverse` | `Complexity/ClassP/BinaryArith/Mul.lean:73` | Convert bit order without a new reversal machine. |
| `BinArith.polyTimeComputable_normBits` | `Complexity/ClassP/BinaryArith/Basic.lean:137` | Normalize an arbitrary little-endian word to `Nat.bits`. |
| `BinArith.polyTimeComputable_add`, `polyTimeComputable_sub` | `BinaryArith/AddSub.lean:162,233` | Arithmetic after normalization. Their `add_pairEncode` / `sub_pairEncode` equations at lines 147/152 cover canonical operands. |
| `BinArith.polyTimeComputable_mul`, `mul_pairEncode` | `BinaryArith/Mul.lean:217,113` | Product and its numeric reading. |
| `BinArith.polyTimeComputable_mod`, `mod_pairEncode` | `BinaryArith/Div.lean:245,62` | Existing general remainder route; no private division host. |
| `Candidates.natToList_zero_append_drop` | `Cryptography/Candidates/Arithmetic.lean:203` | Exact MSB width normalization, including truncation. |
| `Cryptography.polyTimeComputable_zerosPoly` | `Cryptography/Asymptotic/CollectionsLemmas.lean:62` | Generate polynomially many zero bits, using the first pair component's length. |
| `polyTimeComputable_pairTakePoly`, `pairDropPoly` | `Complexity/Randomized/Primitives.lean:200,213` | Parameter-dependent prefix/tail cuts, with complete function signatures. |
| `polyTimeComputable_takePrefixByLength`, `dropPrefixByLength` | `Complexity/ClassNP/PolyTimePrefix.lean:345,358` | Dynamic cuts where the offset is supplied as a unary word. |
| `BinArith.chunkW_pairEncode`, `polyTimeComputable_chunkW` | `BinaryArith/Loops.lean:500,519` | Existing block host; contract requires positive width or zero blocks. |
| `Randomized.bitsEquiv`, `blocksEquiv` and their `_apply` readers | `Complexity/Randomized/RandomBits.lean:220,224,258,263` | Exact uniform/independent dyadic samples as bijections. |
| `Cryptography.uprob_comp_equiv` | `Cryptography/Foundations/Probability.lean:165` | Move those bijections directly into the current real-valued experiments. |

Here `BinaryArith/` abbreviates `Complexity/ClassP/BinaryArith/`. Existing
`padStr` pads on the right and keeps the prefix; numeric width normalization
must instead retain low bits. Do not identify those operations.

## Smallest missing correspondence

The missing glue is the endian equation, rather than another arithmetic host:

\[
\operatorname{LogProg.bitsVal}(w.\operatorname{reverse})
=\operatorname{NumberTheory.listToNat}(w).
\]

A future owned reading lemma can prove it by induction using
`NumberTheory.listToNat_nil`, `listToNat_cons`
(`NumberTheory/Primality.lean:677,682`),
`BinArith.bitsVal_append_singleton` (`Basic.lean:56`) and list reversal equations.
Reversal followed by the existing normalizer then produces
`Nat.bits (listToNat w)`. Apply arithmetic through its canonical-pair equations;
there is no need to unfold a foreign machine or arithmetic definition.

This is a proposed mathematical leaf for the next statement gate, not a filled
Lean lemma in this continuation.

## Exact fixed-width output without a new padding host

For an encoded pair `pairEncode u b`, put `W = p.eval u.length`. The existing
Candidates equation is

\[
(\operatorname{natToList}(W,0)\mathbin{++}b).\operatorname{drop}(|b|)
=\operatorname{natToList}(W,\operatorname{listToNat}(b)).
\]

The zero-numeral equality follows from the existing numeral round trip and
the value of an all-false word. Generate `replicate W false` using
`polyTimeComputable_zerosPoly p`, append `b`, and prepare

```lean
pairEncode b (List.replicate W false ++ b)
```

`polyTimeComputable_pairDropPoly .var` now drops exactly `b.length` bits. The
prepared word has length `3*b.length + W + 2`, by `length_pairEncode`, and the
output has length exactly `W`. It handles shorter, longer and empty words,
including zero width. On an invalid original pair, both total projections
are empty, so it yields `p.eval 0` zero bits; rejection requires an explicit
guard in the consumer.

Consequently future scalar contracts can return the exact strings

\[
\operatorname{natToList}(W,a+b),\qquad
\operatorname{natToList}(W,ab),\qquad
\operatorname{natToList}(W,a+2^W-b)
\]

for in-range residue values `a,b < 2^W`. The writer's existing
`listToNat_natToList_eq_mod` supplies reduction modulo `2^W`. The subtraction
operand cannot underflow after adding the modulus; plain natural subtraction
would be wrong. The modulus word itself has only `W+1` bits and is generated
from zeros and a one bit; no exponentially long unary modulus is needed.

The next owned adapter module should give total behavior, canonical-input
correspondence and output-length bounds for each operation, then consume the
existing public machine contracts. It must not replace `ArithmeticFP` by an
unproved claim of unconditional efficiency.

## Exact dyadic sampling without a new sampler host

`Randomized.blocksEquiv N W` already maps `N*W` fair bits bijectively to `N`
independent values in `Fin (2^W)`. Compose it with pointwise `ZMod.finEquiv`,
then the existing row-major index equivalence. `uprob_comp_equiv` transfers
the resulting bijection directly to the LWE/SIS experiment's uniform law.
A separate rational-`randProb` to real-`uprob` conversion API is unnecessary.

The block reader is little-endian. The actual machine must match the typed
sampler through the endian lemma or per-block reversal; raw block bytes are
not automatically the MSB-first canonical output. The SIS dyadic matrix needs
exactly `2*(κ+1)^4` fair bits, matching its proved index budget.

The existing `UniformSample` rejection sampler is available for future
non-dyadic sampling, with its own failure accounting. An arbitrary finite noise
law cannot always be the exact output of a fixed number of fair bits. Select
an implemented bit-seed noise profile, or separately prove and account for an
approximation; `Family` size bounds alone do not implement its schedules/noise.

## Verification boundary and next gate

The static scan found the same 17 inherited admission tokens in the relevant
machine import closures and none in `RandomBits`' three-module TCSlib closure.
These are source-closure observations, not axiom-dependency probes. The later
machine gate must run the selected modules through the prescribed check script
and probe the consumed public contracts on its own pinned objects. No new native
work is needed for these records, and the current proof audit remains frozen.

Separately, the future leftover-hash consumer lacks owner-side readers for
`InformationTheory.IsUniversal` and `FinDist.HasMinEntropy`. The exact two-file
proposal is `proposed-probability-readers.patch`, with baseline hashes in the
sibling JSON. It adds only `isUniversal_iff` and `hasMinEntropy_iff`, without simp
attributes or new definitions. It passes `git apply --check` but is **unapplied
and not Lean-checked**. These shared probability edits need user coordination
before implementation; no consumer is allowed to bypass that by unfolding.

Notation: `w,u,b` are bit strings; `|b|` is their length; `p` is a `PolyExpr`;
`W` is the requested width; `a,b` in the scalar formulas are natural operand
values; `N` is a block count; `κ` is the existing security parameter.
