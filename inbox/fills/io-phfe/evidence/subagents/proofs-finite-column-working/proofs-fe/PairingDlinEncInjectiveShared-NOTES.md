# Revised BilinearGen.dlinEnc_injective using shared parameter codec

Status: full scratch candidate, inspection only; native verification pending. No Lean/lake/
build/Git/live edits/extra agent were used. Frozen main header/prose exact, one tactic block,
no remaining holes/sorry, no new helper/import/representation changes, ≤100 columns.
The shared PublicParams.encode_injective dependency is native pending. No standard-only
codec chain is claimed. Matrix-codec/length/correctness/diagonal-gap admissions are not used.

## Exact dependency alignment

Read dlinEnc_eq/dlinStr_eq. The first two pairEncode_injective steps recover description
WORD equality hdesc and generator WORD equality hgen. These are both List Bool equalities,
so they can be used BEFORE group types are aligned. congrArg₂ pairEncode hdesc hgen,
precomposed/postcomposed with PublicParams.encode_eq and its inverse, yields
hpp:pp₁.encode=pp₂.encode. Shared PublicParams.encode_injective supplies hPP:pp₁=pp₂.

Eliminate hPP before recovering any of the five arbitrary challenge points. Their encoded
words now use a common group; split the remaining pairs, then apply List.ofFn_injective
and encG_injective five times. Constructor reflexivity finishes. The consumer no longer
destructs public-parameter/subtype records or reasons about reachability/nonidentity proofs;
that entire responsibility is centralized in the pending shared theorem.

The existing layout and all algorithms stay unchanged. No group element gets a scalar
witness or inverse encoding. Every explicit simp item is a published reader. The two encode_eq
proof compositions are terms, not foreign definition reductions or generated-equation reads.

## Actual source/API search record

Read live Linear.lean:123-178 for the exact dependent challenge fields and frozen header,
Parameters.lean:84-96 for encode_eq, and the former manual candidate. Ran a narrow search
for congrArg₂ pairEncode / PublicParams.encode_injective / theorem encode_injective over
Pairing and the supplied helper fragment. The shared helper is still scratch/pending in this
observed source; no consumer algorithm/helper was added here.

Reused APIs: dlinEnc_eq, dlinStr_eq, Turing.pairEncode_injective, Prod.mk.inj, congrArg₂,
PublicParams.encode_eq, pending PublicParams.encode_injective, List.ofFn_injective and the
public encG_injective field. Their exact signatures were inspected in prior adjacent
invocations and are recorded in PublicParamsEncodeInjective-NOTES.md.

## Supersession and overlap

PairingDlinEncInjective.lean.inc and its original notes remain unmodified. Their SHA-256 and
replacement path are recorded in PairingDlinEncInjective.SUPERSEDED.md. This replacement,
paired with the revised MDDH consumer, removes duplicated parameter-record reconstruction;
only each existing wire layout's necessary pair parsing remains. No private proof copy or
new generic local helper is introduced.

Native focus: the term-level reconstruction of pp.encode equality from two ordinary word
equalities, dependent parameter equality elimination, and five group point injections. All
unverified substantive dependency status is explicit above.
