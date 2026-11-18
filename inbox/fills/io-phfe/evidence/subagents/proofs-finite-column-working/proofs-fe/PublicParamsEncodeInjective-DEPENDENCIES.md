# Shared PublicParams.encode_injective: proposed API and revised dependency plan

Status: DESIGN / SEARCH REQUEST ONLY. No new theorem proof, consumer proof block, live edit,
Lean/lake/build/Git command or extra agent was produced. The helper is a term-sorry target
for root's native exact?/apply? searches, not an integrated/proved declaration. Existing
mddhEnc_injective and dlinEnc_injective headers/prose and earlier scratch bodies are untouched.

## Exact new API and home

Full name: TCSlib.Cryptography.Pairing.PublicParams.encode_injective.
Home: MatrixDH/Parameters.lean immediately beside encode_eq, before end PublicParams.

  theorem encode_injective {G : BilinearGen} {κ : ℕ} :
      Function.Injective (PublicParams.encode (G := G) (κ := κ))

The exact header/docstring is in PublicParamsEncodeInjective.target.lean.inc. It proves a
property of the existing codec; it introduces no algorithm, sampler, machine, group/scalar
representation, parameter field, or efficiency obligation. No new import is expected: all
needed pair/list/group readers are in the existing Parameters import closure (root verifies).

Root's probe goal is exactly the displayed Function.Injective proposition. Use the Parameters
prefix ending after encode_eq; exclude this helper and consumer admissions. The probe JSON
records the current source file SHA-256 rather than claiming an unqueried Git HEAD. Requested
exact?/apply?/statement checks are NOT RUN by this agent. No proof is written before results.

## Revised MDDH consumer dependency plan

The manual local hPP block in PairingMddhEncInjective.lean.inc is now a superseded candidate
route, retained as scratch evidence but not recommended for integration.

1. Read mddhEnc_eq; pairEncode_injective separates hpp:pp₁.encode=pp₂.encode from the matrix
   tail equality.
2. Apply the new PublicParams.encode_injective to hpp, then eliminate that parameter equality
   in the MAIN goal. Both dependent group-matrix types now coincide.
3. Pair-inject the matrix tail; apply pending BilinearGroup.groupMatrixEnc_injective to the
   base matrix and response matrix separately; constructor reflexivity finishes.

Proposed dependencies: new shared PublicParams.encode_injective, existing mddhEnc_eq /
pairEncode_injective, and pending groupMatrixEnc_injective. No parameter-record or description/
generator reconstruction remains in this consumer. No existing header/prose change is needed.

## Revised DLIN consumer dependency plan: reuse IS possible

DLIN's serialized layout is nested differently from pp.encode, but its first TWO pair-
injectivity steps already provide exactly the two required WORD equalities:

  hdesc : pp₁.description.val = pp₂.description.val
  hgen  : List.ofFn ((G.group κ pp₁.description.val).encG pp₁.generator) =
          List.ofFn ((G.group κ pp₂.description.val).encG pp₂.generator)

These are equalities of ordinary List Bool values, so they are usable BEFORE the groups are
aligned. Reconstruct pp encoding equality with congrArg₂ pairEncode hdesc hgen and the two
published PublicParams.encode_eq readers (left reader, pair congruence, inverse right reader).
Apply new PublicParams.encode_injective, then eliminate that equality. The five remaining
point-word equalities can now use List.ofFn_injective and encG_injective in one common group.

Thus the DLIN consumer still parses description/generator WORDS as its frozen sketch says,
but all dependent parameter-record reconstruction and proof-irrelevance reasoning moves to
Parameters.lean. The old nested PublicParams/GroupDescription rcases/subst/generator-recovery
part in PairingDlinEncInjective.lean.inc is a superseded candidate route. No new layout reader
or public algorithm is needed; dlinEnc_eq/dlinStr_eq provide the exact existing nesting.

Proposed dependencies: new PublicParams.encode_injective, existing dlinEnc_eq/dlinStr_eq,
PublicParams.encode_eq, pairEncode_injective, List.ofFn_injective and encG_injective. Neither
length theorem nor correctness/reduction admission is used.

## Reuse and search record

Read current live Parameters.lean:53-98, Linear.lean:155-179, MatrixDH/Defs.lean:97-115, and
shared TuringMachine/Encoding.lean:165-178. Re-ran the targeted encode_injective/encode_eq/
dlinStr_eq/pairEncode_injective search over those exact modules. Current live Parameters
publishes encode_eq but no injectivity theorem. The first consumer search was already logged
in PairingMddhEncInjective-NOTES.md; no new native searches are claimed here.

The proposed shared theorem centralizes the only duplicated description/generator dependent
record step. Consumers retain only the layout-specific pair parsing, which is forced by their
different existing encodings. No private proof is copied or replaced by a generic local helper.
Any future proof of this new shared theorem must wait for root's native exact?/apply? results.

## Scope/freeze/dependency status

All existing main statements/prose stay frozen. Only the new public theorem signature is
proposed, under root's explicit modularity decision and within MatrixDH/**. groupMatrixEnc_
injective remains native pending; new encode_injective typing/reuse search/proof remain
pending. None of these planning artifacts is evidence that a proof or audit passed.
