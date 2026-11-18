# Classes.decodeResidues_encodeVector proof draft

Status: one exact-header replacement, inspected but not elaborated. No live source edits;
no Lean, lake, build, or Git commands. No new helper declarations or imports.

## Deliverable

`DecodeResiduesEncodeVector.lean.inc` replaces only the admitted body of
`decodeResidues_encodeVector`, currently `Classes.lean:167`. A Python textual assertion
matched the entire original header through `:=` against the current live file.
One tactic block, no admitted terms, and maximum line width 75 columns.

## Proof route and reuse

1. Apply the published `Encoding.Modular.decodeVector_encodeVector` at the supplied
   modulus `p`, using the existing width-coverage assumption.
2. Rewrite the canonical encoded list using `hword`, then expose only the published
   `Encoding.Modular.decodeVector_eq` reader.
3. Split its explicit parser guard. In the success branch, `Option.some.inj` identifies
   the coordinatewise block casts with `v`; the local `decodeResidues_apply` reader
   already gives exactly those casts. Function extensionality closes the goal.
4. The failure branch says `none = some v` and is impossible by constructor disjointness.

This avoids proving or adding a change-of-modulus encoding helper. The theorem's
implementation decodes at `2^width`, but its already-proved `decodeResidues_apply`
reader exposes direct casts into `p`, which is all the round trip needs. No decoder
or encoder definition is explicitly unfolded and no generated equation is used.

Relevant published dependencies:

- `Encoding/ModularDecode.lean:82`:
  `decodeVector_encodeVector width hwidth v` gives
  `decodeVector width (encodeVector width v) = some v`.
- `Encoding/ModularDecode.lean:56`:
  `decodeVector_eq` exposes its length-and-range guard and success coordinate function.
- `Classes.lean:140`:
  `decodeResidues_apply p count width word i` equates the total decoder's coordinate
  with the natural block value cast directly into `ZMod p`.
- Core/Mathlib `Option.some.inj`, `funext`, `congrFun`, equality transitivity, and
  constructor disjointness. `Option.some.inj` is already used in the published modular
  decoder proofs themselves (`ModularDecode.lean:125`).

No other admitted Classes theorem is used. In particular the preceding
`decodeResidues_modulus` admission is not a dependency.

## Actual searches and reads

All commands were run in
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
sed -n '135,175p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
sed -n '40,124p' TCSlib/Cryptography/Encoding/ModularDecode.lean
sed -n '44,65p' TCSlib/Cryptography/Encoding/Modular.lean
rg -n 'listToNat.*natToList|listToNat.*encodeVector|decodeVector_encodeVector|decodeResidues_encodeVector|encodeVector.*val|ofFn.*getD|take.*flatten|flatten.*take' TCSlib/Cryptography/Encoding TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib/Data/List
```

The search located the required existing round trip and the local pointwise decoding
reader; no helper was needed. The earlier theorem docstring proposes reinterpretation
at the word modulus, but the present proof follows the equivalent direct-cast reader
already present in the public interface, with the same statement and all edge cases.

## Verification limits

Static checks confirm exact header preservation, one tactic block, no admitted terms,
and the width bound. The proof remains pending parent native elaboration. No false or
unattainable claim was found. Empty vectors and width zero are delegated to the published
modular round trip, whose proof explicitly handles width zero without cancellation.
