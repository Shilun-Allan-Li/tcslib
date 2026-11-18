# Existing Classes.ofFn_encodeTensorBits proof draft

Status: exact-header/prose replacement, inspected but not elaborated. No live files
edited; no Lean, lake, build, or Git commands. No helper or new import is proposed.

## Deliverable

`ClassesOfFnEncodeTensorBits.lean.inc` preserves the entire current frozen docstring,
proof sketch, and theorem header of `ofFn_encodeTensorBits`; it replaces only the term
placeholder with one tactic block. The proof body is:

```lean
  simpa only [encodeTensorBits_eq, padFin_def] using
    (ofFn_padFin_of_length (encodeTensor_length width C))
```

Static checks matched the live prose/header exactly, found one tactic block and no
admitted terms, and measured maximum line width 96 columns.

## Nearest reused lemmas

1. `Classes.encodeTensor_length` (currently :191) gives the exact finite bit width
   required by the existing list round trip.
2. `Classes.encodeTensorBits_eq` (currently :201) reads the tensor's finite bit function
   as `fun i => (encodeTensor width C).getD i.val false`.
3. `TCSlib.Cryptography.ofFn_padFin_of_length`, in
   `Cryptography/Asymptotic/Adversary.lean:218`, already states the complete generic
   list-reading round trip:
   `w.length = L -> List.ofFn (padFin L w) = w`.
4. The published `padFin_def` reader in the same module :174 identifies padFin with
   precisely the same finite getD reader, including the false default.

The exact generic round trip is reused rather than reconstructed by list extensionality
or induction. Both TCSlib definitions are accessed only through their published readers;
no foreign definition or generated defining equation is explicitly unfolded. No admitted
Classes theorem is a dependency. Empty bit width is handled by the generic list theorem.

The shared theorem is already in the existing import closure:
Classes -> Encoding.ModularDecode -> Encoding.Modular -> Candidates.Arithmetic ->
NumberTheory.Primality -> Asymptotic.CollectionsHelpers -> Asymptotic.Adversary.
Those direct imports were read; no extra broad import is required by this draft.

## Actual searches/reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

- Read Classes:178-214 for exact current encoders, width reader, frozen prose/header.
- Searched core/Mathlib/Encoding before considering any helper:

  ```sh
  rg -n 'ofFn.*getD|getD.*ofFn|ofFn.*getElem|ofFn_get|ofFn.*length|ofFn.*get' .lake/packages/mathlib/Mathlib/Data/List/OfFn.lean /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/OfFn.lean TCSlib/Cryptography/Encoding | head -95
  rg -n 'ofFn.*getD|getD.*ofFn|List\.ofFn_get|ofFn.*padFin|ofFn.*getElem|List\.ofFn_injective|ofFn_inj' TCSlib/Cryptography | head -80
  rg -n 'getD_eq_getElem|getD.*getElem|getElem.*getD|getElem?_eq_getElem' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List .lake/packages/mathlib/Mathlib/Data/List | head -60
  ```

  Nearest core/Mathlib alternatives were `List.ofFn_get`, `List.ofFn_getElem`,
  `List.getD_eq_getElem`, and the getD/getElem?/Option readers. The project-wide search
  then located the stronger exact `ofFn_padFin_of_length` bridge.

- Located the published shared operation/reader/round trip:

  ```sh
  rg -n 'ofFn_padFin_of_length|def padFin|theorem padFin_eq|theorem padFin_apply' TCSlib | head -35
  sed -n '165,183p' TCSlib/Cryptography/Asymptotic/Adversary.lean
  sed -n '209,231p' TCSlib/Cryptography/Asymptotic/Adversary.lean
  ```

- Read Mathlib List/OfFn:88-104 and List/GetD:20-34; inspected existing
  Lossy/Gadget:183-202 as an example of its ofFn_getElem use. These alternatives
  need not be copied into the proof.
- Read direct import headers in Classes/Defs.Raw, Pairing/MatrixDH/Parameters,
  Pairing/Group, Games/Probability, Encoding/ModularDecode, Encoding/Modular,
  Candidates/Arithmetic, NumberTheory/Primality, Asymptotic/CollectionsHelpers, and
  Asymptotic/Adversary to establish existing dependency availability.
- Some preliminary searches looked in Complexity/Randomized or speculative
  Pairing/Generators.lean / NumberTheory/Binary.lean paths before finding the actual
  generic theorem under Asymptotic/Adversary. Those speculative files did not exist;
  no dependency or source content was taken from them.

## Scope and pending checks

Exactly one existing admission is drafted here. The new residue-block helper is not
proved in this invocation. Parent reports its isolated prefix native searches have
now finished with no complete match (exact? expected failure, apply? partial irrelevant
ZMod suggestions); those results are separate from this proof draft.

Native elaboration, standard-axiom validation, and admission inventory refresh remain
with the parent. No false or unattainable claim was found.

Final focused `rg -n` confirmed encodeTensor_length:191, encodeTensorBits_eq:201,
and ofFn_encodeTensorBits:208 at delivery time.
