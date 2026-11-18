# Classes.decodeResidues_modulus proof draft

Status: one exact-header replacement, not elaborated. No live source changes, Lean,
lake, build, or Git commands. The parent reported M0 statement-reader validation
387/387; this is a separate, unverified proof draft.

## Deliverable

`DecodeResiduesModulus.lean.inc` replaces only the existing admitted body of
`decodeResidues_modulus`, currently `Classes.lean:157`. A Python textual assertion
checked its complete existing theorem header through `:=` against the live file.
The snippet has one tactic block, no helper declarations, no admitted terms, and
maximum line width 85 columns. No new imports are expected.

## Proof and dependencies

1. `PNat.coe_injective` identifies the two positive naturals from the supplied equality
   of their natural values. Case elimination substitutes the second modulus.
2. `funext` reduces equality of residue-vector functions to a coordinate equality.
3. `ZMod.natCast_zmod_val` states precisely `(a.val : ZMod p) = a` for nonzero `p`.
   The existing positive-natural `NeZero` instance supplies the requirement.

No decoder definitions are unfolded, no generated equations are used, and no other
admitted Classes theorem is a dependency. In particular this proof needs neither
`decodeResidues_apply` nor any encoder round-trip theorem: the supplied modulus equality
makes the same-modulus representative identity sufficient.

## Actual searches and reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

- An initial admission search used the nonexistent `FunctionalEncryption/Wee20/Classes.lean`
  path and returned an IO error. The file is directly under `FunctionalEncryption`.
- Located the current file and modular roots with:

  ```sh
  rg --files TCSlib | rg 'Classes\.lean$|Modular.*\.lean$|Modular/'
  ```

- Inspected all existing Classes admissions and surrounding readers:

  ```sh
  rg -n -B 9 -A 8 'sorry' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
  sed -n '1,245p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
  sed -n '245,284p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
  ```

- Searched the local encoding/decoding and finite-sum interfaces before considering a helper:

  ```sh
  rg -n 'encodeVector|decodeVector|decodeResidues|encodeResidues|sum.*mul|snoc.*sum|sum.*snoc' TCSlib/Cryptography/Encoding/Modular.lean TCSlib/Cryptography/Encoding/ModularDecode.lean TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
  ```

- Located the representative-casting and positive-natural equality APIs:

  ```sh
  rg -n 'theorem.*natCast.*val|lemma.*natCast.*val|theorem.*coe.*val|lemma.*coe.*val|natCast_zmod_val' .lake/packages/mathlib/Mathlib/Data/ZMod .lake/packages/mathlib/Mathlib/Algebra/CharP
  rg -n 'coe_injective|coe_inj|eq_iff|ext' .lake/packages/mathlib/Mathlib/Data/PNat/Defs.lean .lake/packages/mathlib/Mathlib/Data/PNat/Basic.lean
  rg -n 'PNat\.coe_injective|PNat\.coe_inj|PNat\.ext|natCast_zmod_val|ZMod\.natCast_val' TCSlib/Cryptography .lake/packages/mathlib/Mathlib/Data/PNat
  ```

  Relevant declarations found:
  - `Mathlib/Data/PNat/Defs.lean:113`:
    `PNat.coe_injective : Function.Injective PNat.val`.
  - `Mathlib/Data/ZMod/Basic.lean:197`:
    `ZMod.natCast_zmod_val {n} [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a`.
  - Existing downstream direct use at `Candidates/DDH.lean:293` confirms the same
    representative identity is already part of the project dependency surface.

## Scope and remaining checks

Exactly one existing admission is drafted. No statement changes or false claims found.
The quadratic/PHFE wire embedding remains untouched: its original-word duplication and
block-decoding argument is larger than this same-modulus bridge. The parent must perform
native elaboration and any inventory update before treating this draft as verified.
