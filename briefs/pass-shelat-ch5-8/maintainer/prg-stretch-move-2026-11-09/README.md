# Asymptotic PRG stretch relocation

Seyoon merged the next-bit split #265 at `8fae4be42ba253578165e8449f0aa65cac71edf0`. The Lean sources and checker
inputs match its verified head `6776475858254d11adadf57776cae215c2c6cd79`.

[PR #266](https://github.com/Shilun-Allan-Li/tcslib/pull/266) at `bcb6f33a120dd663d363afe21f6214465578d990` puts the asymptotic PRG stretch proof, truncation,
and doubling in `Pseudorandom.Generators.Asymptotic.Stretch`. The evaluator and
hybrid distinguisher machine, with their run agreements, live in `StretchMachine`.
The shared wrapper, preprocessing and string lemmas move to
`Asymptotic.ReductionSupport`. The stretch imports are independent of the asymptotic
hard-core construction and GGM. The old imports re-export the moved declarations.

- The final replay covers all 77 affected modules, including `TCSlib` and
  campaign Checks. It checks 52 modules from source and verifies 25 affected
  transfers against identical source and dependency bytes. It also verifies
  1,014 unaffected objects and 3,810 external objects.
- The standalone and compatibility imports print the same seven types. The
  declaration census matches 468 materialized entries, including 108 moves to
  the three new modules. The `owpGenPRG` definition and its generated equation
  are checked for definitional equality against the old spelling. Both lazy
  equations still resolve with the same types. Lean also materializes three
  equations for existing machines and relocates one generated congruence
  theorem. The former private `take_ofFn_castLE` is replaced by the existing
  theorem of the same type.
- The permutation proof uses the published expansion equations. Three hard-core
  proofs transport coins through `NUPPT.coins_wrap` and the existing cast reader.
  Eight final whole-file seals reconcile against five baseline seals. All 14
  remaining diagnostics match existing proof steps, five now in `Stretch`.
  Four inherited diagnostics close. The control passes unsealed, fails at
  `rfl` under the mask, and passes through `PRG.expand_stretch` under the same
  mask. The scans find zero explicit foreign-definition reads and zero references to
  foreign generated equations across the checked owners. [Ledger mapping](READS.json)
- The general style check reports zero findings. The campaign linter's two
  added facade reports come from the finite `Generators.lean` sharing the
  directory name. `Pseudorandom.lean` exports both new modules directly. The
  existing reader warnings are inherited.
- The archive retains the first failed native attempt, which found a duplicate
  private lemma made visible by the new import order. It also retains the
  development masks and the first successful 77-module replay. The final replay
  follows a documentation-only amendment adding a proof sketch and updating a
  reference to the new home of truncation.

`stretch-checks.zip` has SHA-256 `17ee3d72536ddf9695802e6e42ef482aee3094ef1c7fba045478b77e21cb4247`.
[Verification hashes](VERIFICATION.json)

Seyoon merged this slice at `6387f775c8848e5a1e3be7c36f73be56371c63a3`. The Lean sources and checker inputs match the verified head. The permutation-to-PRG move follows in [PR #267](https://github.com/Shilun-Allan-Li/tcslib/pull/267).
