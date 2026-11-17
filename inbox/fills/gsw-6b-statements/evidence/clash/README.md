# Name-clash and shadow scans (check 11)

All scans at the final statement head 8f92fe7d53967bc488a4075fb38210e7d40b9031 (`NameDump.lean` run on oleans
built from sources identical to it; the facades are final). Earlier runs at a855e111 gave the same 140 names.

## (a) Full names
* `NameDump.lean` → `NameDump.log`: every non-internal constant of the 9 new modules, the 2 facades and
  `LWE/BitEncoding` (private names demangled); filtered to the new ones → `new-names.tsv` (**140**: Bootstrap 28,
  LeveledSecurity 22, Asymptotic 20, Leveled 18, DecryptFormula 17, Circular 11, Branching 9, PolyRatio 8,
  O2 5, Ratio 2; the facades declare nothing). No private declaration in the new files.
* `tools/probe/declnames.py` → `base-names.tsv` (base 3e51b5f2: 1,479 files of TCSlib/, TCSlib.lean, audits/;
  34,838 names incl. structure fields, constructors and listed `simps` projections), `pr355-names.tsv` (#355 head
  d3c7cb00, fetched read-only into the lead's clone: 1,378 files, 33,256 names), `final-names.tsv` (8f92fe7d).
* `tools/probe/clash6b.py` → `clash-scan.txt`: **RESULT-a new_names=140 clashes=0** (base, #355 head, and the
  GF-W1 reserved names `TreeCircuit.maxDepth_le_of_forall`, `TreeCircuit.maxFaninL_le_of_forall`,
  `prefixVal_eq_of_false`, `prefixVal_testBit`, `depth_getD_le`, `maxFanin_getD_le`: none is declared).

## (b) New short names that exist elsewhere
TCSlib (base and #355): **3 of 139** short names —
* `Coins` (new `GSW.Coins`): `Complexity.NUPPT.Coins` (Randomized/PPT.lean:222), `LWE.Noise.Coins` (field,
  LWE/Noise.lean:43), `SecureComputation.HybridProtocol.Coins` (Hybrid.lean:146), `Strategy.Coins`
  (ZeroKnowledge/Interaction.lean:129).
* `select` (new `GSW.select`, `GSW.Encrypts.select`): `clPlacement.select` (private field, CookLevin/Hardness.lean:1801),
  `Randomness.Rejection.select` (Extraction/Rejection.lean:185), `Turing.Cfg.select` (TuringMachine/Build/Embed.lean:1092).
* `PublicKey` (new `GSW.PublicKey`): `RSA.PublicKey` (RSA.lean:476).
Mathlib, Batteries, core (`tools/probe/short_ext.py` → `short-external.txt`): only `select` (Mathlib
`WittVector.select`, two private `select`s of `MkIffOfInductiveProp`, `Lean.PremiseSelection.select`).
`pins.txt`'s phase-5 short names (`encrypt`, `view`, `realView`, `reduction`, `decrypt_eq`) are not new names of
6b (6b declares none of them).

## (c) Shadowing: no unqualified use in a DOWN module changes resolution
`tools/probe/shadow6b.py` → `shadow-scan.txt` (at 8f92fe7d).
* Import graph: of the 18 DOWN modules (closures.txt), only the facades `GSW` (now importing the 8 new GSW
  files), `Homomorphic`, `AdvancedEncryption` reach the new GSW modules, and the facade `LWE` reaches
  `LWE/Ratio`; the other 14 reach none (the new files import them, never the converse). O2's five names are in
  scope in all 18 (through `BitEncoding`).
* The facades contain only imports, the three `set_option` lines and docstrings (no identifier is resolved
  in them).
* Token scan (comments and strings stripped) for every identifier whose last component is a new short
  name in scope there: **0 modules** outside `BitEncoding` itself (the defining file). The hits `χ.Coins`,
  `PublicKey` (as in `Encryption.PublicKey`), `Coins` in Regev/GSW phase-5 modules are on names whose new
  homonyms are not in scope there (and `χ.Coins` is dot notation on `χ : LWE.Noise`).
* Hence no identifier of a DOWN module resolves differently. Downstream of the root facade `TCSlib.lean`
  (imports only) nothing is affected either; global uniqueness of the new full names is (a).
* Instances: the one new instance `Parameters.neZero_columns` is visible only where `DecryptFormula` is
  imported (the three facades above and the new files), so no DOWN module's elaboration changes.
