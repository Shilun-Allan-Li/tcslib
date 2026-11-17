Each question records a reading the job had to apply where the brief leaves room; the inventory follows the recommended option
(first), and nothing in it depends on a different answer except where said.

- **DW10-W1. Moved items.** The brief lists "moved" among CHANGED, and FIXED_SINCE as "the recorded failure is gone at the base".
  (a) *Recommended, applied:* a moved item whose failure is gone is FIXED_SINCE (the move noted in `change`); a moved item that
  still fails is CHANGED ("moved"; with the rest of the comparison). (b) Every moved item is CHANGED, failing or not.
- **DW10-W2. An item recorded under seal A that now fails only under seal B.** (a) *Recommended, applied:* CHANGED ("now
  B-only"), classed SEAL-B-ONLY, so it goes to the separate ruling. (b) FIXED_SINCE (canonical coe-A passes), with the B failure
  listed again as a NEW row.
- **DW10-W3. Controls for owners whose readers are not definitional.** 29 owners have published readers, but none holds by
  `intros; rfl` unsealed (propositional readers), and 2 owners (`NumberTheory/Euclid`, `SequentialZK/SimulatorMachine`) define
  only well-founded recursions, so neither a reader nor `eq_def` is `rfl`-checkable. (a) *Recommended, applied:* the first group
  runs the `eq_def` negative only and is recorded `no reader` with the note "readers exist, none rfl-checkable"; the second gets no
  pair, recorded with the reason. (b) Treat these owners as needing a definitional (`rfl`) reader in Stage 2.
- **DW10-W4. `show`/`change` reads.** The brief's suite item 4 names reads by `show`/`change`, but the archived lexer that the
  brief requires unmodified does not inventory them. (a) *Recommended, applied:* accept; such reads are definitional, and the seals
  (all four variants) catch every one of them as a seal failure in its declaration. (b) Extend the lexer in a later job.
- **DW10-W5. File-level `failed to set [local irreducible]` diagnostics.** Some owner files already make a definition locally
  irreducible with their own `attribute [local irreducible] …` line. Under the seal that line fails ("`X` is currently
  `[irreducible]`, `[semireducible]` expected"). The definition is already irreducible, so no later step is masked. #248 recorded
  two of these, SEAL-0306 and SEAL-0307 (`SubHybrids` l.68, disposition `inherited_source_attribute_interaction`, scope
  NO-DECLARATION). They reproduce at the base, and the NEW rows add the same diagnostic at the attribute lines of `Unary`,
  `UnaryPolynomial`, `WordTiming`, `UniversalPadding/BinaryRoot`, `UniversalPadding/Machine` and `Pseudorandom/Functions/GGM`.
  None of the five classes fits.
  (a) *Recommended, applied:* these are not seal debt. The rows keep their status (STILL_OPEN or NEW), get no class and the fix
  "none (harness interaction)", carry pending `DW10-W5`, and are listed separately. A later harness could leave out the
  definitions an owner already marks locally irreducible, or install with `allowUnsafeReducibility`.
  (b) Class them STAGE2, with the fix "drop the file's own attribute line". That would change the owner's behaviour outside the
  seal, so the job does not recommend it.
- **DW10-W6. Shadow transfers (sub-A's review, 39 rows).** Four files restate main-file definitions verbatim in their own
  namespaces (`GI`, `ColProofs`, `GIZK`, `ColSimMachine`):
  - `ZeroKnowledge/GraphIsomorphism/Proofs.lean`
  - `ThreeColoring/ProtocolProofs.lean`
  - `GraphIsomorphismZK/Simulator.lean`
  - `ThreeColoring/SimulatorNumeric.lean`

  The main files take the shadow's results over by definitional equality, which the seal breaks.
  (a) *Recommended, applied:* STAGE2. Each row's fix names a bridge equation `X = GI.X` (or the like), proved from the shadow's
  published or to-be-added readers.
  (b) Retire the shadow copies in Stage 2 and state the results once, on the main definitions. That is a larger refactor, and it
  touches no statement.
  The choice is a design decision for Stage 2; the inventory rows do not depend on it.
- **DW10-W7. Lexer false positives from local bindings.** The archived lexer resolves an unqualified name without local context,
  so a local `let P := …` read by `simp [P]` is inventoried as a read of `Complexity.P`. Four scan items are such locals:
  - `SeedMajority/Enumeration` l.71
  - `Candidates/DiscreteLogHardcore` l.2656 (C1-0284; #248 recorded it)
  - `SecureComputation/SpecialEncryptionMulti` l.301
  - `Yao/HybridProof/GarbledRun` l.117

  (a) *Recommended, applied:* drop them as not reads; they are listed in `evidence/scan-shadowed.tsv`. C1-0284 is FIXED_SINCE,
  and its `change` says why. Only a binder directly naming the item counts: `let`, `set` or `have X`, `intro`/`obtain` patterns,
  `fun` binders, and `(… X :` binders. The archived lexer is left unmodified.
  (b) Keep them as items with the fix "none".
