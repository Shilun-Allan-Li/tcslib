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
