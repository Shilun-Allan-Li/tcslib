# Addendum 1 to `briefs/ch34-b4-mem.md` (B4 membership): the walker as a generic host

Issued 2026-10-12, after dispatch. It amends only the walker's **form**. Your target, file
ownership, statement freeze, ancestor, verification and delivery are unchanged. Record in
`REPORT.md` that you received this addendum, and at which point of your work.

**Why.** The user has adopted a **host-first rule**. A search, recursion, evaluation scheme or
runner is a reusable host. It is no longer built as a one-off inside the proof that first needs
it. Your depth-first assignment walker (route step 2) is the library's first **AND/OR
evaluator**. Savitch's midpoint recursion, NP ⊆ PSPACE and the game values of
`ClassPSPACE/Games.lean` are its next consumers. Your brief predates the rule, so the walker
stays `private` in your block, but write it so that it can be promoted without re-proof.

**What changes (binding):**
1. **Generic in the leaf.** State the walker's contract once, for an arbitrary leaf-verdict
   module rather than for the CNF evaluator. Model the leaf as a hypothesis-carrying parameter:
   a machine (or a family) together with its framed contract. That contract says:
   - from a configuration holding the current record word, it reaches its exit with a verdict
     bit;
   - it has a time bound;
   - it has a head-envelope clause in the library's form
     (`∀ u ≤ t, ∀ j, |pos_j(u) − pos_j(0)| ≤ B`);
   - it leaves the record word unchanged and every scratch tape blank, with the native input
     head at a position the contract fixes.

   The CNF evaluator (route step 3) is then **one instance**, proved separately. `TQBF_mem_PSPACE`
   instantiates the generic walker with it.
2. **Generic in the node kinds.** The quantifier stored in each record decides whether a level
   is AND (∀) or OR (∃). The walker's semantics is a pure private function over the record word
   and the leaf predicate: an AND/OR value with short-circuiting. Prove it equal to
   `QBF.truthAux m qs (fun _ => false) 0` as a separate lemma, so the walker's own contract
   never mentions QBF or CNF.
3. **Time and space clauses.** The walker's contract carries a time bound in the number of
   rounds and the leaf's time, plus a head envelope. Space must come out as the record word, plus
   the leaf's space, plus a constant. The `SPACE (n + 1)` packaging then follows from the
   instance.
4. **Self-contained statement.** The walker's main private theorem gets a natural-language
   docstring statement and a proof sketch that make sense without TQBF. Flag it
   "**promotion candidate (host H1, AND/OR evaluator; `machine-library-design.md` §14)**".
5. **`REPORT.md`.** Under promotion candidates, give the generic contract verbatim, the
   instance's obligations, and anything that would have to generalize for a non-Bool digit
   domain (Savitch's digits are records walked by first/next rows). Do **not** build that
   generalization.

**Not required.** No new public declaration, no file other than yours, no non-Bool digits. Your
brief's invariants still hold: no per-level formula copies, matrix re-read from the input, free
variables read `false`. So do the validate-first fold, the index-lookup idiom and the phase
packaging. The route's sanctioned refinements are unchanged.

**If this costs too much.** If the generic form would materially enlarge the work (more than
about a fifth), deliver the walker as your brief prescribes. Keep the leaf-specific parts
isolated in their own lemmas, and explain in `REPORT.md` exactly what blocked the generic form.
That is not an escalation, and the target still comes first.
