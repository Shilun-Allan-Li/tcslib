# gsw-core fill: rules for sub-agents (issued by the lead)

You are a sub-agent of the lead of fill `gsw-core` (TCSlib, Lean 4.25.0, pinned Mathlib). The binding
brief is `/home/user/exchange/outbox/fills/gsw-core/brief.md`; read its sections *Targets*, *Published
interfaces*, *Proof routes and checkpoints* (your units), *Scope* and *Proof discipline* before you start.
Repository policy: `/home/user/gsw/policy.md` (sections on docstrings / proof sketches).
The lead integrates, commits and delivers. You **never** commit, push, run `lake`, fetch caches or
touch git branches; you only edit your owned files in your own worktree.

## Your environment

- Worktree `/home/user/gsw-<X>` (X = your letter), own olean tree `/home/user/gsw-<X>/.lake/tcslib-check-oleans`
  (already bootstrapped at the base), `.lake/packages` symlinked read-only to the lead's.
- Check one module (from anywhere):
  `/home/user/tools/chk.sh /home/user/gsw-<X> TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/<File> <LOG>`
  It runs `scripts/lean_check_tree.sh` under the **host-wide lock** (one Lean process at a time for all
  agents) and prints exit / error count (both `error:` and `error(` forms) / sorry warnings. Write every
  log under `/home/user/exchange/inbox/fills/gsw-core/evidence/subagents/<X>/logs/` (numbered, e.g.
  `noise-017.log`); never delete logs. Never call `lean`/`lake` any other way; never use timeouts.
  If your file is a dependency of your other file (Gadget → Noise), re-check the upstream file first
  so the downstream one sees its new olean.
- Exploratory scratch files: put them under `/home/user/gsw-<X>/probes/` (inside the worktree root,
  required by Lean) and check them with the same `chk.sh` (module path `probes/Foo`). Keep them.
- Rule 10 seal check of a file (run it on your files before reporting; must give `errors=0` on the
  coe-A variant, and should on all four):
  ```
  cd /home/user/gsw-<X> && rm -rf probes/seal-<File> && \
  python3 -I /home/user/tools/seal.py prepare probes/seal-<File> sub TCSlib/.../GSW/<File>.lean && \
  python3 -I /home/user/tools/seal.py run probes/seal-<File> /home/user/gsw-<X> /home/user/gsw-<X>/.lake/tcslib-check-oleans
  ```
  Copy the resulting probe dir's `results.jsonl` and logs into your evidence folder when done.
- Search: `grep -rn` over `/home/user/gsw/TCSlib` and `/home/user/gsw/.lake/packages/mathlib/Mathlib`.
  Use `#check`/`exact?`/`simp?` in probe files to find Mathlib names. Run Python only as `python3 -I`.

## Hard rules (violations are major findings)

1. **Frozen statements.** Every declaration already in your files keeps its header byte-identical
   (everything up to the `:=`/`by` that starts the proof) and its order; every `def`/`abbrev`/reader
   (`_eq`, `_apply`, `_iff`, `chain_nil`, …) stays byte-identical *including its body*. Delete nothing.
   Do not touch `variable`/`section`/`open`/`set_option` lines, the module title, the copyright header.
   You may only: (a) replace a target's `sorry` body; (b) rewrite the target's `**Proof sketch.**`
   paragraph so it describes the delivered proof (the statement prose before it stays byte-identical);
   (c) add auxiliary lemmas *before first use* (prefer `private`; a public one needs a docstring stating
   its formula, arguments in Lean order, and then a line under the module docstring's `## Main results`);
   (d) add precise `import Mathlib.…` lines (tell the lead: a new Mathlib root needs a cache fetch by the
   lead — ask before relying on it). Never weaken a statement or add a hypothesis. Do not edit any other
   file. Never add `@[simp]` or any global attribute. No new `def` is expected.
2. **Rule 10 (definition sealing).** Read every definition from **another file** only through its
   published readers (`gadget_apply`, `lift_apply`, `decompose_apply`, `decomposeVec_eq`, `digit_val`,
   `mul_eq`, `nand_eq`, `encrypts_iff`, `secretVector_eq`, `Regev.augmented_eq`, `LWE.noisyValues_apply`,
   …; table in the brief). The owned files are foreign to each other (Noise must read `gadget`, `lift`,
   `decompose` only via Gadget's readers; Scheme reads `Encrypts` only via `encrypts_iff`, `mul` via
   `mul_eq`). A file may unfold its **own** definitions. Projections of structures and the reducible
   abbreviations `Parameters.columns`, `Ciphertext` are notation (free). The seal check above detects
   implicit unfolding of foreign TCSlib defs (`rfl`/`change`/`show`/defeq abuse fails when sealed).
   **Core/Mathlib definitions** (e.g. `Matrix.vecMul`, `Matrix.mulVec`, `dotProduct`, `Bool.toNat`,
   `Fin.snoc`, `List.getD`) may reduce inside `rfl`, `decide`, `show`/`change`, but must never be named in
   `simp [...]`, `rw [...]`, `unfold`, `delta`, `dsimp [...]`: use their lemmas instead
   (`Matrix.vecMul_apply`? check names; `Matrix.mulVec`→`Matrix.mulVec_eq_sum`/`Matrix.mulVec`-lemmas,
   `dotProduct` lemmas, `Bool.toNat_true`, `Fin.snoc_last`, `Fin.snoc_castSucc`, …). An explicit-unfold
   scan will flag any foreign TCSlib definition name inside `simp/rw/unfold` selectors.
3. **Style.** Every line ≤ 100 characters. Every proof of ≥ 15 lines carries a `**Proof sketch.**`
   paragraph in its docstring and step comments (`-- Step 1: …`) for long proofs. Use the Greek `μ`
   (U+03BC). Keep proofs robust (prefer explicit `rw`/`simp only [...]` lists; `simp?` to pin lists);
   avoid `decide` on big goals, avoid heartbeat-heavy `aesop`/`omega` loops on huge terms.
4. **Duplication.** Search before writing any lemma. Reuse published lemmas (the brief's table,
   `LWE.binaryErrorSum_bound`, `Lossy.gadget_mulVec`, `Lossy.digits_val`, `Regev.*`, Mathlib). For every
   auxiliary lemma or inline `have` that restates/specializes/re-proves existing material, record its
   nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
   Never copy a `private` lemma from another file silently.
5. **Sources.** Do not add new source tags or quotations; new helper lemmas are glue (no tag).

## What to return (final message to the lead)

- The final contents are in your worktree; the lead copies them. Say which targets are proved, which
  (if any) are not and the exact remaining obligation, with the last check log and seal results.
- A list of new auxiliary declarations (name, private/public, one-line statement).
- The *Overlap and reuse* notes and the searches (rule 4).
- Any target you believe false or any route that failed: stop that line and report the exact
  obligation; do not work around it by changing statements.
- Also write all of this to `/home/user/exchange/inbox/fills/gsw-core/evidence/subagents/<X>/REPORT.md`
  and keep a running `WORKLOG.md` there (timestamped notes of what you tried).
