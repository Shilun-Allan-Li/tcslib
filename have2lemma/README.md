# Have hygiene and have→lemma extraction

Two things are done here, both by `TCSlib/Tactics/Haves.lean` through `scripts/haves.py`:

1. **Removing unnecessary haves** (`clean`).  Mechanical proof writers pad proofs with
   `have h : T := by …` followed by `exact h`, with `have h : goal = P := rfl; rw [h]`
   where `change P` was meant, and with haves nothing ever uses.  Each is decided on
   the elaborated proof term, applied, and verified by re-elaboration.
2. **Turning a substantial have into a named lemma** (`extract`), per the triage below:
   the lemma is placed before its theorem with a parameter list computed from the
   dependency closure of the have's type and proof, and the have's proof becomes a call,
   so every later use of the name is untouched.

```
python3 scripts/haves.py test                       # fixture suite (Mathlib-free, ~3 min)
python3 scripts/haves.py scan FILE                  # facts about every have
python3 scripts/haves.py clean FILE... [--write]    # diff, or rewrite in place
python3 scripts/haves.py extract FILE DECL:HAVE[@LINE]:NAME ... [--write] [--private] [--doc TEXT]
python3 scripts/haves.py census [DIR ...]           # removable haves per file
python3 scripts/haves.py manifest FILE...           # triage manifests (stage 1 below)
python3 scripts/haves.py queue [--file F] [--write] # convert the queued manifest entries
```

The Lean side (`lake env lean --run TCSlib/Tactics/Haves.lean …`) elaborates the file
in-process with info trees, so it sees each have's elaborated type, its proof term, the
goal it was proved under, where its name is used, and its exact source range.  It
rewrites the text and re-elaborates the result; a file is written only when no new
error appears.  The target file's imports must be built; nothing else is compiled, and
no `lake build` is run.  One run costs one or two elaborations of the file (seconds for
a small file, a few minutes for a heavy one).

## What `clean` does

| Shape | Decided by | Rewritten to |
|---|---|---|
| `have h : T := p` never used | `h` absent from the rest of the proof term *and* from the source after the have | deleted |
| `have h : T := p` then `exact h` (or `assumption`), no other use | the rest of the proof term is literally `h` | `p`'s tactics, behind `show T` when `T` is not the goal up to binder names (a term `e` becomes `exact e` or `exact (e : T)`); the have's own binders become an `intro`; under a `·` when the have closed one of several goals. When verification fails, a second attempt keeps the have's exact elaboration order: `exact (e :)` for an untyped term, `refine (?_ : T)` for a block (`show` unifies `T` with the goal first, which can change what `dsimp` sees) |
| `have h : A = B := rfl` then `rw [h]`, goal is `A` | the proof is `rfl`, `h` used once | `change B`, plus `rfl` when the `rw` closed the goal |

A have whose name occurs in the text but not in the term (`nlinarith [h.le]`, `simp [h]`
where the certificate did not need it) is reported as `hintOnly` and left alone: its
line is not the author's claim, but removing it would still break the text.  `clean`
iterates until nothing changes, since a have used only by a deleted have is unused in
the next round; an edit that fails verification is reverted and remembered, and the
others are kept.

## Triage pipeline for extraction

```
/have-triage <file|folder>
  1. python3 scripts/haves.py manifest FILE   → manifests/<Module>.json   (elaborated facts per have)
  2. lean-have-judge agent                    → verdicts in the manifest  (extract / keep-inline / replace-with-mathlib)
  3. lean-have-primer agent                   → QUEUE.md                  (one line per queued conversion)
/have2lemma-run [FILE]
  4. python3 scripts/haves.py queue --write   → converts `status: "queued"` entries, marks them converted/failed
```

Stage 1 is the tool, not an agent: the facts a judge needs (type, use count, dependency
names, whether the proof is one automation call) are read off the elaboration, not
guessed from the text.  The manifest is the contract between stages; re-running stage
1 keeps the judging fields of entries whose declaration, name and type text still match.

### Manifest entry

Fields from `scan`, then the judge's:

| Field | Meaning |
|---|---|
| `haveName`, `anonymous`, `destructuring` | the name (`this` when anonymous; `⟨…⟩` for a pattern have, never a candidate) |
| `declaration`, `line`, `column`, `endLine`, `bodyLines`, `nestingDepth` | position; depth counts enclosing haves |
| `typeText`, `binders`, `typeElab` | the stated type as written (null when inferred), the have's own binders, the elaborated type |
| `valueIsTerm`, `singleTacticClose`, `nextTactic` | proof shape; the tactic name when the proof is exactly one tactic |
| `useCount`, `textRefs`, `unused`, `hintOnly`, `exactAfter`, `rflEq`, `typeIsGoal` | usage, from the term and from the text |
| `localDeps`, `sigDeps` | hypotheses the type and proof depend on (closure); those bound by the theorem's signature |
| `inaccessibleDeps`, `letDeps`, `recursiveDeps` | unnamed hypotheses (`a✝`; extraction names them with a `rename_i` line before the have), `let`-bound and recursive-call dependencies (extraction refuses these) |
| `needsClassical`, `hasSorry` | the proof uses classical decidability; the proof has a `sorry` |
| `verdict`, `proposedLemmaName`, `mathlibExisting`, `rationale`, `confidence`, `needsNaming`, `status` | the judge's; `status` runs `scanned → judged → queued → converted \| failed` |

## Substantiality criteria (summary)

Extract only when most of these hold:
1. **Standalone meaning** — the type reads as a textbook-displayable fact outside the proof.
2. **Nontrivial proof** — multi-step body; NOT `bodyLines ≤ 1` and NOT closed by a single
   `simp/simp_all/omega/linarith/ring/norm_num/positivity/decide/aesop/exact/gcongr/field_simp`.
3. **Reusable** — used ≥2 times, or an instance of a pattern useful elsewhere in TCSlib.
4. **Clean lifted interface** — few lifted hypotheses (`localDeps`); none `let`-bound,
   which the tool refuses (an unnamed `a✝` is named automatically).
5. **Not already in Mathlib** — otherwise verdict is `replace-with-mathlib` (cite, don't duplicate).

Default when torn: `keep-inline`.

## What extraction produces

```
/-- Step `h_sum_pos` of the proof of `hoeffding_log_mgf_weak`, extracted as a lemma. -/
theorem sum_mul_exp_pos {n : ℕ} (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1) (ℓ : Fin n → ℝ) (η : ℝ) : 0 < ∑ i, p i * Real.exp (-η * ℓ i) := by
  …the have's own tactics…

  have h_sum_pos : 0 < ∑ i, p i * Real.exp (-η * ℓ i) := sum_mul_exp_pos p hp_nonneg hp_sum ℓ η
```

Parameters are the dependency closure in context order.  A binder from the theorem's
signature or a `variable` keeps its source text (`{V : Type*}`); a tactic-introduced one
is pretty-printed and checked by re-elaboration in the have's own context, walking a
ladder of printer settings (plain, coercions spelled out, no field notation, explicit)
until one round-trips -- otherwise the extraction is refused and says which binder to
state in the source first.  Implicit binders stay implicit when the call site can infer
them from the statement, instance binders are `[…]`, the have's own binders follow, the
type is the source text, the proof is the source text re-indented (with `classical`
restored when the have sat under it), and `open … in` prefixes of the theorem are
repeated.  A dependency on an unnamed hypothesis (`a✝` from a bare `intro` or a `cases`)
is handled by a `rename_i` line inserted before the have, giving it a fresh name the
lemma and the call use.  The keyword follows the file's majority (`theorem` or `lemma`); `--doc` gives
the docstring that policy.md §2 asks for (the default names the step and the theorem).

## Status legend (QUEUE.md)

☐ queued · ⏳ needs-review (low confidence — human veto before conversion) · ✔ converted · ✗ rejected/failed

## History

The first metaprogram here (`ExtractHavesFile.lean`, June–October 2026, 6,600 lines)
worked on source text: it re-elaborated probe strings through fallback ladders, kept
cross-run state in progress files, and aimed to convert every have of the library.
It was replaced on 2026-10-28 by the info-tree driver above, which reads elaborated
facts instead of guessing them, converts only what the triage asks for, and verifies
every rewrite before writing.
