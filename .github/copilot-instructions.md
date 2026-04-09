# Copilot instructions for TCSlib

## Big picture
- This is a Lean 4 monorepo with three publishable outputs:
  - Lean library (`TCSlib/**`, exported by `TCSlib.lean`).
  - Blueprint site + PDF (`blueprint/src/**` built via `invoke`).
  - Public website (`webpage/**` with Verso; deployed into `site_root/`).
- Content is organized in two math domains mirrored across Lean + blueprint:
  - `BooleanAnalysis/*`
  - `ErrorCorrectingCodes/*`
- CI assembles final Pages output from 3 artifacts (Lean docs, blueprint, Verso site) in `.github/workflows/push.yml`.

## Build and verification workflows
- Lean build (local baseline): `lake exe cache get` then `lake build`.
- CI/dev docs build uses `-Kenv=dev` to enable `doc-gen4` from `lakefile.lean`:
  - `lake -Kenv=dev build TCSlib`
  - `lake -Kenv=dev build TCSlib:docs`
- Blueprint build:
  - install deps from `blueprint/requirements.txt`
  - run `inv all` from repo root (uses root `tasks.py` + `blueprint/tasks.py`).
- Verso website build: `cd webpage && lake exe generate-site`.
- Quick local static preview of Verso site is scripted in `build_local.sh`.

## Project-specific coding conventions
- Never use broad `import Mathlib`; CI lints this explicitly. Use precise module imports.
- Keep theorem files in existing namespaces:
  - `namespace BooleanAnalysis` in `TCSlib/BooleanAnalysis/*.lean`
  - `namespace ErrorCorrectingCodes` in `TCSlib/ErrorCorrectingCodes/*.lean`
- Prefer adding reusable helper lemmas to `Basic.lean` files when they are foundational (example: entropy/domain lemmas in `ErrorCorrectingCodes/Basic.lean`).
- Preserve existing style: docstrings (`/-! ... -/`), scoped notation declarations, and `@[simp]` lemmas near definitions.

## Cross-component integration points
- If Lean declaration names change, verify blueprint references with `inv check` (parses `.lake/build/doc/declarations/*` vs blueprint dep graph).
- Blueprint chapter files in `blueprint/src/chapter/**` should stay consistent with theorem/module naming in `TCSlib/**`.
- Website static assets come from `static_files/**` and are mounted in `webpage/Main.lean` (`static "static" ← "static_files"`).
- Docs/blueprint/webpage are merged at deploy time; avoid hardcoding paths outside `/tcslib/...` URL prefix.

## AI agent workflow tips for Lean edits
- For proof iteration in editor, use Lean InfoView goal states first; reserve full `lake build` for integration checks.
- Make minimal, local proof changes; avoid large rewrites across many theorem files unless explicitly requested.
- When adding a new topic file, update `TCSlib.lean` exports so downstream users import it by default.
