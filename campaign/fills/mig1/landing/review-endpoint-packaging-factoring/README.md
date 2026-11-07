# T5 canonical endpoint packaging — inert proposal

The proposed Catalog refactor passes complete native elaboration and the
scoped 45-definition seal. **It has not been applied to actual source.**
Root owns adoption after the original replay, WordSize's line-pointer
refresh and subsequent combined validation. This bounded result is not
gate/replay/merge clearance or approval of any pending API/home proposal.

Apply [proposal-v2.diff](proposal-v2.diff) to the captured Catalog SHA256
`cfc4365531fade3b5f5e358f0285d4792b239412bc2f1ac662673fdc5f54fb73`.
The complete result is `Catalog-proposed-v2.lean.txt`, SHA256
`a55066f71a5c94f27c8767e0cdada2baabcb65ee7c3c59a14e8bc58ffaceacba`.

One new **private proof lemma**, `Turing.catalog_ofWords_with_tapes`, proves
configuration extensionality once: changing a canonical seam's state and
replacing its tapes by pointwise canonical tapes gives the canonical seam
for the new words. It uses the public `Cfg.ofWords` field readers. Both
existing endpoint bodies apply it and retain only their distinct per-cell
cases and the already shared `catalog_buffer_clip`. No machine, host,
data definition, public API or import is added.

`freeze-v2.json` checks all **146** existing declarations: all headers,
docstrings, visibility and relative order remain literal; all other
declaration chunks remain byte-identical. Only the two endpoint proof
bodies change. Public declarations remain **107→107**, private **39→40**.
The independent undo check restores every original source byte. Nested
`input := x` and record-field assignments in headers are handled by the
balanced delimiter, rather than split at the first assignment.

Six actual managed Lean invocations used the complete read-only
`oleans-mig1-preflight-current2` tree, one process at a time:

| Evidence | Result |
| --- | --- |
| Private helper alone, 45 definitions opaque/defaults3 removed | PASS, `helper-sealed-v1.json` |
| Full intermediate Catalog after transfer repoint | PASS, `transfer-sealed-v1.json` |
| Full final proposal, three individually guarded regions | PASS, `complete-sealed-v2.json` |
| Exact final full source with unchanged production imports | PASS, `complete-native-v2.json` |
| Verbatim reused 90 positive examples, freshly run on current2 | PASS, `controls-unsealed-current2.json` |
| Same controls with each of 45 definitions sealed in isolation | Expected exit1, exactly 90 mapped `rfl` failures, `controls-sealed-current2.json` |

Each final guard begins **before its docstring/header**, suppresses the
three existing definition simp attributes, and restores them outside that
region. Removing instrumentation restores the complete proposal exactly.
This seals only the new helper and two changed endpoints, not legacy
Catalog or its three pending HOLD rows. `Cfg.ofWords` and `bufferTape` are
the ordinary foreign definitions directly named in these statements or
proofs; the existing eligible45 guard conservatively covers the wider
model/witness vocabulary. No transparency override is used.

Fresh recursive axiom prints give `{propext, Quot.sound}` for the helper
and `{propext, Classical.choice, Quot.sound}` for each endpoint. The
controls' source reuse is explicit in `controls-source-reuse.json`; their
executions here are fresh. Every negative diagnostic maps exactly once to
its definition/mode, and the checker rejects three corrupted variants.
The full native run retains 28 warnings, all outside these three affected
declarations in byte-unchanged legacy chunks; none is suppressed.

`verification.json` checks all six commands/log hashes, exact guard/undo
restoration, actual Catalog unchanged, watched snapshot oleans unchanged,
and the prior screen folder's **120-entry manifest untouched**. All input
copies, raw logs and intermediate versions remain. No failed proof attempt
occurred; the negative controls are deliberate. No compiled output,
source/Git/cache/shared-snapshot mutation or screen was performed here.

This proposal moves the existing lengthBits space-row line **2021→2033**;
`line-pointer-note.json` records it. Root refreshes WordSize's comment
after all source proposals are adopted. `SHA256SUMS` covers this frozen
folder except itself. The combined chain, current head screen, census and
gate remain root's work.
