# Stage 2, PROG-2 and PROG-3 statement gate: resolutions

**Gate:** `audits/stage2-statements-pack.md`; bundle `audits/stage2-statements-bundle.md`, SHA-256
`28b7f2c805088d35209cb67a1c652d2e8d7087b4bbba2a360dd5216df9354191`, 82 sections.
**Findings:** `audits/stage2-statements-findings.md`, verbatim.
**Verdict: CLOSED in round 1 (2026-10-14): 0 blockers, 0 majors, 4 minors, 12 notes.** No proposed
theorem is false. The auditor approved the homes, the namespace `WordRAM`, the topic
`Complexity/RAMSimulation/` and `initMem` (N10).

| # | Severity | Finding (short) | Resolution |
|---|---|---|---|
| F1 | minor | `stmtdiff.py` keyed declarations by their last name component, so four were dropped from the draft comparison | Accepted. The corrected totals are the auditor's: Stage2 52 identical, 5 changed, 0 missing, 2 added; LanguageExtensions 38, 1, 0, 3. The four dropped declarations are unchanged. Future comparisons key by qualified name and reject duplicate keys. The landing PR's freeze and replay are the evidence that the landed statements are the gated ones. |
| F2 | minor | Attribution: the published alternative BPP definition is [AB09] Definition 7.3, p. 126, not 7.4; Exercise 1.9 uses a symbol array, not a bit array | Accepted. At landing, `exists_simulation`'s deviation paragraph says "symbol array". `Randomized/Classes.lean` (maintainer-owned, chapter-7 campaign) cites "Def 7.4" in five places. The maintainer checks the published edition, the campaign's reference copy, at p. 126, and makes a comment-only fix PR. `acceptProb`'s citation of §7.1 is sound as proposed. **Done (2026-10-14):** p. 126 confirms Definition 7.3. The check found the whole chapter-7 campaign numbered after the 2007 web draft: 113 of 160 chapter-7 citations, 125 lines in 17 maintainer files, renumbered by PR #89 (comment-only); `Classes.lean` alone had eight "Def 7.4" citations, not five. The colleague-owned `CircuitComplexity` citations went to the user to relay. |
| F3 | minor | `XExec.bounded`'s new premise `1 ≤ lim.word` is not supplied by `XFits` or the input-length premise (counterexample: word 0, empty input, a true coin) | Accepted, as a **PROG-2 integration obligation** (backlog PROG-2). The edited compiler must supply `1 ≤ lim.word` at the existing simulation calls (`Compiler/Simulation.lean:277`, `:356`), as a compiler invariant or premise, or use a separately proved enlarged invariant. It is not inferred from `input_le`. The theorem itself is correct. |
| F4 | minor | The name and cited-name screens are narrower than their wording | Accepted. The populations are exactly: explicit source declarations (`names.py`), and backticked tokens matched by its regex, with lowercase unqualified tokens without underscores excluded (`cited.py`). Later packs state the population exactly, or use environment-based enumeration. No collision or unresolved dependency was found. |

**Rulings recorded** (N7–N10, §§9–12 of the report):
- the slice lemmas are true as stated, and MIG-0b needs no contract-level variant now;
- B1/B2 (PROG-3 for compiled code) may land now against the current compiler, with an obligation
  to re-gate their extended forms at PROG-2, or with PROG-2. The old forms must not be advertised
  as the extended compiler's theorem;
- `acceptProb` is better in a Complexity-side module, keeping its `Light` namespace;
- the mirror-only bridges stay evidence;
- landing must use the explicit landing-name map, not "delete the X";
- B1/B2 keep their upstream file contents and headers, with local-modification notes.

Recommendations for PROG-2 (N8): an `EndsIO.append` convenience lemma and the derived
loop-invariant rules; and a compiler connection that uses streams at least as long as the cost
bound, or explicitly false-pads them.
