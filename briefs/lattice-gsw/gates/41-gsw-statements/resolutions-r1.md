# Gate 41 · resolutions, round 1 · CLOSED by disposition

Codex:
- **#332, the DAGCircuit readers:** CLEAR, 0/0/0/0.
- **#333, GSW:** HOLD, 0/1/3/2.
- **Findings:** `findings/gate41-gsw-statements-findings.md`, SHA-256 `f9d90b3545a63ce438dab5e9889d39639cf775443304fc12c3c0d10727497bf6`. The evidence ZIP was not supplied.
- **Audited heads:** #332 `94eae71b` and #333 `48d796a8`; records `86d19094`; exchange `c72de14a`.

**Mathematics.** All 35 GSW targets are accepted as true with the hypotheses they display. That covers:
- the asymmetric `Nβ₁+|x₁|β₂` bound and the chain bound `β₀+kNβ`;
- `homAnd` and `homGate`, at arities 0, 1 and 2;
- the depth bound `(N+1)^depth·β`;
- the decryption separation, including odd `q` and `q` = 2 or 3;
- the leveled condition, which needs no extra factor and no `L+1`;
- the column-LHL hybrid, and IND-CPA as two DLWE advantages plus `2Nε`.

The two #332 proofs (`getD_lt_depth`, `runWith_rel`) are sound. `runWith_sim` can be derived from `runWith_rel`. The phase-6/7 hooks fit BV14: a selector step costs an additive `2Nβ`.

| # | Severity | Disposition |
|---|---|---|
| G41-01 | major | **Closed by Seyoon's explicit superseding disposition.** Ruling of 2026-11-16, made after this gate's pin and recorded as **DW-7** in `briefs/pass-shelat-ch5-8/deferred-work.md`: the GSW13 ingest from Q14 is deferred in the same way as pairings Q12, to Markdown transcriptions of only the passages used, added later. Seyoon also ruled to close this gate by disposition. |
| G41-02 | minor | **Fixed.** `homAnd` is described as a right-associative product chain, with each head multiplied on the left. Fixed in commit `486f44f8` (LE-gate41, docstring only). |
| G41-03 | minor | **Fixed** in the same commit. `eval_encrypts` now states output correctness, with the every-vertex invariant described as an intermediate step. The code is identical once doc comments are stripped, and the widest line is 95 characters. |
| G41-04 | minor | **Fixed (records).** `plan-section.md` now uses the `AdvancedEncryption/Homomorphic/GSW/` paths, with a status note. |
| G41-N1 | note | Extending the scoped Pei16 Markdown is part of DW-7. |
| G41-N2 | note | The #333 PR description's Gadget summary is corrected. |

Codex also noted that AP14's printed `gᵀ⊗I_n` differs from the code's `I_n⊗gᵀ` by a column permutation. The code matches AP14's block-diagonal description and Pei16. This is not an undisclosed change.

**Gate 41 is CLOSED** (Seyoon's ruling: close by disposition, no round 2).

**Merge conditions:**
- Merge #332 before #333.
- After the merges, rebuild the downstream of `DAGCircuit`: 281 modules for #332 and 291 for #333.
- Whichever of #331 and #333 merges second takes the union of the `AdvancedEncryption.lean` and `TCSlib.lean` facades.
- Rebuild the modules shared with #324 and #327 (16 and 41 modules).
