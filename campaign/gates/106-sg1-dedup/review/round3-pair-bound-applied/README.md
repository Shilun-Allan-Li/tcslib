# Approved pair-bound application — validated checkpoint

**Not yet clear to merge: #215** — the new source passes native/scoped-seal checks; MSG6, current-head screen/comparison and external round3 remain deferred for resume.

Only the approved Hardness edit was applied in the SG1 worktree at base HEAD `d0c4a292e781b55617e05b33fdd423bb059fd735`: add `TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`, use the passed public joint-projection bound in `clA5Pair_sizes`, and update its adjacent sketch accurately. The resulting source SHA-256 is **`3c41a6aca1ed4e24b08330b7819a4d36ce0e695be4a71b11382c346e39499952`**.

Exact before/after sources and patch are retained. Source checking confirms the only changed declaration is that lemma; its bare header remains byte-identical. All definitions/tables, visibility, attributes, other proof chunks, and the relative order of the other imports are unchanged. The other15 repaired bodies are unchanged, including all five SAT repairs; SAT's complete source remains `682df0cd83abed16dac1e44768bee40a1691030eaeab1cf56373fa0677dbc6ba`. Both actual Hardness sources contain zero raw sorry tokens.

Executed sequentially through managed plain `leanelab.sh`, using complete read-only MSG5, local budget3/machine5:

- **Full exact-source native PASS:**161.04s, zero errors,66 warnings. The probe contains the complete actual source verbatim, followed only by metadata inspection.
- **Full-source all11 changed-Hardness-section seal PASS:**154.45s, zero errors,66 warnings. Each changed section has all21 existing foreign ordinary definitions irreducible before its docstring/header; the three model-definition default simp rules are disabled. Removing precisely the recorded section instrumentation recovers the native input byte-for-byte. Unchanged legacy sections are outside those guards.
- **All16 repaired roots plus seven generated descendants** have standard axioms, with identical native/sealed root/kind/AX maps. The full module's eleven local Hardness roots and the five unchanged compiled SAT roots are selected explicitly. Direct ordinary definitions reached by the Hardness repairs are within the21-name guard; no foreign private reference is used. Complete metadata is retained.
- **Fresh42 controls** in the exact seven-import context pass unsealed and fail sealed with exactly42 definition/mode identities and errors. The checker also rejects four malformed evidence cases. The earlier hypothetical four-definition/eight-control proof remains separate evidence and was not substituted for this calibration.

The new pair-bound proof uses only the published inverse, joint bound and projection equations. Its `change` step reduces only the same-home header definitions. No foreign ordinary definition is an unfolding argument. SAT's previous seal is adopted by unchanged source/import bytes as root authorized; no fresh SAT seal or blanket legacy seal is claimed.

The initial preparation assertion incorrectly assumed an NP import in the old control harness. It stopped before any Lean run; that preparation failure and the four missing-runner Python calls are recorded. The corrected harness uses the actual complete import context. All four subsequent Lean jobs finished; the negative-control exit1 is expected.

All prior frozen evidence manifests and payloads were reverified unchanged. No Git commit/push, screen, snapshot/cache write or MSG6 replay occurred here. Following the relocation/pause instruction, **no further probe or replay will be launched**. Source and evidence are stable for root's commit/push checkpoint; the full chained Hardness-downstream replay from MSG5 and refreshed head evidence remain queued for resume.
