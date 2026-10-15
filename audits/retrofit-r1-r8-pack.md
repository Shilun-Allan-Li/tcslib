# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 8

Round 7 (`audits/retrofit-r1-r7-pack.md`, findings verbatim in
`audits/retrofit-r1-r7-findings.md`) closed R6-1. It accepted the 318/423
Catalog census, its spans and strict subtotal, and the in-file convention.
It held the gate on:

- **R7-1**: three sources of printed `MEMBER` pairs were missing from the
  source-side union, because the union had been assembled by hand from
  each target's best match;
- **R7-2**: the extractor's and pass 3b's scope was described imprecisely.

**What changes this round.** Every major since round 2 has had the same
cause. A per-file count was assembled by hand from evidence that was itself
correct, and the hand step lost something. This round removes the hand
step. The script's new **pass 4 generates every file's member set by
name**, and the ledger's rows quote that output. The completeness claim
being audited is therefore narrow and checkable:

> The ledger's per-file member sets are exactly what pass 4 prints: the
> stated historical rules, plus the source and target of every like-kind
> cross-file pair meeting the stated rule, over the stated populations.

## Disposition table (verify each)

| Round-7 finding | Disposition |
|---|---|
| R7-1 (major: three uncounted sources) | **Repaired by generation.** Pass 4 applies the like-kind rule to **all 423** Catalog declarations, not only the non-members, against all five source files: 537 like-kind MEMBER pairs. Every pair contributes its source. The historical rules are written out by name in the script: f2_-twins, the `a2_loop_halted_run` twin, the relocation family, the 13 H3 copies, the counter block and `catalog_` twins. Pass 4 reproduces your three additions (`controlCfg_run`, `emCall_right_run`, `exists_emitLoopTM`). It also finds **24 more** under your R7-1 principle, applied to the whole population (Primitives 16, Loop 7, Wrappers 1). These are source declarations that a Catalog twin of a *sibling* declaration reproduces by more than half. Two are Loop's H3 near-copies `emLoopHost_init` and `emLoopHost_anchor_return`, previously "noted, uncounted"; they now count through the cross-file path. Catalog is unchanged at 318. |
| R7-2 (minor: extractor and pass 3b scope) | **Fixed.** `proof` handles equation-style definitions and inductives, using the text from the first depth-0 `|` or `where`. Pass 3 labels the population exactly: 553 source declarations, 542 with an extracted body of at least 25 characters. The other 11 are genuinely shorter, which matches your count, and no verdict changed. Pass 3b carries the kind guard: **107 like-kind pairs over 62 targets, 12 at 90% or more, plus 2 restatements**, reproducing your figures. The membership rule, with its in-file exception, is now stated once, in one sentence, in the ledger. |
| R7-3 — R7-6 (closures, the accepted convention) | Carried. |

## The generated census (verify against the script output)

| File | Members | Fraction | Lines |
|---|---:|---:|---:|
| `Build/Catalog.lean` | 318 | 75.2% (strict 283) | 7,539 |
| `Build/Primitives.lean` | **173** = 150 historical + 23 from pairs | **63.6%** | **3,790** |
| `Build/Loop.lean` | **117** = 104 historical + 13 from pairs | **55.2%** | **3,153** (with your exact 504-line H3 measurement) |
| `Build/Wrappers.lean` | **19** = 17 historical + 2 from pairs | **65.5%** | **355** |
| `TuringMachine/Composition.lean` | **6** | **31.6%** | **109** |
| `ClassP/TimeConstructible.lean` | 20 | 95.2% | 355 |

The spans of the 24 new source-side members are printed by pass 4: 375
lines in Primitives, 159 in Loop, 18 in Wrappers.

## Brief for the auditor

1. Run the attached script (`--spans`) against the attached sources. Confirm
   that its output equals the attached `.out`.
2. Verify that pass 4 implements the stated rule and historical rules. In
   particular, check that the historical name lists match the round-1 to
   round-7 accepted families. Verify that the ledger rows quote pass 4's
   counts.
3. Spot-check the 24 new source-side members: sample at least five pairs
   and re-tile them.
4. Judge whether any omission remains *within the stated rule and
   population*. An omission inside that scope is a generator bug; name it.
   Material outside it, meaning other files or adaptations restructured
   below the 25-character tile, is a scope note, not an omission.
5. Report in the standard table, with findings verbatim into
   `audits/retrofit-r1-r8-findings.md`. The gate closes on zero blockers and
   majors, retiring epoch R1 and arming 12.2c.

## Repository-side attestations

Documentation-only delta in the screened files. Since round 7, the branch
has integrated the zone-f1 A2/B2/C2 deliveries, which do not touch any of
the six screened sources; their byte identity to the round-7 bundle is
attested and recomputable from git.
