# Efficiency remediation, wave 1 (rulings Q11 A, Q7 B, Q8): staged fill briefs

Records only, prepared 2026-11-18 at records tip `b1219429d8e2a15cb71f44454eaeb6a8f6d55220`. Inputs:
`../audit-r1.md` §5, `../rulings-r1.md`, `../inventory-r1.md`, handoff §2 (rule 15). Every job: Claude fill
route, delivery to `inbox/fills/<unit>/` on `exchange/pass-shelat-ch5-8`, rules and checks in `COMMON.md`.
Bases: **REC** = `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62` (snapshot #10 Lean = records tip's Lean);
**IO** = `iO/phase-a-base` `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (REC + #374, #378, contract `8e01b720`, #380).

| Job (folder) | Unit | Content | Size (new lines) | Base | Depends on | Questions |
|---|---|---|---|---|---|---|
| EF-H1 | `ef-h1-arith` | 8 `ArithmeticFP` fields incl. `xgcd` (extended Euclid: a Fermat inverse does **not** fit the field's spec, which covers every modulus); `PrimesInP`, `ArithmeticFP.ofPrimesInP`, `ArithmeticFP ↔ PrimesInP`; new files only | 900–1,600 | REC | — | Q-H1-1 |
| EF-D1 | `ef-d1-lattice-families` | `LWE.EfficientFamily`, `SIS.EfficientFamily` (uniform parameter map; noise in `SamplesEfficiently` form), schedule constructors, non-vacuity instances | 350–650 | IO | — | — |
| EF-D4 | `ef-d4-ltdf-interfaces` | `LossyTDF`, `ABOTDF` with uniform generators and polytime eval/inv as fields; predicates over `NUPPT` (statement job; Codex gate after) | 300–500 | REC | Q-D4-1 A: [PW10] §3 ingestion first | Q-D4-1 |
| EF-R2-R3 | `ef-r23-regev` | general-mod-`q` vector toolkit; Regev symmetric and PKE: proved `NUPPT` reduction machines (`RealizesOn`) and asymptotic security from `DLWEAssumption` | 1,100–1,900 | IO | — | Q-R-1, Q-R-2 |
| EF-H4 | `ef-h4-sis-crh` | `CRH` from a dyadic `SIS.EfficientFamily`; compression; CR from `SISAssumption` via the existing machine; dyadic instance | 400–750 | `<BASE>` = EF-D1 final | **EF-D1** | — |
| EF-H11 | `ef-h11-sharing-bgw` | efficient secret-sharing interface (prime `p`, `n` listed parties), Shamir instance, efficient resharer and BGW gate steps | 1,800–3,500 | IO | — | Q-H11-1, Q-H11-2 |
| EF-H12 | `ef-h12-levin-3col` | `LevinNPHard L3COL R3COL` via [AB09, Lem 6.10, 6.11] (public) and 3SAT → 3COL (`SATtoColorReduction`), padding; unconditional ZK-for-NP corollaries | 2,000–3,800 | REC | — | Q-H12-1, -2, -3 |

Total 6,850–12,700 new lines (±40%). **No job edits an existing non-facade file.**

**File disjointness (checked mechanically, 2026-11-18).** Every job's files are disjoint from each other,
from cleanup Stage 2 (`scope.tsv` + `s2a-items.tsv`: 203 owner paths; branch `cleanup/stage2-s2a` head
`c119a3c4…`: 26 Lean paths), from #376 (`04ba2446…`) and #377 (`7563734a…`), and from every
`complexity/arora-barak-*` and `codex/ab34-*` (Ladner) diff (252 paths, none under `TCSlib/Cryptography/`).
One exception, handled: the facade `LWE.lean` is changed by #377, so EF-D1 does not edit it; the maintainer
adds `import TCSlib.Cryptography.LWE.Efficient` at landing.

**Parallelism.**
- **Now, in parallel (6 workers):** EF-H1, EF-D1, EF-R2-R3, EF-H11, EF-H12, and EF-D4 (once Q-D4-1 is
  answered; under A after the §3 ingestion). **Then** EF-H4 on EF-D1's accepted final.
- **Lean processes.** Local hosts: at most **3 per machine across all jobs** (S2-A may already hold slots),
  one per olean tree: at most three single-process wave-1 workers on one machine, coordinated by
  messaging. Cloud workers: a memory-sized pool each (addendum *Lean parallelism*; `workflow.md` §4.1 as
  quoted there). Recommended: cloud for EF-H12, EF-H11, EF-R2-R3, EF-H1 (large, sub-agents); EF-D1, EF-D4,
  EF-H4 fit one process on a local host.

**Landing notes (not dispatch blockers).** IO jobs (EF-D1, EF-R2-R3, EF-H11, EF-H4) land after #374,
#378, #380 merge (or as stacked PRs). `CoinSampling/Contract` (`foundations/coin-contract` `8e01b720`) has
**no PR** (Q-W1-1). Replay risk only (imports, never edits): S2-A's proof-level changes to `Randomized/PPT`,
`Games/Efficiency`, `Asymptotic/{Ensembles,UniversalLemmas}`; the Arora–Barak ch. 3–4 branch's changes to
`ClassP/BinaryArith/{Div,ModPow,Mul}`, `CircuitComplexity/*`, `ClassNP/SAT`, `CookLevin/Hardness` (EF-H1, EF-H12).

## Questions for Seyoon (recommended option first)

- **Q-W1-1** Contract PR: **A** open a PR for `foundations/coin-contract` (stacked on #378) now · B land it
  inside the first IO job's PR.
- **Q-H1-1** `PrimesInP`: **A** `Randomized.PRIMESBin ∈ Complexity.P` (bridge to `primeStr` proved) · B
  `PolyTimeComputable primeStr`.
- **Q-D4-1** [PW10] §3 definitions are not ingested (pages 33–39 only): **A** ingest §3.1–§3.2 before
  dispatch · B cite by section, disclosed.
- **Q-R-1** **A** one worker for EF-R2 and EF-R3 (shared toolkit, three series) · B two workers, EF-R2 on
  EF-R3's head.
- **Q-R-2** **A** general modulus `q` · B dyadic families only.
- **Q-H11-1** **A** Shamir + resharer + BGW gate steps now; whole-circuit evaluator only on a registered
  host · B Shamir only now.
- **Q-H11-2** inverses mod `p`: **A** Fermat via `BinArith.powMod` (precedent `DetMod`) · B wait for EF-H1's
  `xgcdStr`.
- **Q-H12-1** route: **A** through circuits ([AB09, Lem 6.10, 6.11], public) · B direct §2.3 tableau (needs an
  Arora–Barak-side publication of private Cook–Levin internals).
- **Q-H12-2** AB09 ch. 2/6 and a 3-colouring source are not ingested: **A** maintainer ingests them before
  the delivery review · B in-repo anchors and course material only.
- **Q-H12-3** explicit colouring (`sat3Coloring` is private): **A** re-derive, disclosed (file stays
  read-only) · B a two-declaration owner PR in `NPReductions/ThreeSATToColoring.lean`.

**Not yet ready to dispatch — the records commit that files this folder (`<RECORDS>`) is pending, and the
questions above need answers or acceptance of the recommended options (Q-D4-1 A also needs the ingestion;
EF-H4 also waits for EF-D1).**

**Update (2026-11-18, overnight):** [PW10] §3.1–§3.2 (pp. 14–15) are ingested (`EF-D4/ingest-report.md`); EF-D4 is ready to dispatch once its `<RECORDS>` pin is filled. One morning question for Seyoon on EF-D4: PW10's lattice constructions meet only an *almost-always* correctness/lossiness, while the brief's interface is exact (see the ingest report, item 1).
