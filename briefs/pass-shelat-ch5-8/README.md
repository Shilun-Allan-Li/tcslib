> **Maintainer hand-off (2026-11-07): start with [`MAINTAINER-HANDOFF.md`](MAINTAINER-HANDOFF.md)** (and `AGENTS.md`/`CLAUDE.md` in this folder). The text below is the original 2026-11-04 planning note, kept for history.

# Pass–shelat ch. 5–8: start here

Planning documents for formalizing Chapters 5–8 of [PS10] R. Pass, a. shelat, *A Course in
Cryptography* (3rd ed., 2010), on top of the ch. 2–4 layer of this branch. Written 2026-11-04 by
the maintainer agent of the Arora–Barak ch. 3–4 campaign, at the user's (Seyoon Ragavan's) request,
for a later session to pick up. **Nothing is started:** no Lean exists for ch. 5–8, and no
decision beyond "ch. 2–4 stays with Frederick Dehmel; ch. 5–8 is pursued in parallel" has been
taken.

| File | What it is |
|---|---|
| `../../PassShelatChapter5-8Plan.md` | the plan: scope, dependence on ch. 2–4, the spine-then-prongs architecture, pacing, sizes, source gaps, coordination with the ch. 2–4 owner, phasing, risks, decision log |
| `inventory-ch5-8.md` | every item of ch. 5–8 (50 core, 14 optional, 5 deferred, 3 out) with its ch. 2–4 and `main` dependencies, prong, scope, difficulty and source notes |
| `SPINE-DESIGN.md` | the shared design built before the parallel prongs, and the open decisions D-1…D-7 with recommendations. It covers:<ul><li>the base and frozen interface;</li><li>the oracle-game layer;</li><li>two-party execution;</li><li>circuits for Yao;</li><li>the NUPPT ↔ BPP bridge;</li><li>the statement phase and its single gate.</li></ul> |
| `WORKFLOW.md` | how the Arora–Barak ch. 3–4 campaign is run, and what carries over. It covers:<ul><li>roles and the fill lifecycle;</li><li>gates and replays;</li><li>the local `exchange/` hand-off folder;</li><li>standing rules and overnight routines.</li></ul> |

**State of the base (2026-11-04):**
- this branch's ch. 2–4 head (`c1360aa1`) does not build: two duplicate public names;
- 63 sorried declarations remain, by text census;
- it forked from `main` on 2026-10-08.

The plan and `SPINE-DESIGN.md` §S1 say what the ch. 5–8 line needs from it.

**Update (2026-11-04, maintainer session):** decisions D-0…D-7 are ruled (plan, decision log). Shamir is already proved on `main`, so P0 is the extractor basics plus [PS10] citations on main's Shamir. The hand-off folders are on the orphan branch `exchange/pass-shelat-ch5-8`.

**Next steps:**
1. Rulings on D-1…D-7.
2. Prong zero (Shamir secret sharing, extractor basics), which needs nothing from ch. 2–4.
3. In parallel, a building base and an interface agreement with the ch. 2–4 owner.
