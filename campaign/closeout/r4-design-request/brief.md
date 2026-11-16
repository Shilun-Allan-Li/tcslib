# R4 design request: the SAT/Hardness duplication families (Claude cloud worker, read-only design pass)

**Who and where.** You are a Claude worker in the cloud with read and write access to the exchange
branch `exchange/pass-shelat-ch5-8` of `Shilun-Allan-Li/tcslib`. Everything you need is in this
bundle (`arora-barak-ch3-4/outbox/fills/r4-design/r4-design-bundle.md`, one section per file, in
`BUNDLE-FILES.txt` order; check its SHA-256 against `SHA256SUMS`). The Lean sources in it are the
campaign at Lean `68cba664c2fcb4e33b4845b385feea3f456d0105`.

**Deliverable:** `r4-design.md`, pushed to `arora-barak-ch3-4/inbox/r4-design/` on the exchange
branch (`git pull --rebase` first; never force-push; touch nothing outside `arora-barak-ch3-4/`).
End your session with a short summary: the summary table of §3 and the push commit.

**This is a design and sizing study, not a fill.** Edit no Lean file, open no pull request, and do
not run Lean or `lake`: measure by reading the bundled sources (line counts, text searches). Where
a number cannot be measured that way, give a range and say it is an estimate.

## 1. Why this study

The chapters 3–4 closeout is retiring acknowledged duplication before integration into `main`
(`campaign/closeout/REFACTOR-PLAN.md`, bundled). Wave **R4** is the largest: the SAT/Hardness
families. Two lessons from the waves already run decide what this study must measure:

- **R2c** (`campaign/closeout/R2C-SCANNER.md` §6): a generic interface that removes copies can
  cost more than it saves once each instance's transport/instance code is counted. Catalog grew
  by 361 lines and the copy screen by 10 pairs, and the family was carried instead.
- **R2a** (gate 144): every proof a refactor *touches* becomes subject to the rule-10 seals
  (`campaign/maintainer/WORKFLOW.md` §2, `policy.md` §1): it may read another file's definitions
  (TCSlib, Mathlib or Core) only through published equations. Untouched legacy proofs often unfold
  other files' definitions (by `rfl`, `change`, `show`, `decide`, `simp [Def]`, `unfold`, generated
  equation lemmas `Def.eq_1`/`eq_def`); once touched, each such read must be repaired. In R2a
  that repair work was larger than the refactor itself.

So the study must give, per family, an **honest net cost**, including interface, instance and
transport code, use-site edits and rule-10 repairs, and a run-or-carry recommendation.

## 2. The families (descriptions in the bundled ledger and backlog; grep the ids)

All in `TCSlib/Complexity/ClassNP/SAT.lean` and `TCSlib/Complexity/CookLevin/Hardness.lean` (both
bundled) unless noted.

1. **SG1 kinds 1–6** (ledger, the SG1 kind table): clean module, positive-release stop, bank padding,
   one-way transducer, polynomial bridge, finite-family dispatcher. About 22 exact
   prefix-renaming pairs between the two files. The records call them "retained debt, not a new
   API"; retiring them needs shared interfaces that Seyoon must approve.
2. **SG1-UH**, the unary-clock host (backlog SG1-UH): Hardness's 12 `clRepeat*` declarations,
   `clA5Iter_native`, `clA5Iter_shrinking`. A shared host contract with resource and
   head-envelope clauses (the API goes to Seyoon).
3. **PL-1's twins** (ledger PL-1): `a3n_poly_*`, `sat_pt_eq`, `clA5_pt_eq`.
4. **12.2c item 13, `clPlacement`** (ledger, item 13): 17 declarations in Hardness; plain `Fin`
   embeddings proposed.
5. **FH-1's held implementations** (`campaign/gates/122-first-halt-reuse/`, bundled resolutions):
   seven implementations held at gate 122 that might cite `Turing.MultiTapeTM.exists_first_halt`
   (`TuringMachine/Finite.lean`, bundled).
6. **FE-LIVE-1's Hardness front**, `clA5Compare_compute` (`campaign/gates/121-fe-live1-cleanup/`,
   bundled resolutions), held at gate 121. Canonical: `exists_first_entry_of_fixed` (Finite).

## 3. What to produce, per family

1. **Members:** the duplicated declarations (fully qualified names, file, line), checked present in
   the bundled sources, and for pairs which declaration duplicates which.
2. **Proposal:** what each member becomes. Prefer citing an existing public declaration. Where a
   new shared interface is needed, give its proposed Lean statement(s) (signatures and docstring
   summary, uncompiled), and say where it would live.
3. **Use sites:** every declaration whose statement or proof mentions a member, so would change.
4. **Net cost:** lines removed (members, copied proof text), lines added (interface, its proofs,
   each instance's adapter or transport, use-site edits), and the net; the copy-text pairs it
   would retire and any it could create (instances resembling each other).
5. **Rule-10 exposure:** for each use site and each member that would be edited, list the reads
   of other files' definitions its proof makes today (the forms in §1) and estimate the repair:
   a published equation exists (cite it), or a new published equation would be needed.
6. **Statement changes:** any public statement that would change (should be none; flag it if the
   design needs one).
7. **Recommendation:** run or carry, with the reason, and if run, the PR slicing and order.

Then a **summary table**: family · members · use sites · net lines · pairs retired/created ·
rule-10 repairs · new public API · statement changes · recommendation.

## 4. Constraints

- No statement change of a public declaration; no rename; no new import into a frozen file
  without flagging it. New public declarations are proposals for Seyoon, not decisions.
- Follow `policy.md` (docstrings with proof sketches for proposed lemmas; attribution tags) and
  the campaign standards (`campaign/standards/TEMPLATE.md`).
- Be honest about uncertainty: give ranges where you cannot measure, and say which numbers were
  measured (line counts, searches in the bundled sources) and which were estimated.
