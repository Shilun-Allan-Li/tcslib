# Dispatch · Gate 44 round 1

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/30ef1257a56873489b599007782046b7dedeb7fc/outbox/gates/44-pairing-fills-gate)
is staged on the exchange. The commit is local and signed, and is not pushed yet; the maintainer pushes it. Seyoon
dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 44 of the pairing campaign (the
fills of T1 and T4), round 1, in https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 30ef1257a56873489b599007782046b7dedeb7fc.
   Read outbox/gates/44-pairing-fills-gate/README.md, pack-r1.md and bundle.md.
   Verify the pack using SHA256SUMS, and verification-r1.zip using the
   SHA256SUMS inside it.
2. Audit two draft PRs together, using the pack, with campaign records
   8f888790b7e40f9e0529967e29a05a72c5ee8ba3:
   - PR #340 at Lean head 916afc25c21f5e52b4b01958186ad55d2f615fd1 (merge base
     9e7a96481785d6cac4dea3b2e990c49ac278b060): the proof of T1
     BilinearGen.bdhAssumption_of_dbdhAssumption (Decision BDH implies BDH
     under the exponential-order hypothesis), Pairing/Assumptions.lean only.
   - PR #346 at Lean head 89a18a8225be1b76166af12a15179da291747783 (merge base
     7291f6b237fec75add1549c0992c174442180488): the proof of T4
     exists_bb1_distinguisher (the BB1 reduction machine, BB04 section 4.2),
     five new helper modules under IdentityBased/BonehBoyenMachine/, the
     seven approved readers in IdentityBased/Defs.lean and BonehBoyen.lean,
     and the landing edit LE-bb1m (89a18a82).
   Their merge with the records tip 1d1a9bb3aa4d5d28c7c9a2343cb322a39da07821
   is T44 = 33681cb8ed893a897ca2028d5ada70ca29237978 in every order (Lean-equal
   to c7be1301f59ec0f208f2645544abac8ac5cc6626).
   Check (pack, questions 1-10):
   - that the targets are true as frozen and the proofs establish them, for
     every input, with the edge cases; that T2-T4 still suffice for
     bb1_sidSecure, which now reaches sorryAx only through T2 and T3;
   - that T1's and T4's headers and statement prose are unchanged, and every
     other frozen declaration too; that the seven readers are exactly the
     approved text, inserted verbatim at the approved positions and nothing
     else (Seyoon's ruling of 2026-11-16); that LE-bb1m is proof- and
     doc-only;
   - Rule 10: the seals on Pairing/Assumptions and the five #346 owners
     downstream of it (strict and coe, A and B), the paired controls on
     Assumptions, the explicit-unfold scan, whether request-set identity
     justifies not re-sealing Defs, BonehBoyen and Draws, and the
     supplement: the re-seal of the unchanged Gate 40 owners downstream of
     the changed files (Joux, BonehBoyenSecurity, the IdentityBased and
     AdvancedEncryption facades; 16/16, controls ALL_OK);
   - sources and citations: BB04 tags, T1's folklore attribution (ruling
     Q10), the PS10 Theorem 52.3 locator on Draws.draw, BB04 page locators;
   - duplication (an undisclosed re-proof of a public lemma is a major),
     with #340's seven overlap disclosures and #346's review findings BM-F01
     to BM-F09, which you should grade;
   - docstrings and sketches, the axioms, and the joint replay on olean
     snapshot #4 (16/16 rc 0, admissions 198 -> 196, exactly T1 and T4);
   - whether anything is undisclosed (pack, known slips).
   Gate 40 (the statements) is closed and is not re-audited; the bb1-sim
   fill (T2, T3) and #351/#352 are out of scope. The merge order and the
   snapshot adoption are maintainer merge conditions, not audit items.
3. Return gate44-pairing-fills-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and
   evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `8f888790b7e40f9e0529967e29a05a72c5ee8ba3` (Seyoon's ruling: the records tip just before this gate's
  first commit, as in Gate 42 r2; the pack's own files are filed after the pin). The replay was staged at
  `1d1a9bb3aa4d5d28c7c9a2343cb322a39da07821`; the three records-only commits to `8f888790` (the bb1-sim T2/T3 fill) change no
  code path.
- **Records commits:** `997aac33ab63f3c58e2a40f324c864b4dbdca626` (the first staging, on `8f888790`; pushed by the
  coordinator) and the finalization commit on top of it that carries this file (the pin filled, the seal supplement, the
  refreshed PR descriptions, regenerated sums). Both add only `briefs/pairings/gates/44-pairing-fills/`.
- **Exchange:** the commit is `30ef1257a56873489b599007782046b7dedeb7fc`, one SSH-signed commit on the exchange tip
  `4cbe7980fc9716618a0ae5a3a3255d8464dd317a` ("Outbox: gate 154 round 2 bundle (PR #350, head 375531b6)"). The tip moved
  from `c797f6f2` after the first staging (`bc2bf64a` cleanup-stage1 checkpoint 1, `1ef26470` bb1-sim checkpoint 1,
  `4cbe7980` the Arora–Barak gate 154 outbox; no shared path), so the staging commit `c92247e1` (never pushed) was replayed
  onto it.
  - The local branch is `stage/gate44-exchange`, in the sparse worktree `$SP/wt-exch-g44`.
  - The commit adds only `outbox/gates/44-pairing-fills-gate/`.
  - It is **not pushed**.
  - 15 files; `SHA256SUMS` (`14af9a59…`) verifies 14/14 from a fresh `git archive` of the commit; `bundle.md` is
    `e15009856b528f3be9cb6d4efd77dd23f34ef94b9f929bc4e4fdf7f398310f79`, 43 sections (not committed to the records, per
    workflow §3); `verification-r1.zip` (`ebb59398…`) has 550 entries and verifies against its own `SHA256SUMS` from a fresh
    extract.
- **PR descriptions:** Seyoon updated both bodies on 2026-11-17 (04:34 UTC); the pack carries them as fetched afterwards.

**Ready to dispatch** once the exchange commit and the records finalization commit are pushed.
