# Ch3–4 fill campaign — B5a, the canonizer, continuation 6: the grammar stage (`exists_canonGrammarStage`, by declaration in `TuringMachine/CodeSimulator.lean`)

> **DRAFT (maintainer, overnight 2026-10-16). Not issued.**
> - Base: the tip after #113 (cont5 partial), #112 and #116. Every ⟨…⟩ is measured at issue.
> - The pre-ship **inventory** (the user's "Everything" rule) is still to do. It covers the
>   counter-loop statements' definitions (`counterOverhead`, the loop configurations) and the
>   catalog rows the route names. Any gap goes into an API PR before issue.

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out **`complexity/arora-barak-ch3-4`**,
  not `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it fails, **stop**.
  That commit contains:
  - **your predecessor's delivery (PR #113, merged).** It holds:
    - the prescribed factoring;
    - **`exists_canonDecider` proved modulo your stub**;
    - the two permitted leaves (`canonSuffixTM`/`canonSuffix_run`, the native all-`true` suffix
      scan, unused so far, which is yours to use; `canonHaltTM`/`canonHalt_run`);
    - the emit adapter `canonEmitVerdict`.

    Its review is `audits/evidence/b5a-canon-cont5/delivery-review.md`.
  - **the specification APIs** (PRs #112 and #116): every definition your route reads outside
    your file has a published equation or field lemma (ground rule 10);
  - the fill-agent environment addendum, and the copy-text screen v3;
  - **this round's inputs** (`audits/evidence/b5a-canon-cont6/`): the order list
    `briefs/orders/b5a-fill-canon-cont6.txt`, **which now includes `ClassNP/TMSAT`** (cont5's
    review found it missing), the base sorry set, the screen base and the pre-ship log.
- Branch from exactly that commit (`git checkout -b fill/b5a-canon-cont6 @ANCESTOR@`). Never rebase,
  merge or cherry-pick.
- **Delivery is by zip:** `fill-b5a-canon-cont6.zip`, with the same contents as cont5's (REPORT, source,
  format-patch, bundle, logs, note-50 file and log, both screens, `SHA256SUMS`).

## What this is

**The canonizer's last open admission.** `MachineFormat.exists_polyCanonizer` is proved modulo
exactly one private stub, **`exists_canonGrammarStage`** (⟨line⟩). Your target is that stub, and
then note 50 on the complete canonizer.

**User ruling on cont5's escalation E1 (2026-10-16): the adapter is authorized.**
- C2 (`exists_canonRecordTM`) cannot be a counter-loop body directly: it stops at a separate,
  stationary `exit true`, while `counterLoopTM` needs each round to start and end at one anchor.
  The cont5 brief's pitfall said otherwise; it is withdrawn.
- **Use a phase-host adapter with a fresh anchor:**
  - a fresh state `a` dispatches to C2's entry;
  - C2's `exit true` returns to `a`;
  - C2's `exit false` goes to a separate escape.

  It is a composition over the public `phaseHostTM` (two dispatch steps per record), **not a new
  host**.
- **State and prove its first-return contract once**, as a private lemma: from `a`, positive time,
  the interior avoids both `a` and the escape (the anchor is fresh, so C2's internal visits to its
  own entry do not count), the endpoint is `a` or the escape, and the record's ledger is C2's plus
  two.

## Owned regions (lines at the issue tree, measured)

- **(a) the home** ⟨line⟩;
- **(b) `exists_canonGrammarStage`'s body** ⟨line⟩. Rewrite its appendix paragraph (⟨lines⟩)
  for the final state.
- **(c) `exists_polyCanonizer`'s docstring:** a flagged appendix paragraph. Its "(spec, fill
  pending — batch B5a)" tag becomes "proved" only for a complete delivery; flag it.

Everything else is frozen, including #113's declarations and the H1 region.

## The route (binding where it names a row)

The cont5 brief's C3–C5 route (`briefs/b5a-fill-canon-cont5.md`, "The route") stands, with these
changes:
1. **The inner loop's body is the adapter around C2** (above), not C2 itself.
2. **The suffix** uses the landed `canonSuffixTM`/`canonSuffix_run`.
3. **The generic link** ("a counter loop whose body decides a skipper `r` decides
   `codeSkipRepeat r (counterValue c)`, failing fast") is proved once, over the adapter's
   contract.

## Ground rules

As cont5's, except:
- **Rule 10, no unfolding (user, 2026-10-16), as in the current briefs.** Never unfold another
  file's definition; read it through published lemmas. The model's primitives go through their
  existing lemmas, and you unfold `step` only for a leaf in your own file. Escalate a missing
  lemma.
- **Imports:** unchanged.
- **Out of scope:** `exists_uniformSimulator` and every other sorry.

## Phases (for a partial)

1. **The adapter and its contract** (a private lemma).
2. **The generic link.**
3. **`exists_canonGrammarStage` proved:** the canonizer is complete.
4. **Note 50** elaborated on the complete canonizer.

Add no new admission. Prove a helper before inserting it.

## Measurements to fill at issue

⟨order list⟩, ⟨base sorry set⟩, ⟨screen population and base⟩, ⟨lint base⟩, ⟨import probe⟩.
