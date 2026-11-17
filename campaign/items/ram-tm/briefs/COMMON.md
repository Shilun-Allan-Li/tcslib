# RAM fills: rules common to every brief

These rules bind every RAM fill (tier 1 `fill-ram-wordsize`, tier 3 `fill-ram-classes`, and
later the tier 2 fills). Each brief adds its targets, owned file and route.

## Repository, exchange and base

- **You work to and from the exchange.** It is branch `exchange/pass-shelat-ch5-8` of
  `https://github.com/Shilun-Allan-Li/tcslib`, folder `arora-barak-ch3-4/`.
  - **Inputs:** your fill's bundle and README, in `arora-barak-ch3-4/outbox/fills/<fill-name>/`.
  - **Output:** your delivery, in `arora-barak-ch3-4/inbox/<fill-name>/` (see "Delivery").
  - Do not push anywhere else.
- **Repository:** the same repository. Fetch the base commit from it read-only.
- **Base:** the commit named in your brief, on branch `complexity/ram-simulation`. That branch
  is `main` after the chapters 3–4 integration (#364), with the maintainer tools
  (`devtools/seyoon/`) merged in. Work on a local branch off it, record the base in `REPORT.md`,
  and never rebase.

## Ground rules (binding)

1. **Statement freeze.** Every existing declaration keeps its statement byte-identical. You
   change only the bodies of your targets, their `**Proof sketch.**` paragraphs, and the owned
   file's module docstring. A statement you believe is false or unprovable as written is an
   **E-STATEMENT** stop: report it with the evidence, and do not change it.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2). A proof may read another file's TCSlib
   definition only through that file's published equations and lemmas. So:
   - no `simp [Def]`, `unfold Def`, `delta`, generated `eq_1`/`eq_def`, or
     `rfl`/`change`/`show` that unfolds another file's definition;
   - core and Mathlib definitions may reduce by `rfl`, `decide` or `show`, but are not passed to
     `simp`, `rw` or `unfold`.

   The maintainer's seal check makes every other-file definition irreducible and re-elaborates
   your proofs. A proof that unfolds one fails there. A missing reader is an **E-READER** stop.
   Report it; do not unfold.
3. **No new public surface.** Do not add public declarations, files, imports, `@[simp]`
   attributes, `sorry`, `admit` or axioms. Helpers are `private`, in the owned file, under a
   section header. If you need a new public lemma or machine elsewhere, that is an **E-HOST**
   stop: report its statement and why.
4. **Cite, do not re-prove.** Search the import closure before proving a helper fact. Re-deriving
   an existing fact, or copying a proof's text for a variant instead of factoring a private
   helper, is a duplication finding even when the copy screens miss it.
5. **Standards** (`policy.md`): a `**Proof sketch.**` on every proof over 20 lines, describing
   the proof you wrote and naming declarations, not file line numbers. Docstrings carry no
   campaign labels: no decision or item codes such as `R8.5c`, `MIG-0a` or `PROG-4`, no
   `design §…` and no `campaign/` paths. Rewrite the proof sketches of the targets you prove to
   meet this. When the owned file's last admission is proved, drop "proofs pending" from its
   module docstring.
6. **A clean frontier is a valid delivery.** Prove what you can. Leave each unproved target as
   `sorry`, and report exactly where you stopped and why.

## Environment and verification

- Follow `campaign/standards/fill-environment-addendum.md` (v2.6). **Never run `lake build`.**
  Bootstrap the import closure at the base into your own scratch olean tree.
- **At most 3 Lean processes may run at once across the machine.** Other fills share it: start
  at most one of your own at a time, check the machine-wide count first, and record any waits.
- **Final checks** (record their exit codes):
  - the owned file elaborates with zero errors and no `sorry` warnings for the proved targets;
  - `#print axioms` for each proved target prints at most `propext`, `Classical.choice` and
    `Quot.sound`, plus `sorryAx` only if the target reaches a still-admitted declaration. Run
    it through a scratch file, not in the library;
  - for every target whose axioms include `sorryAx`, a scratch **dependency walk** that lists
    each reachable constant whose value uses `sorryAx`, as the chapters 3–4 probe
    `CloseHeadlines` does (gate 160, G160-01). The list must contain only the admitted
    declarations your brief names;
  - every module that imports the owned file elaborates with zero errors.

## REPORT.md checklist

- [ ] The base, and each target: proved, or the frontier and the reason.
- [ ] For each target that reaches `sorryAx`, the dependency walk's list of admitted
      declarations.
- [ ] Every new private declaration and its role. Every other-file definition reached, and the
      published equation used to read it. The existing facts you searched for before each
      helper.
- [ ] The final check outputs, the axiom prints, and `git diff --stat` touching only the owned
      file.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `<fill-name>.zip` containing `REPORT.md`, the delivered owned file, the patch against the
base, and the check logs. Push it, with any `<fill-name>-checkpoint-N.zip`, to
`arora-barak-ch3-4/inbox/<fill-name>/` on the exchange branch. Run `git pull --rebase` first,
do not force, and touch nothing else there. Also attach the final zip in chat. Do not push to
any other branch, and do not open a pull request. The maintainer lands the delivery as a gated
PR into `complexity/ram-simulation`.
