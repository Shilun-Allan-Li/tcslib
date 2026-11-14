# Ladner fill 2 (Codex): the saturated power and the padding parser

## Repository and base — read this before anything else

- Repository: `https://github.com/Shilun-Allan-Li/tcslib` (the same repository as your exchange
  checkout).
- **Base commit:** given in the dispatch prompt. It is the campaign `complexity/arora-barak-ch3-4`
  after Ladner fill 1 (#304, the two selector theorems) merges, or #304's head
  `bd8cd565ce1c9999211173b237f9ff8eae3f3d62` if it has not; `Ladner.lean` is the same in both.
  Work on a local branch off it (suggested `fill/ladner-common-leaves`). Record the base in
  `REPORT.md`. Never rebase.
- **Delivery** is by zip pushed to the exchange and attached in chat; see "Delivery".

## What this is

Ladner's theorem [AB09, Theorem 3.3 and its proof] has four admitted targets left in
`Diagonalization/Ladner.lean`. The Codex route draft (bundled,
`campaign/items/ladner/fill-routes-request/delivery/ladner-fill-routes.md`, §3 "Common leaves")
plans shared leaves that targets 1, 2 and 5 all use. **This fill builds those leaves and proves no
Ladner target.** Seyoon's rulings of 2026-11-14 (`campaign/backlog.md`, P3.4) apply.

### Part 1 — the saturated power (public, approved), in `ClassP/BinaryArith/Mul.lean`

Add, beside `mul`, exactly these four public declarations in namespace `Complexity.BinArith`, none
`@[simp]`:

```lean
def powCap (z : List Bool) : List Bool :=
  Nat.bits (min
    ((LogProg.bitsVal (pairFstD z)) ^ (LogProg.bitsVal (pairFstD (pairSndD z))))
    (LogProg.bitsVal (pairSndD (pairSndD z)) + 1))

theorem powCap_eq (z : List Bool) :
    powCap z = Nat.bits (min
      ((LogProg.bitsVal (pairFstD z)) ^ (LogProg.bitsVal (pairFstD (pairSndD z))))
      (LogProg.bitsVal (pairSndD (pairSndD z)) + 1))

theorem powCap_pairEncode (m e c : ℕ) :
    powCap (pairEncode (Nat.bits m) (pairEncode (Nat.bits e) (Nat.bits c))) =
      Nat.bits (min (m ^ e) (c + 1))

theorem polyTimeComputable_powCap : PolyTimeComputable powCap
```

`powCap z` is `min (m ^ e) (c + 1)` on the three numbers the word encodes, with malformed words
read as `0` by `bitsVal`, as for `mul`. Compute it by binary repeated squaring, one exponent bit per
round, saturating every product at `c + 1`; handle `m = 0`, `e = 0` and `0 ^ 0 = 1`. Obtain the FP
theorem from the existing `BinArith.polyTimeComputable_iterate` with `polyTimeComputable_mul`, the
comparisons of `AddSub` and the published bit-tail readings, with a polynomial size invariant on
**every** state of the loop. A huge binary exponent must not force a huge output or a long loop.

### Part 2 — the padding parser and finite tables (private), in `Diagonalization/Ladner.lean`

Add the route's §3 `LadnerRouteShared` declarations as **private** declarations in namespace
`Complexity` (prefix names `ladner_` as fill 1 did): `parse`, `padSyntax`, `parseWord`,
`parse_some`, `parse_none`, `parsed_length`, `parse_FP`, `syntax_FP`, `pad_membership`,
`finite_lookup_FP`, `small_SAT_table`. Their statements in the bundled route probe
(`Route-Shared.lean.txt`, pre-shipped here) are binding for meaning; you may adjust binder
presentation. `parse` is a mathematical specification; implement `parse_FP` through the existing
reverse, `uRest` and `hasFalse` hosts and length arithmetic, not by a new transition table.
`syntax_FP` uses `polyTimeComputable_powCap` (part 1) to compare `p.length ^ h p.length` with the
unary suffix without allocating a huge number. `pad_membership` goes through `mem_padSAT_iff`.
You may add the approved import `TCSlib.Complexity.ClassP.BinaryArith.Loops` to `Ladner.lean`.

## Owned files (modify these and nothing else)

`TCSlib/Complexity/ClassP/BinaryArith/Mul.lean` (part 1) and
`TCSlib/Complexity/Diagonalization/Ladner.lean` (part 2). Every existing declaration of both files,
including all Ladner targets (proved and admitted), stays **byte-identical**.

## Ground rules (binding)

1. **Statement freeze** for every existing declaration; the four part 1 statements are as above.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2, bundled): read other files' TCSlib
   definitions only through their published equations; core and Mathlib definitions may reduce by
   `rfl`, `decide` or `show` but are never passed to `simp`, `rw` or `unfold`. `powCap`'s own
   proofs may read `powCap` (same file). The readers R1–R6 (#302) and the route's §2 API table are
   available. If a step needs a reading with no published equation, **stop and escalate**
   (E-READER, with the proposed statement and home).
3. No other new public declarations, files, `@[simp]` attributes, `sorry`, `admit` or axioms.
4. **Standards** (`policy.md`): docstrings cite sources ([AB09, Theorem 3.3 and its proof] for the
   Ladner leaves; a standard reference or "repeated squaring" for `powCap`); a `**Proof sketch.**`
   on every proof over 20 lines; no campaign labels in Lean text.
5. **Escalate** anything unprovable as stated (E-STATEMENT) or a missing host (E-HOST). Part 1
   complete beats both parts partial.

## Environment and verification

Follow the bundled fill-environment addendum (v2.6); **never run `lake build`**. Bootstrap the
import closure at the base into your own scratch olean tree. **At most 3 Lean processes may run at
once across the machine** (other fills share it): start at most one of your own at a time, and
check the machine-wide count first; record waits. Final checks, with exit codes:

- `ClassP/BinaryArith/Mul.lean`, `ClassP/BinaryArith/Loops.lean` and `Diagonalization/Ladner.lean`
  with zero errors; Ladner's only `sorry` warnings are its four admitted targets;
- `#print axioms` for `polyTimeComputable_powCap`, `powCap_pairEncode` and the part 2 FP lemmas:
  at most `propext`, `Classical.choice`, `Quot.sound`;
- the facade `Diagonalization.lean` with zero errors.

## REPORT.md checklist

- [ ] Parts done (1, 2, or 1 plus a frontier); the base.
- [ ] Every new declaration with its role; every other-file definition reached and the equation used.
- [ ] Final check outputs, axiom prints, and `git diff --stat` touching only the two owned files.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `fill-ladner-common-leaves.zip` with `REPORT.md`, both delivered files, the patch against the
base and the check logs. Push it, with any `fill-ladner-common-leaves-checkpoint-N.zip`, to
`arora-barak-ch3-4/inbox/fill-ladner-common-leaves/` on the exchange branch after
`git pull --rebase`, without force and touching nothing else; also attach the final zip in chat.
Do not push to any other branch or open a pull request.
