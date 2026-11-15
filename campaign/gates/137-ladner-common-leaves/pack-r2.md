# Gate 137 round 2 · Ladner fill 2 with the shared repeated-squaring round (PR #310)

**Not yet clear to merge** · PR #310 is a draft. Seyoon dispatches and merges.
The Lean commit is `3b45471ccefbc2605541b5d5075a04a44f341477`, against campaign Lean
`a052f8891d3c4520407bf9d976421148fc0f7a02` (the campaign after #304, unchanged since round 1).
Round 1 audited `07272ed4` and returned HOLD with one major, G137-01, and one minor, G137-02
(`findings.md`, verbatim). This round checks their resolutions (`resolutions.md`) on fresh evidence.

## What changed since round 1

- `3b45471c` (`patch/round1-to-head.patch` in the carrier; two files):
  - `CircuitComplexity/UnaryCode.lean` gains the reader
    `BoolCircuit.encodeNat_eq (k) : encodeNat k = List.replicate k true ++ [false]`, beside the
    definition, not `@[simp]`, proved by `rfl`. Seyoon approved it on 2026-11-14. It is the tenth
    public declaration of the PR, and UnaryCode is its fifth owner.
  - In `Ladner.lean`, the inline `hr` of `ladner_parse_prefix` is now `uRest_encodeNat n w`
    rewritten through `encodeNat_eq`, `List.append_assoc` and `List.singleton_append`. The
    induction is gone, and no other declaration changes.
- The carrier now holds every wide-screen population file at BASE and HEAD.

The scope, rulings, API and statement checks are those of round 1's `pack.md` (bundled), with
the one added reader.

## Brief for the auditor

1. **G137-01.** Check the repaired `hr`. It must cite `uRest_encodeNat` and read
   `encodeNat` only through `encodeNat_eq`. Check that `encodeNat_eq` states the definition
   exactly, sits beside it, is not `@[simp]` and is proved by `rfl`. Check the seal of
   `ladner_parse_prefix`, which now has `BoolCircuit.encodeNat` among its sealed heads.
2. **G137-02.** Check that `screen-wide/BASE/population/` and `screen-wide/HEAD/population/` in
   the carrier hold all nine population files, and that both wide screens reproduce from them.
3. **Fresh evidence.** Replay, seals, controls, metadata, lint and both copy screens at the
   round 2 head.

## Evidence

- `r2-evidence/REPLAY.json`: the merged-tree replay of the downstream closure of the five owners on the
  campaign snapshot after #304 (876 objects; prospective tree
  `162b0b2b5dee98473406592796ea4ada70767560`). The closure grows from 24 to 93 modules because
  UnaryCode is now an owner. 93 passed, 0 failed; the 25 admissions are inherited (Ladner's four
  targets and 21 in `ClassPSPACE/TQBF`, which UnaryCode's closure now reaches).
- Seals: 36 proofs pass sealed (Div 1, ModPow 3, Ladner 13, Mul 19) with 29 other-file
  definitions irreducible, now including `BoolCircuit.encodeNat`. The 58 paired controls each
  close natively and fail sealed. The 37th proof, `encodeNat_eq`, reaches no other-file TCSlib
  definition, so the harness lists it under `no_foreign_boundary` instead of sealing it (its
  only change this round: `scripts/grouped-cmp.py` in the carrier). The maintainer's ModPow
  probe (`probes/`) is unchanged and gives the same results.
- Metadata: all 37 proofs use standard axioms only; `encodeNat_eq` uses none
  (`probes/Axioms.log`). Lint: no new finding. The campaign lint loses one warning, UnaryCode's
  `encodeNat` without a lemma beside it (check 8).
- Copy screens: the narrow screen (five owners) gives BASE 60 declarations and 26 pairs, HEAD 97
  and 45. The wide screen (nine files) gives BASE 148 and 96, HEAD 185 and 121. Both pair lists are
  identical to round 1, so the dispositions carry over (`r2-evidence/PAIR-DISPOSITIONS.json`,
  with G137-01 recorded as the one semantic copy the screen could not see).
- `r2-evidence/DATA-CARRIER.json` and its recovery map hold 414 logical files: everything
  round 1's carrier held, refreshed, plus the wide-screen sources and the round 1 patch. Decode
  each gzip+base64 blob and check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate137-ladner-common-leaves-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
