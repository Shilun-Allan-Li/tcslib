# Gate 137 · Ladner fill 2: the saturated power and the padding parser (PR #310)

**Not yet clear to merge** · PR #310 is a draft. Seyoon dispatches and merges.
The Lean commit is `07272ed4d91b22357b5a81a1f65d6787c6210e93`, against campaign Lean
`a052f8891d3c4520407bf9d976421148fc0f7a02` (the campaign after #304). This is the first audit.

## Scope

Codex's fill 2, under the brief `campaign/fills/ladner-common-leaves/briefs/ladner-common-leaves.md`
(bundled; pre-shipped, `preship/`), builds the common leaves of Ladner's theorem [AB09,
Theorem 3.3 and its proof] and proves no Ladner target. Codex's delivery is the branch's first
commit (`5a080e56`). The maintainer's dedup refactor is the second (`570cf193`), and its rule-10
repair the third (`07272ed4`).

1. **The saturated power** (public, approved), in `ClassP/BinaryArith/Mul.lean`: `powCap`,
   `powCap_eq`, `powCap_pairEncode` and `polyTimeComputable_powCap`, exactly as the brief states
   them, with 18 private helpers.
2. **The padding parser and finite tables** (private), in `Diagonalization/Ladner.lean`: 16
   `ladner_*` declarations (the route's §3 list, with glue) and the approved import
   `ClassP.BinaryArith.Loops`.
3. **The dedup refactor** (Seyoon's ruling, `campaign/backlog.md` P3.4). The delivered
   `powCap` round copied `ModPow.powStep` (screen pairs 50–86%). A generic public round now goes in
   Mul: `BinArith.sqStep op stop`, with readers `sqStep_of_stop`, `sqStep_cons` and
   `polyTimeComputable_sqStep`. `ModPow.powStep`'s body becomes
   `sqStep (fun z => mod (pairEncode (mul (pairSndD z)) (pairFstD z))) (fun S => decide (bitsVal (pairFstD S) = 0)) S`.
   Its type and every ModPow statement are unchanged, and its four proofs are re-pointed to the
   readers. `powCap`'s private step becomes `sqStep powCapMul (fun _ => false)`. The two loop
   invariants stay separate. One deviation from the ruled sketch: the fixed test is
   `decide (E = [])` rather than `isNilB E` (`ClassNP/PolyTimeBlockLoop`). The two are equal by
   definition, but `isNilB` has no published equation, so rule 10 could not read it.
4. **The `mod` reader** (approved). Re-pointing `powInv_step` and `polyTimeComputable_powMod`
   made them maintainer proofs, and they unfolded `mod`, `mul` and `bitsVal` directly. The new
   reader `BinArith.mod_eq` goes beside `mod` in Div; it is not `@[simp]` and is proved by `rfl`.
   It is needed because ModPow's modulus is an arbitrary word, which `mod_pairEncode` does not
   cover. The two proofs now read `mod` through `mod_eq`, `mul` through `mul_pairEncode` on the
   normalized registers, and `bitsVal` through `bitsVal_eq_headD` and `bitsVal_bits`. ModPow's
   unchanged proofs (`powInv_init` and others) keep their old unfolds and are out of scope.

`patch/campaign-to-head.patch` in the carrier is the whole Lean change (4 files).

## Brief for the auditor

1. **The mathematics.** `powCap` is `min (m ^ e) (c + 1)`, with malformed words read as `0`. Check
   `polyTimeComputable_powCap`: the size invariant holds on **every** loop state; every product is
   saturated, base squaring included; `m = 0`, `e = 0` and `0 ^ 0 = 1` are handled; a huge
   exponent forces neither a huge output nor a long loop. Check the Ladner leaves against the
   route probe's binding meanings (`preship/`), in particular `ladner_syntax_FP`, which compares
   `p.length ^ h p.length` with the unary suffix through `powCap` without allocating a huge number.
2. **The refactor.** `sqStep`'s body, specialised as above, is the old `powStep` body, with
   `isNilB` replaced by `decide (· = [])`. ModPow's statements are byte-identical: the inventory
   reports `definitions_changed: [powStep]` and no header change. The readers state
   `sqStep` exactly; none is `@[simp]`.
3. **Scope.** Only the four owners change; every existing declaration of Mul and Ladner is
   byte-identical; the new public declarations are exactly the nine approved ones (four `powCap`, four
   `sqStep`, `mod_eq`); no `sorry`, `admit`, axiom or attribute is added; Ladner's four
   other targets remain admitted.
4. **Rule 10.** Check each proof reads other files' TCSlib definitions only through published
   equations (the delivery's boundary ledger lists Codex's). Two checks:
   - **Seals** (`seals/`): all 36 changed or new proofs pass (Div 1, ModPow 3, Ladner 13, Mul 19),
     with 28 other-file definitions irreducible. The 56 paired controls each close natively and fail
     sealed.
   - **Probes** (`probes/`): the maintainer's probe seals `sqStep`, `mod`, `mul`, `bitsVal`
     and the pairing functions around the three changed ModPow proofs; its control file's two
     `rfl` goals fail sealed.

   Also check their `rw`/`simp`/`unfold` arguments. The base side was not sealed: the changed
   ModPow proofs are rewritten, so only the head versions are claimed rule-10 clean, and
   `checks.out`'s "BASE skipped" line is the script's default wording.
5. **Standards.** Docstrings cite [AB09, Theorem 3.3 and its proof], [AB09, Exercise 7.3]
   (repeated squaring) or library declarations; every proof over 20 lines has a proof sketch; no
   campaign labels in Lean text.
6. **Duplication.** Check the copy screens and their dispositions
   (`evidence/PAIR-DISPOSITIONS.json`). The narrow screen covers the four owners (BASE 58
   declarations and 26 pairs; HEAD 95 and 45; 27 new, 8 gone). The wide screen adds Basic,
   AddSub, Words and Loops (`screen-wide/`; BASE 146 declarations and 96 pairs; HEAD 183 and 121; 34 new, 9 gone).
   - No pair with `powCapStep` or `powCapInv_step` remains; the delivered fill had the
     78% `powStep`/`powCapStep` pair.
   - The new pairs are short closure or reader terms (`fp-idiom`, `idiom`), base pairs of
     `powStep` now attached to the shared host (`relocated`), or the two invariants kept apart
     by the ruling (`separate-invariant`).

   Report any disposition you disagree with, and any proof a new helper should cite instead.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure of the four owners on the
  campaign snapshot after #304 (876 objects; prospective tree
  `9872696527184e4a4b3401f8d8184deed3b43e26`). 24 passed, 0 failed; the 4 admissions are the
  remaining Ladner targets.
- Metadata: all 36 proofs use standard axioms only (`probes/Axioms.log` prints the public
  ones: at most `propext`, `Classical.choice`, `Quot.sound`). Lint: no new style or campaign
  finding.
- `evidence/DATA-CARRIER.json` and its recovery map hold 182 logical files, including the
  delivery zips. Decode each gzip+base64 blob and check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate137-ladner-common-leaves-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
