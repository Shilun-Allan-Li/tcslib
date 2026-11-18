# Gate 167 · (a5) PROG-2: the signatures of Light with input and output (a statement gate on a mirror)

**A statement gate on a mirror.** No Lean PR is gated here. Light gains string input and output
and coins, in place in the vendored files, as decided in October (design §15c–§15d) and confirmed
by Seyoon on 2026-11-18. The edit changes definitions in place, so a sorried statements PR cannot
land first. Instead this gate audits a self-contained mirror of every new and changed declaration
before jobs H1 and H2 edit the vendored files. Seyoon dispatches.

- **The design:** `campaign/items/ram-tm/PROG2-DESIGN.md`: purpose, October's binding decisions,
  the mapping from mirror to in place (§3), the edit set (§4), the jobs (§5), the risks (§6) and
  the rulings (§7).
- **The mirror:** `campaign/items/ram-tm/prog2/PROG2Mirror.lean.txt`, 493 lines, in the namespace
  `TCSlib.Draft.PROG2`. It is October's draft (`ExtensionsDraft.lean.txt`, gated in principle at
  gate 10 in October, with its extended forms to be re-gated here), updated with:
  - **relocation:** `XStmt.shift`, `XProgram.behind`, `XExec.shift`, the extension of
    `Light/Renumber`, vendored since;
  - **the deliverable:** `haltsWithin_compileProgram`. A Light run of the outermost call on `x`
    with output `o` makes the compiled extended-RAM program `HaltsWithin` on `x`, with output `o`,
    within `ramSteps + 1` steps and `3t` cells. The mirror cannot compile mirror syntax, so the
    compiler, `ramSteps`, `dispPos` and `stackCells` are `opaque` stand-ins, with only the shape
    audited;
  - **the hypothesis** `|x| ≤ lim.word`, which the compiler's `Input.arg1_le` needs.
- **Check:** the mirror elaborates on the RAM branch's build `oleans-cl165-cl164` with 0 errors and
  27 `sorry` warnings, all of them the intended statements (`prog2/mirror.log`).

## Brief for the auditor

1. **Fidelity to the in-place edit.** Each mirror declaration must be what the in-place one will
   be (design §3). Check:
   - `XStmt` is `Light.Stmt` plus four constructors;
   - `XExec` is `Light.Exec`'s nine rules with the indices `o` and `r`, concatenated by `seq` and
     `whileTrue` and passed through `call`, plus four rules;
   - `XEnds` keeps `Light.Ends`' type;
   - `XLimits` is `Light.Limits` with an `input` field.

   Check these against the vendored `Light/Syntax.lean`, `Logic.lean`, `Calls.lean` and
   `Renumber.lean` in the bundle.
2. **Truth.** Each sorried statement must be provable as stated:
   - the six inductions: conservativity, `append`, `loc_eq_of_notMem_assigns`, `bounded` (with
     the new `1 ≤ lim.word`), `mem_outside`, and `shift`;
   - `det`, and the length bounds;
   - the `EndsIO` rules and `callLast`;
   - `EndsIO.ofEnds`;
   - the deliverable, against the compiler's actual `Input`, `Fits` and `compileProgram_correct`
     (bundled).
3. **Semantics.**
   - `inBit` off the input, and at negative positions, reads `0`;
   - `emit` appends "nonzero";
   - a coin past the stream's end: `EndsIO` requires the consumed word to be a prefix;
   - `half` is `Int./` by 2, which rounds down, matching `BitVec.sshiftRight 1` on the RAM side;
   - `AcceptsND` and `acceptProb` (`randProb` over streams of length `m`), with uniform time
     bounds.
4. **Sufficiency.** For the crypto bridge: the deliverable, with `WordRAM.progOut_eq` and
   `WordRAM.polyTimeComputable_progOut` (PR #379), gives `PolyTimeComputable` for Light programs
   that halt within polynomial cost on every input. For L, NL and BPP consumers: `EndsIO`,
   `MeetsIO`, `AcceptsND` and `acceptProb`. Report any clause H1 or H2 would need that is missing.
5. **The edit set and risks** (design §4, §6): anything the mirror misses that the in-place edit
   must change.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate167-prog2-statements-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
