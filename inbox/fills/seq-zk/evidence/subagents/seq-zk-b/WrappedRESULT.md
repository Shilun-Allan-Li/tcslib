# seq-zk-b wrapped verifier result

seq-zk-b proved all 16 public declarations of SequentialZK/WrappedVerifier.lean, including
phaseVerifier_efficient, phaseAux_poly and phaseAux_length_le. The exact phase encoding is
`phaseAux z r j pre = pairEncode z (pairEncode r (pairEncode (replicate j true)
(Strategy.encodeMsgs pre)))`. The wrapper has zero coins and satisfies
`(phaseVerifier V).next x (phaseAux z r j pre) s hist = V.next x z r (pre ++ hist)`.

Final source SHA256: 76c24474aaa9873c5039a9b99decd325691a002f9876b5b5817f9f32dcc15040.
197 lines; maximum width 96; no sorry. wrapped-check-03.log: exit 0, no diagnostics;
maximum resident set size 2235383808 bytes. All 16 axiom prints in wrapped-axioms.log are
standard only (propext, Classical.choice and Quot.sound, or a subset/none); no sorryAx.
Final style lint across the four local helpers: 0 FAIL / 0 WARN.

All raw attempts are retained. The first attempt had 43 parser/import diagnostics because
`prefix` is a Lean keyword and the GI projection-machine lemmas require GI.Efficiency rather
than only GI.Proofs. The binder is now `pre`, and the precise import is corrected.
Both check-02 and final check-03 passed with no diagnostics. Diagnostic counts use the
required regexp matching both `error:` and `error(...)`; see wrapped-static.json.

The lead authorized source-only copies of seq-zk-a's stable Normalization.lean and
NormalizationMachine.lean. Their hashes/provenance and both independent successful compile
logs are retained. No foreign source was edited, no agent-a olean was copied, and no new host
was built. The wrappers use published canonical reencoding and encoding-append lemmas.
Every overlap and promotion request is disclosed in wrapped-overlap.md, with raw searches.

Every Lean run held the default shared host slot through /private/tmp/seq-zk-lean-slot.sh,
with tag seq-zk-b and TCSLIB_OLEANS=.lake/seq-zk-b-oleans; cap is 3 host-wide. No Lake ran.
No commit made. Lead remains responsible for merged checks and whole-closure Rule 10 seals.
