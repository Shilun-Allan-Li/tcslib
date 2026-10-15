# Chapter 7: prefix operations and fixed-randomness circuits

Base: `69a606dac3366a878f98683812b69c40356e4c0b`, branch
`complexity/arora-barak-ch7`.

Proof implementations replace three stubs in `Randomized/PolyTimeModel.lean`:

- `polyTimeComputable_takePrefixByLen`
- `polyTimeComputable_dropPrefixByLen`
- `polyTimeModel_verifierHasCircuits`

All 20 pre-existing definition and theorem signatures in that file are unchanged.
The new support modules contain no admissions or additional axioms. Their imports
are added to the existing topic facades. These are additive infrastructure changes
in the Chapter 1–2 function, machine, and circuit layers; existing declarations in
those layers are unchanged.

## Proof arguments

The shared prefix program counts one source bit per aligned doubled pair. At the
separator it either copies that many payload bits or skips them and copies the
remaining payload. Incomplete encodings and the forbidden aligned pair `10`
halt without output. The abstract step bound is `5(|z|+1)`; the existing
counter-program compiler gives polynomial-time machines.

The circuit construction applies the proved `P ⊆ P/poly` theorem to the verifier's
paired acceptance language. Each encoded input coordinate receives a distinct
buffer vertex: the doubled input bits are copies, and the separator and random
bits are constants. Shifting all old vertex numbers preserves distinct inputs and
fan-in. The resulting circuit has exactly `n + C.size` vertices. The proof composes
the paired-length polynomial with the family's size polynomial to obtain a bound
independent of the random string's contents.

## Validation

- Independent source reviews of both constructions and the main circuit proof.
- `scripts/style_lint.py`: zero findings in all seven touched Lean files.
- Prefix-program model: all 8,190 input/mode combinations for bit strings of
  length at most 11 passed output and abstract-time checks.
- Circuit-buffer model: 2,790 evaluation and well-formedness checks passed,
  including empty input and random strings and gates reading both doubled copies.
- Uniform circuit-size arithmetic: 7,776 parameter combinations passed,
  including zero coefficients and exponents.
- No public-statement drift in `PolyTimeModel.lean`; no new `sorry`, `admit`,
  custom `axiom`, or `unsafe` declaration in the support modules.

**Lean elaboration and kernel checking remain unverified.** The execution environment
has no Lean runtime or working LeanInfoView, and `AGENTS.md` requires proof-state
checking through LeanInfoView rather than shell build commands. The finite model
checks above validate the algorithms and arithmetic; they do not certify the Lean
proof terms. This commit is a proof implementation awaiting that check.

Three machine-model admissions remain: majority, OR repetition, and shifted OR.
The separate expander-Chernoff theorem remains intentionally statement-only.
The specialized ZPP, Adleman, and Sipser–Gács corollaries consequently still depend
on unfinished closure proofs.
