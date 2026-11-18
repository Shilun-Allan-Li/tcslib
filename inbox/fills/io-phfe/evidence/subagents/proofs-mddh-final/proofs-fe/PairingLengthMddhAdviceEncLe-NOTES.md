# Advice-word polynomial length bound

Status: complete scratch proof candidate, NOT natively checked. No Lean/lake/build/Git,
live-source edit, process operation, extra agent, or native search was run by this child.

Candidate: PairingLengthMddhAdviceEncLe.lean.inc. The exact frozen original docstring/header
of BilinearGen.length_mddhAdviceEnc_le was copied from the current live SelfReduction.lean.
One tactic block, no placeholder/admission, no line over 100 columns. All source declaration
and public algorithm statements are unchanged. No new generic helper is defined or proved.

## Exact dependencies / assembly

- orderSchedule_neZero G p hp kappa supplies the existing nonzero scalar modulus instance.
  No Field instance or Mathlib.Algebra.Field.ZMod import is needed for this length proof.
- Turing.length_bits_le_self at Complexity/TuringMachine/Encoding.lean:301 gives
  n.bits.length <= n. Mathlib Nat.size_eq_bits_len at Data/Nat/Size.lean:126 rewrites the
  left side to Nat.size n. This is reused independently for d.eval kappa and ell.eval kappa;
  the generic binary-width estimate is NOT re-proved via induction or exponent arithmetic.
- G.mddhAdviceEnc_eq and G.mddhAdviceLen_eq are the only advice-definition readers used.
- Turing.length_pairEncode (:220), Candidates.length_natToList (Arithmetic.lean:107),
  List.length_replicate/length_append/length_ofFn, and Encoding.Modular.encodeMatrix_length
  (Encoding/Modular.lean:91) give every serialized block's actual length.
- PolyExpr.eval_add/mul/var/const (Complexity/Randomized/PolyExpr.lean:116-125) read the
  polynomial. Nat.add_mul distributes its scalar-count sum; omega closes using the two
  published binary-header bounds. No multiplicative/rank counting lemma is recreated.

The exact serialized length after readers is
  2*kappa + 2*size(dk) + 2*size(lk) + 6 + (dk+1)
    + (lk*3)*w + (2*dk)*w + (lk*dk)*w.
The advertised polynomial is
  2*kappa + 2*dk + 2*lk + 10 + (dk+1)
    + (lk*3)*w + (2*dk)*w + (lk*dk)*w.
Hence the reused stronger size(n)<=n bounds leave four extra bits of slack. This does not
change the frozen proof sketch's weaker value-plus-one estimate or the polynomial formula.
The zero response/row/width cases are included automatically.

No group-order encoding-width bound is needed: the published modular LENGTH theorem holds
even when a width truncates. The no-truncation/order-width obligation belongs to the separate
advice INJECTIVITY proof. No BB1 draw or coin decoder, or proof from one, is copied or used.

## Actual static reuse searches

Live root: /Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange.
Read SelfReduction.lean:1-175, including the exact codec/length readers and frozen theorem.
Read Encoding/Modular.lean:45-110, Candidates/Arithmetic.lean:90-114,
Complexity/TuringMachine/Encoding.lean:208-229 and :282-309,
Complexity/Randomized/PolyExpr.lean:110-137, and Mathlib/Data/Nat/Size.lean:81-126.

Actual rg searches covered:
- mddhAdviceEnc / length_mddhAdvice / order-width and size/order shapes in Pairing/Encoding;
- encodeMatrix_length / length_natToList / length_pairEncode exact names;
- size_le_self / size_le_succ / Nat.size inequalities in core Init/Data/Nat, Mathlib Nat,
  TCSlib Pairing/FunctionalEncryption, then TCSlib globally for size_le.2 uses;
- eval_add/mul/var/const in Complexity PolyExpr modules;
- public length_bits_le_self after finding it at TuringMachine/Encoding.lean:301;
- core Nat.lt_two_pow_self at Init/Data/Nat/Lemmas.lean:1227 was inspected as the nearest
  underlying exponent reader, but the candidate consumes length_bits_le_self instead;
- core List and Mathlib OfFn length-reader names; actual imported modular theorem consumes
  the existing fixed-length encoders, so no list flatten/chunk helper is needed.

The Lamport Advice.lean:55-59 reader length_indexBits_le is a source-relative parallel of
using Nat.size_le plus Nat.lt_two_pow_self, but is tied to its indexBits algorithm. The shared
Turing.length_bits_le_self is the closer reusable theorem and is the one actually consumed.
QuadraticSecurity/Advice.lean was read for comparison of analogous metadata; no code or
algorithm is taken from it. Two exploratory paths (LinearSecurity/Advice.lean and a broad
candidate search) yielded missing-path/no-match diagnostics and were replaced by rg --files
and targeted reads. An initial candidate search output was truncated, so no conclusion
relies on its omitted portion; all actual reused APIs were re-read by narrow source range.

Native validation, axiom census and Rule 10 seals remain lead-owned and pending.
