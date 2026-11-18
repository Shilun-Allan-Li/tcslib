# BilinearGen.length_mddhEnc candidate

Status: scratch full candidate checked by inspection only; native pending. No Lean, lake,
build, Git, live edit or extra agent was used. Frozen header/prose copied byte-for-byte,
including its existing newline after :=. One tactic block, no remaining holes/sorry, no
helper/import/statement change. The dependency BilinearGroup.length_groupMatrixEnc remains
pending native verification/integration, so no standard-only encoding-length chain is claimed.

Read mddhEnc_eq and PublicParams.encode_eq. The three pair encodings have lengths given by
length_pairEncode; both matrix words are read through length_groupMatrixEnc, and the public
generator word through List.length_ofFn. A proof-only reachability witness supplies
`G.desc κ r = c.pp.description.val`, so length_desc fixes that word length. ring then checks:

2*(2*desc+2+wG)+2 + 2*(ell*2*wG)+2 + ell*d*wG
  = 4*desc + (2+4*ell+ell*d)*wG + 8.

The width is fixed by G.group's type BilinearGroup (G.wG.eval κ) (G.wT.eval κ); no description-
dependent width or scalar encoding is introduced. Zero matrix dimensions are supported by
the matrix-length theorem. Eliminating the existential description proof occurs only in this
length proof, with no sampler, algorithm, generator-coin recovery function, DLOG, or witness
encoding. No foreign/core/Mathlib definition is explicitly passed to simp/rw/unfold; all
listed items are public equation/algebra lemmas.

## Actual search/read record

* Read live MatrixDH/Defs.lean:100-133 for exact mddhEnc_eq and frozen length_mddhEnc header.
* Read MatrixDH/Parameters.lean:86-107 for PublicParams.encode_eq. Searched
  `length.*encode|encode.*length|length_desc|descLen|wG` in Parameters/Defs and found no
  more direct public-parameter length theorem; its existing encoding reader suffices.
* Read shared Complexity/TuringMachine/Encoding.lean:215-224 for length_pairEncode (220).
* Read pending PairingLengthGroupMatrixEnc.lean.inc for the exact rows*cols*wG formula.
* Read installed core Init/Data/List/OfFn.lean:40 for List.length_ofFn and
  Pairing/Group.lean:302-313 for G.length_desc (310).
* `rg -n 'PublicParams.encode_eq.*length|length_pairEncode.*length_groupMatrixEnc|length_mddhEnc'`
  over TCSlib and scratch drafts located only this existing frozen target; no helper was
  needed. Prior public-description reachability/width searches are recorded in
  PairingLengthDlinEnc-NOTES.md; that proof pattern is reused here without new semantics.

Dependency ledger: mddhEnc_eq/PublicParams.encode_eq/length_pairEncode/List.length_ofFn/
length_desc are existing proved readers; length_groupMatrixEnc is the explicitly pending
local M1 candidate. Correctness and reduction admissions are not used.
