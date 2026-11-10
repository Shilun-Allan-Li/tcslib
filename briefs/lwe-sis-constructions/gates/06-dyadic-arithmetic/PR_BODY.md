Fixed-width cryptographic values now have scalar addition, multiplication and
subtraction contracts modulo powers of two, assembled from the audited encoding
adapters and existing binary arithmetic machines. Subtraction reduces the right
operand before adding the modulus, so overlong operands retain their modular
meaning. Arbitrary templates, zero width and total malformed-input behavior are
explicit.

This statement draft has 18 declarations and twelve admitted obligations; only
the three complete defining equations are proved. A fresh serial 94-module sweep
passes. All 284 earlier constants preserve exact identity/axioms, and the sixteen
backing contracts have only standard axioms. Exactly twelve of the 302 owned
constants use `sorryAx`; style is 0 FAIL / 2 unchanged WARN over twenty files.
There are seventeen inherited admission warnings and no whole-root build claim.
Evidence and limits: `briefs/lwe-sis-constructions/gates/06-dyadic-arithmetic/`.

Target: `cryptography/lwe-sis-constructions`, with audited dependencies #236/#237/#238.
The user approves and merges. The new statement audit is not yet selected or
dispatched. Source-policy and relevant landing checks remain open. Shared-file
overlap is one Encoding facade import/contents entry in a separate commit; no
shared owner API, root export, host or pin is changed. No primitive-security
completion is claimed.
