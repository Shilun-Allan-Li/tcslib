# Scope request: reuse doubling over concatenation

Request (2026-11-15): allow this one-line import in the new file
`TCSlib/Cryptography/SecureComputation/Yao/HybridProof/DescriptionDecoder.lean`:

```diff
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
```

Reason: the public proved `TCSlib.Cryptography.MultiMsg.dbl_append` at that module's line
235 states exactly `dbl (a ++ b) = dbl a ++ dbl b`. The decoder's streaming output
correctness needs the identity. Its home is outside the supplied import order. Reuse avoids
re-proving a merged public list identity. No frozen-file change is proposed. If approved,
add its TCSlib dependency closure to the module order and any new direct Mathlib roots to the
narrowed cache request. The decoder sub-agent identified this before any Lean check; its
unpublished local duplicate will be removed.

Question sent via request_user_input_async:
A second reuse scope request: may `Yao/HybridProof/DescriptionDecoder.lean` add
`import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine`? Its proved
`MultiMsg.dbl_append` is the exact encoding lemma the decoder needs, but the module is
outside the issued order. This adds no frozen-file edit.

User answer (verbatim): "Approve this helper import". Approved 2026-11-15.
