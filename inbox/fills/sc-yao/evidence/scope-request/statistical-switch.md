# Scope request: reuse the published expectation-switch inequality

Proposed extra import in the new helper
`TCSlib/Cryptography/SecureComputation/Yao/HybridProof/StatisticalSwitch.lean`:

```diff
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
```

The brief lists `MultiMsg.abs_uexp_sub_le_uprob` among its published interfaces, but its
home module is missing from the supplied order. It bounds the difference of expectations
by the probability that their integrands differ. Reusing it closes the generic statistical
switch without re-proving probability machinery. The exact extra dependency closure and
Mathlib roots are recorded in evidence/logs/probability-order.log.

Question sent via request_user_input_async:
Scope request: may `Yao/HybridProof/StatisticalSwitch.lean` import
`TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas` to reuse
`MultiMsg.abs_uexp_sub_le_uprob`? The brief lists this public interface, but its module is
missing from the supplied order. I’ll extend the narrowed dependency checks for it.

User answer (verbatim): "Approve this probability-helper import". Approved 2026-11-15.
