import TCSlib.Cryptography.Candidates.RSA
open TCSlib.Cryptography.Candidates
-- after E2: the instance is no longer visible to importers (expected: failed to synthesize)
example {m : ℕ} (P : RSAParams m) : NeZero P.N := inferInstance
