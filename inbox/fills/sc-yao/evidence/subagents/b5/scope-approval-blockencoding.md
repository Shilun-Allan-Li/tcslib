# Scope request: reuse the public challenge-list encoding identity

Question sent via request_user_input_async:
May `Yao/HybridProof/SelectedSlices.lean` import
`TCSlib.Cryptography.Asymptotic.BlockEncryptor`? Its public
`encodeList_eq_flatMap` supplies the challenge-list encoding identity needed by the B1
sampler. The module is outside the issued order; approval lets us reuse it instead of
duplicating its proof.

User answer (verbatim): "Yes". Approved 2026-11-15.

No frozen-file edit is proposed. Extend the narrowed dependency order and roots before use.
