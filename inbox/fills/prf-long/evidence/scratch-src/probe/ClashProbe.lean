import TCSlib.Cryptography.Asymptotic.BlockEncryptor

/-! prf-long fill, clash probe: with `Asymptotic/BlockEncryptor` (the public
`TCSlib.Cryptography.encodeList_eq_flatMap`) in the import closure, the frozen private
`encodeList_eq_flatMap` of `FromPRF.lean` (same namespace, same name) can no longer be declared.
Expected: exactly one error, "a non-private declaration … has already been declared". -/

namespace TCSlib.Cryptography

private theorem encodeList_eq_flatMap : True := trivial

end TCSlib.Cryptography
