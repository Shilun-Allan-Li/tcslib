import TCSlib.Cryptography.LWE.BitEncoding
set_option autoImplicit false
namespace TCSlib.Cryptography.LWE.BitEncoding
-- Rule 10 control (neg): reads `TCSlib.Cryptography.LWE.BitEncoding.decodeLo` of TCSlib.Cryptography.LWE.BitEncoding from another file through its body
example (P : Parameters) : decodeLo P = P.modulus / 2 / 2 + 1 :=
  rfl
end TCSlib.Cryptography.LWE.BitEncoding
