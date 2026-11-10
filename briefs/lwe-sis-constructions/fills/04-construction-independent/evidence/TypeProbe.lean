import TCSlib.Cryptography.Encoding
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
import TCSlib.Cryptography.Encryption
import TCSlib.Cryptography.Hashing
import TCSlib.Cryptography.Pseudorandom
import TCSlib.Cryptography.TrapdoorFunctions

open Lean in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.toString.startsWith "TCSlib.Cryptography.Encoding." ||
          mod.toString.startsWith "TCSlib.Cryptography.LWE." ||
          mod.toString.startsWith "TCSlib.Cryptography.SIS." ||
          mod.toString.startsWith "TCSlib.Cryptography.Encryption.Symmetric.Regev." ||
          mod.toString.startsWith "TCSlib.Cryptography.Hashing.SIS." ||
          mod.toString.startsWith "TCSlib.Cryptography.Encryption.PublicKey.Regev." ||
          mod.toString.startsWith "TCSlib.Cryptography.Pseudorandom.Generators.LWE." ||
          mod.toString.startsWith "TCSlib.Cryptography.TrapdoorFunctions.Lossy." ||
          mod.toString.startsWith "TCSlib.Cryptography.TrapdoorFunctions.AllButOne." then
        let payload := Json.arr #[Json.str n.toString,
          Json.str (reprStr ci.levelParams), Json.str (reprStr ci.type)]
        logInfo m!"RAW_TYPE|{payload.compress}"
