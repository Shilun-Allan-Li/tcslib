/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecretSharing.Defs
import TCSlib.Cryptography.SecretSharing.Interpolation
import TCSlib.Cryptography.SecretSharing.Shamir
import TCSlib.Cryptography.SecretSharing.Sharing
import TCSlib.Cryptography.SecretSharing.Vector

/-!
# Secret sharing

Shamir's threshold scheme, together with the scheme-independent definitions it is an instance of
and the polynomial-counting lemmas it is proved from.

## Contents

* `TCSlib.Cryptography.SecretSharing.Defs`: monotone access structures, the data of a secret
  sharing scheme, correctness and perfect privacy.
* `TCSlib.Cryptography.SecretSharing.Interpolation`: counting polynomials of bounded degree
  through prescribed points; reusable for any "random low-degree polynomial" argument.
* `TCSlib.Cryptography.SecretSharing.Shamir`: the `k`-out-of-`n` scheme, its correctness and its
  perfect privacy.
* `TCSlib.Cryptography.SecretSharing.Sharing`: the algebra of share vectors — closure under
  addition, scaling and multiplication, and reconstruction as a linear functional.
* `TCSlib.Cryptography.SecretSharing.Vector`: sharing a vector of secrets, with joint privacy.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
* [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011.
-/
