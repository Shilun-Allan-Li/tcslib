import TCSlib.Cryptography.Asymptotic.Adversary
open TCSlib.Cryptography
example (w : List Bool) : padFin 1 w 0 = w.getD 0 false := by rfl
