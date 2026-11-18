import TCSlib.Cryptography.LWE.Efficient
import TCSlib.Cryptography.SIS.Efficient
/-! D1-P3 probe (evidence only): the `noise_efficient` field of `dyadicExample` is a proof term,
not an assumption; its axioms are the standard three (or a subset). -/
open TCSlib.Cryptography
def d1p3_noise_efficient := LWE.dyadicExample.noise_efficient
def d1p3_params_uniform := LWE.dyadicExample.params_uniform
def d1p3_noiseInput_uniform := LWE.dyadicExample.noiseInput_uniform
def d1p3_sis_params_uniform := SIS.dyadicExample.params_uniform
#print axioms d1p3_sis_params_uniform
#print axioms d1p3_noise_efficient
#print axioms d1p3_params_uniform
#print axioms d1p3_noiseInput_uniform
