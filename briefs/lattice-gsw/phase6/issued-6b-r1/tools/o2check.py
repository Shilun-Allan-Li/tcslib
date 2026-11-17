"""o2check.py (gsw-6b-statements staging, issued-6b-r1): a numerical check of O2's interval form of decoding.
Plan section r3 §H5.8 fixes, with h = q/2 (floor), decodeLo = h/2 + 1 and decodeHi = (q + h + 1)/2 (floors), and
states decode v = true <-> decodeLo <= v.val < decodeHi. BitEncoding.decode (LWE/BitEncoding.lean:108) is
decide (distance v (codepoint true) < distance v (codepoint false)), distance x y = |valMinAbs (x - y)|,
codepoint true = h, codepoint false = 0, and Mathlib's ZMod.valMinAbs sends x to x.val if x.val <= q/2 and to
x.val - q otherwise. This script compares both sides for every residue of every modulus 2 <= q <= QMAX (default
2000) and prints the number of mismatches. Evidence for the brief, not a proof. Usage: o2check.py [QMAX]."""
import sys
QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
def vma(x, q):
    x %= q
    return x if x <= q // 2 else x - q
bad = 0
for q in range(2, QMAX + 1):
    h = q // 2; lo = h // 2 + 1; hi = (q + h + 1) // 2
    for v in range(q):
        if (abs(vma(v - h, q)) < abs(vma(v, q))) != (lo <= v < hi):
            bad += 1
print(f'moduli 2..{QMAX}: {bad} mismatches')
