"""Build the sanity probes from the current units, and the negative controls from the probes."""
import sys, os
O = sys.argv[1]
w = os.path.join(O, "work"); pr = os.path.join(O, "probes")
def rd(p): return open(p, encoding="utf-8").read()
def wr(p, s): open(p, "w", encoding="utf-8").write(s)
s2 = rd(os.path.join(O, "Stage2.lean")) + rd(os.path.join(w, "s2probe_tail.lean"))
le = rd(os.path.join(O, "LanguageExtensions.lean")) + rd(os.path.join(w, "leprobe_tail.lean"))
wr(os.path.join(pr, "Stage2Sanity.lean"), s2)
wr(os.path.join(pr, "LanguageExtensionsSanity.lean"), le)
negs = [
 ("neg1", s2, "example : outAfter (xstep (W := 4) [.emit (-1)] [true, false, true] [] (XCfg.init 4 3)) = [true] := by",
  "example : outAfter (xstep (W := 4) [.emit (-1)] [true, false, true] [] (XCfg.init 4 3)) = [false] := by"),
 ("neg2", s2, "    = BitVec.ofInt 4 (-2) := by decide", "    = BitVec.ofInt 4 (-1) := by decide"),
 ("neg3", le, "example : inBitVal [false, true] 1 = 1 := by decide", "example : inBitVal [false, true] 1 = 0 := by decide"),
]
for name, src, a, b in negs:
    assert src.count(a) == 1, name
    wr(os.path.join(w, name + ".lean"), src.replace(a, b))
print("probes and negative controls rebuilt")
