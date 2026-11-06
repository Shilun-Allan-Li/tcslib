# usage: python3 -I mkcontrol.py <in> <out> -- append the two rfl controls inside the namespace
import sys
src=open(sys.argv[1]).read()
ctrl='''
/-- Seal control: `dlP` read by definitional unfolding. -/
example (i : List Bool) : dlP i = listToNat (pairFstD i) := rfl
/-- Seal control: `PolyExpr.eval` read by definitional unfolding. -/
example (n : ℕ) : PolyExpr.var.eval n = n := rfl

end TCSlib.Cryptography.Candidates
'''
end="\nend TCSlib.Cryptography.Candidates\n"
assert src.rstrip().endswith("end TCSlib.Cryptography.Candidates")
i=src.rindex("end TCSlib.Cryptography.Candidates")
open(sys.argv[2],'w').write(src[:i]+ctrl.lstrip("\n"))
