# usage: python3 -I mkseal.py <owned file> <names file> <out>  -- whole-file seal after the `open` line
import sys
src=open(sys.argv[1]).read(); names=[l.strip() for l in open(sys.argv[2]) if l.strip()]
anchor="open Complexity Turing NumberTheory Finset\n"
assert src.count(anchor)==1
seal="\nattribute [local irreducible] "+" ".join(names)+"\n"
open(sys.argv[3],'w').write(src.replace(anchor, anchor+seal))
