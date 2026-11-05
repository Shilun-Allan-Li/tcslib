# The landing head's screen (gate 93)

`screen-ed-pairs.py` is the v3 copy-text screen (`scripts/copy-text-screen-v3.py`) restricted to pairs
with an `NTimeDiagonalizer` declaration on one side (one added line; the NF cont1 review's
`screen-nf-pairs.py` with the file name changed). It ran over the brief's 38-file population
(`population.txt`) on a `git archive` export of #188's head `dae7929c` (`status.txt`).

Result: 177 pairs with the owned file (`screen-land-ed-pairs.txt`). The review's full head screen
(`campaign/fills/eq/reviews/ed-fill/out/17-screen-head.txt`) restricted to the same pairs gives the
same 177 lines (`head-ed-pairs.txt`, `land-ed-pairs.txt`; `head-vs-land.diff` shows only the
summary line, which the filtered head list lacks). The landing edits E1–E7 and the merge add and
remove no pair.
