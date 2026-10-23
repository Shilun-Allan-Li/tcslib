#!/bin/bash
W=$1; P=TCSlib/Complexity/TuringMachine/Build
while read rev path; do
  b=$(git -C $W rev-parse "$rev:$path")
  n=$(git -C $W cat-file -p $b | wc -l | tr -d ' ')
  w=$(git -C $W cat-file -p $b | python3 -I -c 'import sys; print(max(len(l.rstrip("\n")) for l in sys.stdin))')
  echo "$rev $path blob=$b lines=$n maxwidth_chars=$w"
done <<LIST
126127b8959e4b64b37ac8ed15c0b1b05d747c9e $P/SeamLayout.lean
7cd01f8459f214b844877c63ccc7534a911346cf $P/SeamLayout.lean
bfe3e0237e5dbedd4e6be2be1127160a980deae9 $P/SeamLayout.lean
1c06ea94 $P/SeamLayout.lean
0416ffea $P/SeamLayout.lean
8114e482fcad1f1d07abdcc244ef74755b752b56 $P/InputDevice.lean
b26d53c955cf81e2e01d68f66ba636efe10996e8 $P/InputDevice.lean
34af2e0f $P/InputDevice.lean
13e1758929aa0eb3f298a8dd399e3dbc4bd809c0 $P/ZoneRebalance.lean
43d22595 $P/ZoneRebalance.lean
LIST
