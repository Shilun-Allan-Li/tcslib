# Own-check serialization and source snapshot correction

Two own check drivers were accidentally queued at once: b2-uniform-bound-02 and
b2-corollaries-01. The host wrapper serialized their Lean runs, in the opposite order.
The slots log proves acquisition/release intervals 10:42:34–10:42:44 UTC and
10:42:45–10:42:51 UTC. Thus there were no simultaneous Lean writers to this olean tree.

Both actual checks read the completed Garbling.lean source written before 10:41:39 UTC;
no Garbling.lean edit occurred between then and both completed checks. Both passed with
zero errors and zero sorry warnings. Their earlier source snapshots had been copied at
queue time, so those copies did not necessarily represent the source read by Lean.

The original queue-time copies are retained as *.source.queued.lean.txt, and the actual
source used in the controlled no-edit interval is retained as *.source.lean. A new serial
check is run after this correction. Future drivers take a nonblocking, worktree-local
flock to prevent multiple own check drivers; source snapshots are copied by check_one.sh
inside the host slot, immediately before the module check. The local lock does not reserve
host Lean slots between modules. No other worker's process or lock was touched.

At 11:02 UTC the own NestedBounds check PID 27209 was interrupted with SIGINT after
roughly three minutes of CPU time and increasing RSS (4.48 GB), with no diagnostic output.
Only that verified sc-garble Lean PID was signaled. Its raw failure log is retained; the
next diagnostic run applies a local heartbeat limit to the new collision corollary so
an elaboration hotspot can be located before another unrestricted check.
