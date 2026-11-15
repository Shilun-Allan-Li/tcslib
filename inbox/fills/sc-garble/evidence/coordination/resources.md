# Shared Mac resource coordination

Human authorization is preserved verbatim in `../scope-request/autonomy.md`.
All outgoing messages used Codex chat coordination, only for shared Mac scheduling.

- Ladner chat `01a1de61-f563-7962-b138-c28b6c56a109` initially reported a separate
  `.tcslib-scratch/locks` domain. I asked it to adopt the issued wrapper and default
  `~/.lean-slots`, one call per module, without interrupting an active Lean process.
  It temporarily reserved one issued slot while its old bootstrap controller finished.
  Its reply: “My bootstrap completed at 09:12:38 UTC and the temporary slot reservation
  has released automatically. I have left over ten seconds before checking again;
  all subsequent commands now use the issued wrapper per check with
  LEAN_SLOT_TAG=ladner-poly, plus a verified ps count after acquiring the slot.
  No more bootstrap reservation.”
- I notified derand chat `01a1de60-7647-7322-a442-5ea66c4694ee` of the lock-domain issue.
  It confirmed every command uses the issued slots, tag derand, and cache gets hold three.
- At 09:08 UTC a short sc-garble check was starved by rapid seq-zk module relaunches.
  I requested one 6–10 second gap from seq-zk chat `01a1de61-7f45-7013-9d73-94b218b90706`.
  Its bootstrap ended at 09:11:05; our check acquired at 09:11:06 and released at 09:11:08.
  The seq-zk lead confirmed later sweeps release between modules with six-second gaps.
- Ladner's completion reply: “All Lean checks completed successfully by 09:32:16 UTC,
  all own shared slots released, and no further Lean jobs are planned. No other worker's
  native Lean process was interrupted.”
- The final signature probe queued at 10:04:53 UTC behind a CPU-active seq-zk
  StatisticalRecursion check and a derand three-slot narrowed cache request with two
  partial reservations. I continued static proof and payload work. The seq-zk lead reported
  more than 6 GiB headroom, so this was not treated as E-RES. I requested rescheduling of
  only the waiting cache wrapper if needed, never killing another worker's Lean.
  Derand reported the cache completed in 7.89 seconds after acquiring all three slots,
  then released them. Our signature probe completed successfully at 10:15:33 UTC.

No other worker's file, process or lock was edited or removed. Every own Lean invocation
is in `../logs/slots.log`. The legacy Ladner reservation was an exception of that worker,
reported here because it affected shared scheduling; sc-garble never held a slot across modules.

2026-11-15 10:55–10:57 UTC: Requested a 6–10 second dispatcher boundary gap from derand
under the user's resource-coordination authorization. Derand reported pausing only its own
Python dispatchers, leaving native checks intact, and resuming at 10:57:31 after a 12-second
idle boundary. Our queued CoinBlocks check acquired 10:57:59 and finished normally. No other
worker's process or lock was touched by sc-garble.
