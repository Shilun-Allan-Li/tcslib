# CP1 failed-log retention — bounded addendum

**No original diagnostic bodies located for any of the 30 failed dev attempts in the frozen CP1 logs. Two console summaries survive.** This is a result about the delivered payload only, not proof of permanent loss on the worker's host or in its session/backups. The frozen report is unchanged.

Delivery: `8b133945c3ba4aa7abb3b896bec38441535959b2`. Root reports the original review recorded at `388f89436a0b1f216a4970d665c3cedbcb152e47`; unchanged local report SHA-256 `42cee1bd5caae6d24779af76ca563838125c8f27843d2202ef0d7d0ba2fc2e18`.

Read all 2,589 delivered .log files (3,223,728 bytes), the three retained dev console segments, chain console, checker and relevant shell drivers as data. The own read-only script checks every FAIL row's full source hash/start, native error headers for its exact original module source, and its exact printed status summary. It does not execute or import supplied tools. No Lean/cache/build/apps/source/Git mutation occurred.

## Exact coverage result

- All 30 FAIL rows retain metadata in checks-dev.jsonl, including start/end, PID, source digest, return code, error count and prerequisite identities.
- No delivered raw .log contains any of those 30 start timestamps or source digests. No native error header in the delivered logs names any of those attempts' original source modules. No standalone unlocated `error:` line was found. Thus no complete or partial original diagnostic body could be matched to an exact failed attempt in these logs.
- Row 739 (OneWayLemmas, start 2026-11-08T05:20:45.400651+00:00, PID 20645, source 528e42fdf7c7a5592e73ddb7d6078cf2ca28be8fb6808a73da64ae4c25ba6283) has a matching FAIL summary at `devrun-j2-part1.log:462`: rc 1 / errors 2 / fresh False/2.8s/2542MiB. Row 748 (Concrete, start 2026-11-08T05:25:07.386405+00:00, PID 23402, source f80013900104f838bc4987d57bb2fb8625d0f48ef79775dca13556e76e77c0b0) has a matching summary at `devrun-j2-part2.log:16`: rc 1 / errors 1 / fresh False/4.3s/2738MiB. These are count/status summaries, without Lean messages, source hashes or start timestamps in the console itself; matching the rest of the row is not independent console provenance of the source/start.
- The other 28 attempts have metadata-only coverage in this delivered set. The part 3 console has only successful checks; the chain starts after the dev pass succeeds. Other sealed-probe diagnostics were not credited as original development errors: their source paths and attempts differ.

chk.py:77–83 sends raw child stdout/stderr into the per-module file. Its line 92 prints only the one-line status/error count, and devrun.sh relays that output. Therefore a retained dev console segment normally preserves that summary, not the native diagnostic body. `lasterr.sh` can print error excerpts to the worker's interactive output, but no separately saved output of that command is delivered; this is one possible external recovery source rather than a delivered coverage match.

## Qualification of W2

Use: **“The immutable CP1 delivery contains no located original raw diagnostic bodies for its 30 failed development attempts; metadata survives for all 30 and console summaries for two. The referenced module logs were replaced by later successful logs. Originals may still exist outside this payload and could be supplied in a separately pinned supplement.”**

Do not repeat a global assertion that the diagnostics are permanently unrecoverable. The frozen report's “permanent” wording is too broad if understood as a claim about the worker's filesystem/session/backups. Even if originals are later supplied, the CP1 path-overwrite behavior and the need for unique future attempt paths/log hashes remain. A supplemental record should match exact attempt/source/start and distinguish original raw logs from later reconstruction. No worker contact or request was sent by this review.

## Attempt-by-attempt index

The full JSON retains each source path, hash, complete start/end, PID, parsed count, current replaced log start, and exact match locations. Here “summary” means only the status line described above; every row has zero located original diagnostic bodies.

| Dev row | PID | Module | Start (UTC) | Source SHA-256 | Reported errors | Delivered coverage |
|---:|---:|---|---|---|---:|---|
| 6 | 15128 | `TCSlib/Complexity/Randomized/Build/StringLoops` | `2026-11-08T01:35:20.096848+00:00` | `c8318f5f9b582482d3c72e898f56e22208682d39305b3acb9883e393b69592e7` | 4 | metadata-only |
| 9 | 15334 | `TCSlib/Complexity/Randomized/Repetition` | `2026-11-08T01:35:51.004048+00:00` | `65778010a92603f92b2e60105f85be72334a1f490e3b2c3cdd6c589d4ae430ab` | 2 | metadata-only |
| 10 | 15407 | `TCSlib/Complexity/Randomized/Repetition` | `2026-11-08T01:36:08.497425+00:00` | `81d4252665ecb8d06ee518e803fd2f8657c20ae0995523a14dc507b34e8db2f1` | 1 | metadata-only |
| 67 | 17345 | `TCSlib/Cryptography/Asymptotic/PRF` | `2026-11-08T01:44:17.840162+00:00` | `2a7d89d21aa207f46bc66f05c7e6b64e09479574b170d5ca966f3a72622cbf74` | 2 | metadata-only |
| 70 | 31312 | `TCSlib/Complexity/Randomized/Classes` | `2026-11-08T02:43:31.902000+00:00` | `a8077b5e3c871d3137ea1dc68101c11aa26ebf0abe9a2bcfda02ce38f3cabf95` | 1 | metadata-only |
| 73 | 31637 | `TCSlib/Complexity/TuringMachine/Configuration` | `2026-11-08T02:45:13.356388+00:00` | `47d8cea632fbb595c3a1a503cc624e4af36837e5b25e5d311a4fea079f912672` | 6 | metadata-only |
| 75 | 31908 | `TCSlib/Complexity/TuringMachine/Deterministic` | `2026-11-08T02:46:49.945971+00:00` | `bd79d919f3339b072725f3e8bfe8e7b5286634c3efdc1f3e45990ef4e631d9bb` | 1 | metadata-only |
| 78 | 32144 | `TCSlib/Complexity/TuringMachine/Simulation` | `2026-11-08T02:48:10.498775+00:00` | `f4bf39081d3f25437653dbf45687188f16c68d29f299c8e171530df47d14b371` | 4 | metadata-only |
| 83 | 32470 | `TCSlib/Complexity/TuringMachine/Build/ModuleHost` | `2026-11-08T02:50:10.470234+00:00` | `ceb9288ec1d3354b91bdac6b3ebd74a1a7b3014348d7e47dbe5d4cd3da8c608b` | 2 | metadata-only |
| 89 | 390 | `TCSlib/Complexity/Randomized/PPT` | `2026-11-08T02:52:32.239026+00:00` | `3ecc7cca65affe5ba7f53ec47939eb5dcd08507d0b4fa774652dc60c73e04c58` | 1 | metadata-only |
| 91 | 650 | `TCSlib/Complexity/Randomized/NonUniform` | `2026-11-08T02:54:26.433839+00:00` | `7ee5d2ddc8131a8dd53d43b711471cb4b624ca6f905e9a850016a45a0615f00d` | 1 | metadata-only |
| 110 | 1311 | `TCSlib/Cryptography/HardcoreBit/InnerProduct` | `2026-11-08T02:57:21.126077+00:00` | `7129a5422e47ebe3fa99ba677886f2d8787ac0a85351f9d37ffd94fd76768389` | 1 | metadata-only |
| 121 | 1880 | `TCSlib/Cryptography/Asymptotic/Collections` | `2026-11-08T03:00:51.073012+00:00` | `11e8e80d97e9d394801d3d26738cdaa740dcdc4099c9d2ba6a94237e764722b6` | 2 | metadata-only |
| 126 | 2164 | `TCSlib/Cryptography/Candidates/DiscreteLogHardcore` | `2026-11-08T03:01:56.273603+00:00` | `6b1b9b27110bac66e200dcc0de5ce40d1701e340397589c9069c78f946507a57` | 2 | metadata-only |
| 132 | 2561 | `TCSlib/Cryptography/Pseudorandom/Indistinguishability` | `2026-11-08T03:04:20.515076+00:00` | `bad4e58a7f017f1008ac15c863f155d0dc9a8767c80ae61c1723d52a5af82e3b` | 1 | metadata-only |
| 172 | 5792 | `TCSlib/Cryptography/Asymptotic/OneWay` | `2026-11-08T03:09:11.129414+00:00` | `d4cdfc8540bafb38431802bac88d0d11ee1b91d184eab897941959c5b958e26b` | 3 | metadata-only |
| 214 | 7113 | `TCSlib/Cryptography/Asymptotic/Collections` | `2026-11-08T03:13:46.491152+00:00` | `ff04c74301003e7b692b73de11b3e01303fbab871f356cdc02b7eaec0e5f7fc4` | 1 | metadata-only |
| 225 | 9618 | `TCSlib/Cryptography/Asymptotic/EnsemblesLemmas` | `2026-11-08T03:16:42.831673+00:00` | `4de1ad71a4bb0db705787a07d7dbffe391949de1dbc0d97a103c36fbb11a643f` | 4 | metadata-only |
| 226 | 11961 | `TCSlib/Cryptography/Asymptotic/OneWay` | `2026-11-08T03:19:42.187202+00:00` | `c38496e684a9d8ea5c1a86134d3c999003dcc41d169efbcacd2c5ba9e12e07c9` | 2 | metadata-only |
| 243 | 12883 | `TCSlib/Cryptography/Asymptotic/Encryption` | `2026-11-08T03:25:23.940124+00:00` | `d92f16b09d4738e4bd0dcb1f29d8fa71d38e992cac698cc06af6324a8dd63318` | 1 | metadata-only |
| 245 | 13167 | `TCSlib/Cryptography/Asymptotic/BlockEncryptor` | `2026-11-08T03:27:49.950119+00:00` | `b417a0c4d171adc5373b2af869af4eac661daacf4e34da5d4a3a63f283ae52a3` | 28 | metadata-only |
| 248 | 13494 | `TCSlib/Cryptography/Asymptotic/HardCoreLemmas` | `2026-11-08T03:30:37.066975+00:00` | `ffc332b1508cb093f7e805aea1f5d17abb6316c3cdad9510af92bd739f4a10ed` | 1 | metadata-only |
| 253 | 13888 | `TCSlib/Cryptography/Asymptotic/HardCoreCollection` | `2026-11-08T03:33:45.489235+00:00` | `433609065f288819dd4e62ba6ed34cd7c633abb25ea5b931c9c376c14b57c915` | 1 | metadata-only |
| 254 | 14067 | `TCSlib/Cryptography/Asymptotic/HardCoreCollection` | `2026-11-08T03:35:36.742732+00:00` | `9383237386547a5437600a266bb92e2b2dd1a224d8a6c218973c84f37b47c34b` | 5 | metadata-only |
| 259 | 14463 | `TCSlib/Cryptography/Asymptotic/GGMReduction` | `2026-11-08T03:38:28.850557+00:00` | `38172a94cb7f540d809e6793450cd78db4a1076935d37f3c2a66929bfb3b7c1d` | 4 | metadata-only |
| 355 | 17098 | `TCSlib/Cryptography/ZeroKnowledge/NP` | `2026-11-08T03:48:22.947999+00:00` | `651b34977206bc2e298cbbe06bec17962b008057c17bd0d65859e0a3c9fddaa0` | 3 | metadata-only |
| 507 | 7240 | `TCSlib/Complexity/ClassNP/PolyTimePairing` | `2026-11-08T04:33:13.437563+00:00` | `da8a0cf2e709b13a7481f1725dd247b05f335fc462bb5432bb9e9bfd8860c562` | 1 | metadata-only |
| 739 | 20645 | `TCSlib/Cryptography/Asymptotic/OneWayLemmas` | `2026-11-08T05:20:45.400651+00:00` | `528e42fdf7c7a5592e73ddb7d6078cf2ca28be8fb6808a73da64ae4c25ba6283` | 2 | summary-only |
| 748 | 23402 | `TCSlib/Cryptography/Candidates/Concrete` | `2026-11-08T05:25:07.386405+00:00` | `f80013900104f838bc4987d57bb2fb8625d0f48ef79775dca13556e76e77c0b0` | 1 | summary-only |
| 749 | 23787 | `TCSlib/Cryptography/Candidates/Concrete` | `2026-11-08T05:29:50.992500+00:00` | `3633e5fc3646a279b9cfab1951e0cace18d24d0c30c5ea6d52396b35e694dd4b` | 1 | metadata-only |

The raw-log inventory is bound by a canonical path/byte-count/SHA-256 inventory digest in failure-log-addendum.json. Reproduce only with the independently authored `python3 -I check_failure_log_alternates.py`; no incoming program is used.

**Not yet clear to merge — this addendum narrows the historical evidence-loss claim; CP1 remains partial.**
