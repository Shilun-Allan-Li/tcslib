/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.CoinSampling.Basic
import TCSlib.Cryptography.CoinSampling.Buckets
import TCSlib.Cryptography.CoinSampling.Transfer
import TCSlib.Cryptography.CoinSampling.Asymptotic
import TCSlib.Cryptography.CoinSampling.Instances
import TCSlib.Cryptography.CoinSampling.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coin sampling: exact non-dyadic laws from fair coins, with perfect correctness kept

Experiments in the library are stated with exact laws: a uniform draw `Games.ProbComp.sample Ω`
of a finite type (uniform `ℤ_q` for any `q`, the seeds of `LWE.Noise`, rational seeds) and its
pushforwards. Machines have fair coins only, and `|Ω|` is rarely a power of two. This area
connects the two, keeping every every-outcome property (perfect correctness, injectivity on
reachable encodings) exact:

* **per sampler**, `CoinSampler Ω s`: a decoder from `s` fair coins to `Option Ω`, exact on
  success, with derived failure probability; the bucket sampler `bucket N s` (one draw
  `x < 2^s`, accepted below `⌊2^s/N⌋·N`, output `x mod N`) fails with probability
  `(2^s mod N)/2^s < N/2^s`;
* **per experiment**, `Games.ProbComp.Close` (`TCSlib.Cryptography.Games.Closeness`): replacing
  exact draws by coin draws anywhere in a game moves every acceptance probability by at most the
  summed failure probabilities;
* **correctness**, `Games.OracleComp.OutputsSubset`: with a default value as the fallback, every
  `AllOutputs` property transfers unchanged;
* **asymptotics**, `drawSlack`: `q(κ)` draws with `t(κ) ≥ κ` slack bits are negligible and
  `SubexpSmall c` for every `c < 1`;
* **efficiency**, `UniformSampler`: one polynomial-time string map reading the modulus from its
  input, whose machine `NUPPT.ofPolyTimeUniform` is a PPT (no advice, no κ-indexed programs, no
  hard-wired modulus); `bucketSampler` is built from the proved `Complexity.BinArith` arithmetic.

## Contents

* `TCSlib.Cryptography.CoinSampling.Basic`: the contract `CoinSampler`, the mixture identity,
  closeness to the exact draw, transport, independent draws, the rejection sampler as an
  instance.
* `TCSlib.Cryptography.CoinSampling.Buckets`: the bucket sampler, its exact failure and the
  slack-bit bound, enumerations, rational seeds and weighted buckets.
* `TCSlib.Cryptography.CoinSampling.Transfer`: coin draws in games; closeness of one draw, of a
  draw per oracle query, and output inclusion of default-fallback draws.
* `TCSlib.Cryptography.CoinSampling.Asymptotic`: the summed slack `q(κ)·2^{-t(κ)}`, negligible
  and subexponentially small.
* `TCSlib.Cryptography.CoinSampling.Instances`: residues modulo any `q`, noise seeds, the LWE
  seed and the LWE challenge from fair coins.
* `TCSlib.Cryptography.CoinSampling.Efficiency`: `UniformSampler`, its uniform machine, and the
  polynomial-time bucket decoder.
-/
