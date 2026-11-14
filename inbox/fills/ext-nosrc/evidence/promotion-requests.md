# Consolidated promotion requests

These requests respect the fill's exclusive ownership: no shared provider file is edited.
All owned definitions have public readers beside them. No reader request remains blocking.

- Promote the generic finite-distribution families enumerated in `rejection-review.md`:
  uniform pushforward, map/expectation/probability readers, product pushforward, probability
  bounds, tuple decomposition, first-success laws, accepted-flat calculations, convex mixtures
  and source preservation. Proposed homes: InformationTheory/FinDist, Samples, Entropy and a
  shared finite rejection-sampling module.
- Promote `RejectionSampler.take_poly` to Complexity/ClassNP/PolyTimePrefix. Promote the
  bounded selector, polynomial-time construction, block correspondence and machine/coin
  reader families enumerated in `sampler-review.md` to a shared uniform-sampler layer.
- Promote the owned uniform-machine family: `uniformSampler`, `uniformSampler_coins`,
  `uniformSampler_uniform`, `uniformSampler_runAt`, `uniformSamplerCoins`,
  `uniformSamplerCoins_eq`, `uniformSamplerCoins_ofFn` and `samplerLaw_uniformSampler`.
  The machine and coin identification belong in the uniform-sampler layer; its FinDist law
  belongs in the corresponding cryptographic sampling bridge.
- Promote `uniform_one_probTrue` to the one-bit finite-probability API and
  `uniform_card_div_quarter` to bit-source entropy arithmetic.
- Consider relocating the already-public `FunFamily.ofFn_blocks_symm` from Asymptotic/OneWay
  to the common block/list API. Sampler imports its public provider instead of copying it;
  relocation would reduce future dependency closures.

The efficient-source membership, extractor-specific lower bound, first-bit reader and law
bridge are local consumers of the owned definitions and remain with Extraction.

Overlap: none. No private foreign proof is copied or re-derived from its implementation.
See the separate search logs and independent review for the precise reuse audit.
