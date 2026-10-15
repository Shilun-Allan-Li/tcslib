/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Applications
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Comparison
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.General
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.NoiseKernel
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Norms
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Tensorization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-product hypercontractivity

Finite-product definitions, general bounds, and applications.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Applications`: Product-space spectral and low-degree applications.
* `Basic`: Finite-product measures, norms, and coordinate noise.
* `Comparison`: Weighted norm interpolation and sharp comparison-constant limits.
* `General`: Product hypercontractivity bounds and coordinatewise tensorization.
* `NoiseKernel`: Product resampling kernels and first-norm contraction.
* `Norms`: Finite weighted Hölder inequality, norm recovery, and self-adjoint duality.
* `Tensorization`: Pairing and norm tensorization for finite nonnegative kernels.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
