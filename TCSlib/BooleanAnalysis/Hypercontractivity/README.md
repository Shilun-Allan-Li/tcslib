# Hypercontractivity

Import `TCSlib.BooleanAnalysis.Hypercontractivity` for the whole development, or import
one of the folder facades below for a narrower dependency.

| Module | Contents |
| --- | --- |
| `Parameters`, `MomentBounds` | Shared probability moments and reasonability bounds |
| `Cube` | Forward and reverse inequalities for the uniform Boolean cube |
| `RandomVariables` | General, symmetric, multilinear, and discrete random variables |
| `RandomVariables.Sharp` | Scalar, finite-space, and finite-law sharp discrete bounds |
| `Products` | Finite-product definitions, bounds, and applications |
| `Randomization` | Randomized Fourier components and notable coordinates |
| `SharpThresholds` | Boosters, pseudo-juntas, and sharp-threshold statements |
| `Applications` | Small-set expansion, low-degree consequences, stable influences, and KKL |

Definition modules support narrow imports. `Cube.General` progresses from kernels through
tensorization and duality to scalar estimates and the final bounds. `Cube.Reverse` progresses
from extended power means through the two-point estimate, tensorization, reverse Hölder,
and exponent extensions to the final two-function inequality.

The random-variable development builds on `RandomVariables.Basic`. Its multilinear proof
is in `Polynomial`; independent sums are in `General`; discrete bounds and optimality are
in `Discrete`. The sharp proof separates scalar calculus, finite-space contraction, and
transfer to random-variable laws, so each stage can be reused independently.

Declarations share the namespace `BooleanAnalysis.Hypercontractivity`. Technical layers use
the inner namespaces `FiniteProduct`, `FiniteLaw`, `Tensorization`, and `SharpDiscrete`.
Interpolation and reverse-moment helpers use their own inner namespaces.
