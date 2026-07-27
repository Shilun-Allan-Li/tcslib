<!-- generated-by: proofmatch Codex repair -->
<!-- source-pdf-sha256: 20e15a3d3d5e94a7b8771247aadec17f0ea241a8e4cd9335baa9c1fc7a2cfaf0 -->

<a id="pdf-20e15a3d3d5e-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
# Chapter 3
## Spectral structure and learning

<a id="pdf-20e15a3d3d5e-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.99 -->
## 3.1. Low-degree spectral concentration

<a id="pdf-20e15a3d3d5e-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.99 -->
**Definition 3.1.** We say that the Fourier spectrum of `f : {−1,1}ⁿ → ℝ` is `ε`-concentrated on degree up to `k` if

`W^{>k}[f] := ∑_{S⊆[n], |S|>k} f̂(S)² ≤ ε`.

For `f : {−1,1}ⁿ → {−1,1}`, this is equivalently `Pr_{S∼S_f}[|S|>k] ≤ ε`.

<a id="pdf-20e15a3d3d5e-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.99 -->
A concentration result can be shown combinatorially by proving that the function has small total influence.

<a id="pdf-20e15a3d3d5e-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.96 -->
**Proposition 3.2.** For any `f : {−1,1}ⁿ → ℝ` and `ε > 0`, the Fourier spectrum of `f` is `ε`-concentrated on degree up to `I[f]/ε`.

<a id="pdf-20e15a3d3d5e-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
This follows immediately from Theorem 2.38, `I[f] = E[|S|]` for the spectral sample. For Boolean functions, this is Markov’s inequality applied to the cardinality of the spectral sample. For example, `I[Tribes_{w,2w}] = O(log n)` (Exercise 2.13), so its spectrum is `.01`-concentrated on degree up to `O(log n)`. Explicit Fourier calculation would be painful.

<a id="pdf-20e15a3d3d5e-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.99 -->
**Proposition 3.3.** For any `f : {−1,1}ⁿ → {−1,1}` and `δ ∈ (0,1/2]`, the Fourier spectrum of `f` is `ε`-concentrated on degree up to `1/δ` for

`ε = 2/(1−e^{−2}) NS_δ[f] ≤ 3 NS_δ[f]`.

<a id="pdf-20e15a3d3d5e-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.88 -->
Using Theorem 2.49,

`2 NS_δ[f] = E_S[1 − (1−2δ)^{|S|}] ≥ (1−(1−2δ)^{1/δ}) Pr[|S|≥1/δ] ≥ (1−e^{-2}) Pr[|S|≥1/δ]`.

The first inequality uses that `(1−2δ)^k` is nonincreasing in `k`; the claim follows. As an example, Theorem 2.45 gives `NS_δ[Maj_n] ≲ √δ`, so `Maj_n` is `3√δ`-concentrated up to degree `1/δ`, equivalently `ε`-concentrated up to degree `9/ε²`. There is no simple converse to Proposition 3.2: majority has constant-degree concentration but total influence `Θ(√n)`.

<a id="pdf-20e15a3d3d5e-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.96 -->
**Theorem 3.4.** Suppose `f : {−1,1}ⁿ → {−1,1}` has `deg(f) ≤ k`. Then `f` is a `k2^{k−1}`-junta.

<a id="pdf-20e15a3d3d5e-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.92 -->
The bound `k2^{k−1}` cannot be significantly improved (Exercise 3.24). The key lemma is Lemma 3.5.

<a id="pdf-20e15a3d3d5e-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.99 -->
## 3.2. Subspaces and decision trees

<a id="pdf-20e15a3d3d5e-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.99 -->
**Lemma 3.5.** Suppose `deg(f) ≤ k`, where `f : {−1,1}ⁿ → ℝ` is not identically `0`. Then `Pr[f(x) ≠ 0] ≥ 2^{−k}`.

<a id="pdf-20e15a3d3d5e-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.99 -->
**Proposition 3.6.** If `f : {−1,1}ⁿ → {−1,1}` has `deg(f) ≤ k`, then `Inf_i[f]` is either `0` or at least `2^{1−k}` for all `i ∈ [n]`.

<a id="pdf-20e15a3d3d5e-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.92 -->
By Proposition 3.6, the number of coordinates with nonzero influence is at most `I[f]/2^{−k}`. Fact 3.7 gives `I[f] ≤ deg(f)`, so this is at most `k2^{k−1}`. Thus `f` is a junta on those coordinates.

<a id="pdf-20e15a3d3d5e-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.96 -->
Identify characters with vectors `γ ∈ F₂ⁿ`: `χ_γ(x)=(-1)^{γ·x}` and `χ_βχ_γ=χ_{β+γ}`. Thus

`f(x)=∑_{γ∈F₂ⁿ} f̂(γ)χ_γ(x)`.

<a id="pdf-20e15a3d3d5e-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.96 -->
**Definition 3.8.** The Fourier `p`-norm is

`||f̂||_p = (∑_{γ∈F₂ⁿ} |f̂(γ)|^p)^{1/p}`.

Counting measure is used. Parseval gives `||f||_2 = ||f̂||_2`.

<a id="pdf-20e15a3d3d5e-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
**Definition 3.9.** `sparsity(f)=|supp(f̂)|=#{γ:f̂(γ)≠0}`.

**Definition 3.10.** `f` is `ε`-granular if every `f̂(γ)` is an integer multiple of `ε`.

<a id="pdf-20e15a3d3d5e-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.96 -->
For a subspace `A≤F₂ⁿ`, define `A⊥={γ:γ·x=0 for all x∈A}`. Then `dim A⊥=n−dim A` and `(A⊥)⊥=A`.

<a id="pdf-20e15a3d3d5e-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.93 -->
**Proposition 3.11.** If `A≤F₂ⁿ` has codimension `k`, then

`1_A = 2^{−k} ∑_{γ∈A⊥} χ_γ`,

and the probability density `φ_A=2^k1_A` has Fourier expansion `φ_A=∑_{γ∈A⊥}χ_γ`.

<a id="pdf-20e15a3d3d5e-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.95 -->
Let `γ₁,…,γ_k` be a basis of `A⊥`. Since `A=(A⊥)⊥`, `x∈A` iff `χ_{γ_i}(x)=1` for every `i`. Therefore

`1_A(x)=∏_{i=1}^k (1+χ_{γ_i}(x))/2 = 2^{−k}∑_{γ∈span{γ_i}}χ_γ(x)`.

The expansion of `φ_A` follows from `E[1_A]=2^{−k}`.

<a id="pdf-20e15a3d3d5e-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.94 -->
**Proposition 3.12.** If `A=H+a` is an affine subspace of codimension `k`, then

`1̂_A(γ)=2^{−k}χ_γ(a)` for `γ∈H⊥`, and `0` otherwise.

Hence `φ̂_A=∑_{γ∈H⊥}χ_γ(a)χ_γ`, `sparsity(1̂_A)=2^k`, `||1̂_A||_∞=2^{−k}`, and `1_A` is `2^{−k}`-granular.

<a id="pdf-20e15a3d3d5e-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.97 -->
**Definition 3.13.** A decision tree over `F₂ⁿ` is a rooted binary tree whose internal nodes query coordinates, edges are labeled `0` and `1`, leaves have real labels, and no coordinate repeats on a root-to-leaf path. The output is the label reached by the computation path.

<a id="pdf-20e15a3d3d5e-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.96 -->
The size `s` of a decision tree is its number of leaves; its depth `k` is the maximum root-to-leaf path length. `DT(f)` and `DTsize(f)` denote least depth and size. The example tree for `Sort3` has size `6` and depth `3`.

<a id="pdf-20e15a3d3d5e-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.96 -->
**Fact 3.15.** If `T` computes `f` and `P` ranges over root-to-leaf paths, then the associated subcubes `C_P` partition `F₂ⁿ`, `f` is constant on each `C_P`, and

`f=∑_P f(P)1_{C_P}`.

<a id="pdf-20e15a3d3d5e-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.99 -->
**Proposition 3.16.** Let `f : F₂ⁿ → ℝ` be computed by a decision tree `T` of size `s` and depth `k`. Then:

- `deg(f) ≤ k`;
- `sparsity(f̂) ≤ s2^k ≤ 4^k`;
- `||f̂||₁ ≤ ||f||∞ · s ≤ ||f||∞ · 2^k`;
- `f̂` is `2^{−k}`-granular assuming `f : F₂ⁿ → ℤ`.

<a id="pdf-20e15a3d3d5e-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.95 -->
**Proposition 3.17.** If `f:{−1,1}ⁿ→{−1,1}` is computed by a decision tree of size `s` and `ε∈(0,1]`, then its spectrum is `ε`-concentrated on degree up to `log(s/ε)`.

<a id="pdf-20e15a3d3d5e-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.99 -->
## 3.3. Restrictions

<a id="pdf-20e15a3d3d5e-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
Let `(J,J̄)` partition `[n]`, let `z∈{−1,1}^{J̄}`, and let `f:{−1,1}ⁿ→ℝ`. The restriction `f|^J_z:{−1,1}^J→ℝ` fixes coordinates in `J̄` to `z`: `f|^J_z(y)=f(y,z)`.

<a id="pdf-20e15a3d3d5e-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.99 -->
For the function `f:{−1,1}⁴→{−1,1}` defined in (3.2), consider the restriction `x₃=1, x₄=−1`. The restricted function is `f'(x₁,x₂)=min₂(x₁,x₂)` with

`f'=−1/2 + (1/2)x₁ +(1/2)x₂ +(1/2)x₁x₂`.

The coefficient on `x₁` is obtained by summing all original monomials containing `x₁` after substituting `x₃=1, x₄=−1`, yielding `1/2`.

<a id="pdf-20e15a3d3d5e-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.96 -->
**Definition 3.20.** For `S⊆J`, define `FS_J f(z)= f̂|^J_z(S)`, the Fourier coefficient on `S` of the restricted function.

<a id="pdf-20e15a3d3d5e-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.96 -->
**Proposition 3.21.**

`FS_J f(z)=∑_{T⊆J̄} f̂(S∪T) z^T`.

Equivalently, the Fourier coefficient of `FS_J f` on `T⊆J̄` is `f̂(S∪T)`.

<a id="pdf-20e15a3d3d5e-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->
Write every Fourier index as the disjoint union `U=S∪T`, with `S⊆J` and `T⊆J̄`, and write `x=(y,z)`. Then

`f(x)=∑_{S⊆J}∑_{T⊆J̄} f̂(S∪T)y^S z^T`.

For fixed `z`, the coefficient of `y^S` is therefore `∑_{T⊆J̄} f̂(S∪T)z^T`.

<a id="pdf-20e15a3d3d5e-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.96 -->
**Corollary 3.22.** If `z∈{−1,1}^{J̄}` is uniform and `S⊆J`, then

`E_z[f̂|^J_z(S)] = f̂(S)`,

and

`E_z[f̂|^J_z(S)^2]=∑_{T⊆J̄} f̂(S∪T)^2`.

<a id="pdf-20e15a3d3d5e-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->
For a subspace `H≤F₂ⁿ`, write `f|_H:H→ℝ` for restriction to `H`. For `z∈F₂ⁿ`, define the translate `f^{+z}(x)=f(x+z)`.

<a id="pdf-20e15a3d3d5e-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.97 -->
**Fact 3.25.** The Fourier coefficients of `f^{+z}` are

`f̂^{+z}(γ)=(-1)^{γ·z}f̂(γ)`,

so `f^{+z}(x)=∑_γ χ_γ(z)f̂(γ)χ_γ(x)`.

<a id="pdf-20e15a3d3d5e-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.94 -->
For `H≤F₂ⁿ` and `z∈F₂ⁿ`, write `f^{+z}|_H` for restriction of `f` to the coset `H+z`, with the representative `z` explicit. The average over the coset is `⟨φ_H,f^{+z}⟩=E_{h∼H}[f(h+z)]`.

<a id="pdf-20e15a3d3d5e-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.97 -->
For `f:F₂ⁿ→ℝ`, `H≤F₂ⁿ`, and `z∈F₂ⁿ`,

`E_{h∼H}[f(h+z)] = ∑_{γ∈H⊥} χ_γ(z) f̂(γ)`.

<a id="pdf-20e15a3d3d5e-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.99 -->
## 3.4. Learning theory

<a id="pdf-20e15a3d3d5e-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.96 -->
In the model of PAC learning under the uniform distribution on `{−1,1}ⁿ`, a concept class `C` is a collection of functions `f:{−1,1}ⁿ→{−1,1}`. A learning algorithm is a randomized algorithm with limited access to an unknown target function `f∈C`. The two access models are random examples `(x,f(x))`, where `x` is uniformly random, and membership queries requesting `f(x)`.

<a id="pdf-20e15a3d3d5e-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.97 -->
For a collection `F⊆2^[n]`, the Fourier spectrum of `f` is `ε`-concentrated on `F` if

`∑_{S∉F} f̂(S)^2≤ε`.

For Boolean `f`, equivalently `Pr_{S∼f̂²}[S∉F]≤ε`.

<a id="pdf-20e15a3d3d5e-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.94 -->
**Theorem 3.29.** Suppose a learner with random-example access can identify a collection `F` on which the target’s spectrum is `ε/2`-concentrated. Then, using `poly(|F|,n,1/ε)` additional time, it outputs with high probability a hypothesis `ε`-close to the target.

<a id="pdf-20e15a3d3d5e-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.97 -->
**Proposition 3.30.** Given random examples from `f:{−1,1}ⁿ→{−1,1}`, a randomized algorithm estimates any fixed `f̂(S)` to additive error `ε`, except with probability `δ`, in time `poly(n,1/ε)log(1/δ)`.

<a id="pdf-20e15a3d3d5e-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.97 -->
`f̂(S)=E_x[f(x)χ_S(x)]`. The algorithm samples the `±1`-valued variable `f(x)χ_S(x)` and uses its empirical mean. Chernoff’s bound shows that `O(log(1/δ)/ε²)` examples suffice.

<a id="pdf-20e15a3d3d5e-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.96 -->
**Proposition 3.31.** If `||f−g||²₂≤ε²/2` and `h(x)=sgn(g(x))`, then `dist(f,h)≤ε`, with `sgn(0)` arbitrary.

<a id="pdf-20e15a3d3d5e-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.98 -->
If `f(x)≠sgn(g(x))`, then `|f(x)−g(x)|²≥1`; hence

`dist(f,h)=Pr_x[f(x)≠h(x)]=E[1_{f(x)≠sgn(g(x))}]≤E[|f(x)−g(x)|²]=||f−g||²₂`.

To prove Theorem 3.29, estimate every `f̂(S)` for `S∈𝓕` to error `ε/(2√|𝓕|)` with failure probability `1/(10|𝓕|)`, and use the union bound. Let `g=∑_{S∈𝓕} f̂(S)χ_S` and `h=sgn(g)`.

<a id="pdf-20e15a3d3d5e-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.94 -->
If every function in `C` is `ε/2`-concentrated up to degree `k≥1`, then `C` can be learned from random examples with error `ε` in time `poly(n^k,1/ε)`, by taking `F={S⊆[n]:|S|≤k}`, whose size is `O(n^k)`.

<a id="pdf-20e15a3d3d5e-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.94 -->
**Corollary 3.32.** The class `{f:{−1,1}ⁿ→{−1,1}: I[f]≤t}` is learnable from random examples with error `ε` in time `n^{O(t/ε)}`.

**Corollary 3.33.** The class of monotone Boolean functions is learnable from random examples with error `ε` in time `n^{O(√n/ε)}`.

<a id="pdf-20e15a3d3d5e-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.99 -->
**Corollary 3.34.** For `δ∈(0,1/2]`, let `𝒞={f:{−1,1}ⁿ→{−1,1} | NS_δ[f]≤ε/6}`. Then `𝒞` is learnable from random examples with error `ε` in time `poly(n^{1/δ},1/ε)`.

**Corollary 3.35.** Let `𝒞={f:{−1,1}ⁿ→{−1,1} | DT_size(f)≤s}`. Then `𝒞` is learnable from random examples with error `ε` in time `n^{O(log(s/ε))}`.

<a id="pdf-20e15a3d3d5e-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.93 -->
**Theorem 3.36.** Let `k≥1` and let `C={f:{−1,1}ⁿ→{−1,1}:deg(f)≤k}`. Then `C` is exactly learnable from random examples in time `n^k poly(n,2^k)`. (For example, `C` contains all depth-`k` decision trees.)

<a id="pdf-20e15a3d3d5e-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.99 -->
## 3.5. Highlight: the Goldreich–Levin Algorithm

<a id="pdf-20e15a3d3d5e-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.97 -->
Given query access to `f:{−1,1}ⁿ→{−1,1}` and input `0<τ≤1`, there is a `poly(n,1/τ)`-time algorithm that, with high probability, outputs a list `L` of subsets of `[n]` such that:

- `|f̂(U)|≥τ ⇒ U∈L`;
- `U∈L ⇒ |f̂(U)|≥τ/2`.

Parseval implies `|L|≤4/τ²`.

<a id="pdf-20e15a3d3d5e-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->
If every `f∈C` has its Fourier spectrum `ε/4`-concentrated on a collection of at most `M` sets, then `C` can be learned using queries with error `ε` in time `poly(M,n,1/ε)`. This is the Kushilevitz–Mansour algorithm.

<a id="pdf-20e15a3d3d5e-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.93 -->
Let `C={f:{−1,1}ⁿ→{−1,1}:||f̂||_1≤s}`. Then `C` is learnable from queries with error `ε` in time `poly(n,s,1/ε)`. This includes functions computable by decision trees of size at most `s`.

<a id="pdf-20e15a3d3d5e-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.97 -->
For `S⊆J⊆[n]`, define the Fourier weight on sets whose restriction to `J` is `S` by

`W^S_J[f]=∑_{T⊆J̄} f̂(S∪T)^2`.

<a id="pdf-20e15a3d3d5e-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.95 -->
Corollary 3.22 gives

`W^S_J[f]=E_{z∼{−1,1}^{J̄}}[f̂|^J_z(S)^2]`.

**Proposition 3.40.** With query access to `f`, an algorithm estimates `W^S_J[f]` to additive error `ε`, except with probability `δ`, in time `poly(n,1/ε)log(1/δ)`. It samples independent `y,y′,z` and estimates the mean of `f(y,z)χ_S(y)f(y′,z)χ_S(y′)`.

<a id="pdf-20e15a3d3d5e-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.96 -->
Initially all `2ⁿ` subsets are in one bucket. Repeatedly split a bucket containing `2^m` sets into two buckets of `2^{m−1}` sets, estimate each bucket’s Fourier weight, and discard a bucket if its estimate is at most `τ²/2`. Stop when all buckets are singletons.

<a id="pdf-20e15a3d3d5e-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.95 -->
Assuming estimates are accurate to within `τ²/4`, every `U` with `|f̂(U)|≥τ` is retained because it contributes at least `τ²`; no `U` with `|f̂(U)|≤τ/2` reaches a singleton bucket because that bucket has weight at most `τ²/4`. Every active bucket has weight at least `τ²/4`, so Parseval gives at most `4/τ²` active buckets. Each bucket splits at most `n` times, so there are at most `4n/τ²` iterations.

<a id="pdf-20e15a3d3d5e-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.96 -->
Buckets are indexed by `0≤k≤n` and `S⊆[k]`:

`B_{k,S}={S∪T:T⊆{k+1,…,n}}`.

The initial bucket is `B_{0,∅}`; splitting `B_{k,S}` produces `B_{k+1,S}` and `B_{k+1,S∪{k+1}}`. The final buckets are `B_{n,S}={S}`, and the weight of `B_{k,S}` is `W^S_{[k]}[f]`. At most `8n/τ²` estimates are needed. Taking `δ=τ²/(80n)` makes all estimates accurate with probability at least `9/10`.

<a id="pdf-20e15a3d3d5e-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.99 -->
## 3.6. Exercises and notes

<a id="pdf-20e15a3d3d5e-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.94 -->
Exercises cover Fourier behavior under invertible linear and affine transformations; the sharp constant in Proposition 3.3; induction proof of Lemma 3.5; norm properties of Fourier `p`-norms; restriction effects on spectral `1`-norm and sparsity; Hausdorff–Young special cases; monotone functions; Proposition 3.12; Parseval for subspaces; affine-subspace indicators; the bound `||f̂||₁≤2^{n/2}`; and fractional sparsity.

<a id="pdf-20e15a3d3d5e-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.94 -->
Exercises include the uncertainty principle; approximate spectral concentration; decision-tree representations; Propositions 3.16 and 3.17; decision lists and threshold functions; sharpness of Theorem 3.4; influence of read-once trees; and generalizations to subcube partitions, parity decision trees, and affine-subspace partitions.

<a id="pdf-20e15a3d3d5e-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.88 -->
Further exercises ask for spectral and learning properties of generalized decision-tree representations; analysis of `Equ₃`; tensor products; restrictions and projections; and marginal and conditional densities of distributions on `F₂ⁿ`.

<a id="pdf-20e15a3d3d5e-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.88 -->
Exercises cover large coefficients from decision-tree leaves; translation of Fourier coefficients; granular functions; exact learning in time `O(2ⁿ)`; improving Proposition 3.31 by randomized thresholding; examples lacking concentration; Theorem 3.36; exact learning of juntas, decision trees, and sparse functions; Theorem 3.38; and amplification of learning success probability.

<a id="pdf-20e15a3d3d5e-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.88 -->
Exercises address reuse of one sample batch in the Low-Degree Algorithm; kernel form of the resulting hypothesis; Goldreich–Levin for real-valued targets; identification of linear functions from random examples; and the Goldreich–Levin pseudorandom-generator construction.

<a id="pdf-20e15a3d3d5e-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.97 -->
Exercise 3.45 analyzes `g(r,s)=(r,f(s),r·s)` for a one-way permutation `f`, showing that an adversary predicting `r·s` would yield a set of `s` with noticeably large correlation and, via the Goldreich–Levin algorithm, an inverter for `f`. The notes discuss Pontryagin duality, spectral sparsity, decision-tree and subcube-partition complexity, the uncertainty principle, Green–Sanders results, and the Nisan–Szegedy theorem.

<a id="pdf-20e15a3d3d5e-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.95 -->
The best known upper bound cited for decision-tree depth in terms of degree is `deg(f)^3` (Midrijānis). The chapter notes the origins of computational learning theory, the Fourier approach of Linial–Mansour–Nisan, noise sensitivity methods, results of Bshouty–Tamon, Goldreich–Levin, Kushilevitz–Mansour, and Gopalan et al.
