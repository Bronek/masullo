# Masullo in Lean

A Lean 4 formalisation of some analysis around the trace-formula approach to the Riemann hypothesis
in Masullo, "The Music Of The Primes", which builds on work of Connes and Meyer.

**This is not a proof of the Riemann hypothesis**, and nothing here restricts the location of any
zero of zeta. The project set out to build such a proof along these lines. What it has is the
spectral side, in the simplest case (the Riemann zeta function, no logarithmic factor in the
weight), a reduction of the trace identity above width 5/12 to printed results that enter as
hypotheses, and a precise statement of what is missing. It is independent of Masullo and is not
endorsed by the author of that work.

## What is proved

`W a` is the space of functions on the line, in the logarithmic variable, that are square integrable
with weight `2 cosh(2au)`, and `V a` is the closed span in it of theta functions built from even
Schwartz functions `f` with `f(0) = 0` and `∫ f = 0`. Test functions are smooth with compact support
in `(1, ∞)`. Zeros are those of zeta in the open critical strip, counted with multiplicity, and their
distance is measured from the critical line. For every `a > 0`:

| Result | Declaration |
|---|---|
| `V a` is the space cut out by the zeros at distance less than `a` from the critical line | `V_eq_J` in `Masullo/Synthesis.lean` |
| Scaling by a test function is trace class on `W a / V a`, with trace the sum over those zeros | `exists_hasTrace_induced` in `Masullo/Trace.lean` |
| That trace is Weil's functional for every test function iff no zero has distance at least `a` | `trace_eq_efFunctional_iff` in `Masullo/Trace.lean` |

At `a ≥ 1/2` the trace is Weil's functional unconditionally (`hasTrace_of_half_le`).
At any width, the difference between Weil's functional at the translate of `φ` by `t` and the trace
is the sum over the finitely many zeros in the strip at distance at least `a` and height at most
`T`, up to an error of at most `C e^(t/2) / (1 + T²)`, where `t, T ≥ 0` and `C` depends on `φ` only
(`exists_bound` in `Masullo/Tail.lean`).

On average over modulations the trace identity holds at every positive width with a power saving,
unconditionally. Let `φ^τ(x) = x^(iτ) φ(x)` and `κ = min(a/2, 1/8)²/3`. The mean over
`τ ∈ [-T, T]` of the absolute difference between Weil's functional at `φ^τ` and the trace at width
`a` is at most `C T^(-κ) log²(2T)` for `T ≥ 2`, with `C` depending on `a` and `φ`
(`mean_modulate_le` in `Masullo/Modulation.lean`). It is a consequence of the zero-density estimate
and excludes no zero: on paper, a single zero off the critical line contributes `O(1/T)` to the
mean. The exponent cannot reach 1 for a test with a nonzero discrepancy: if the unnormalised
integral over `[-T, T]` falls below every `ε > 0` at arbitrarily large `T`, the identity holds at
every modulation of `φ` (`trace_eq_of_integral_small`), since the integrand is continuous.

One sufficient condition is arithmetic. Let `G(x) = ∑_{n ≤ x} Λ(n)(x/n - 1) - x log x + (1 + γ)x`,
and fix real numbers `θ ≥ 0`, `δ > 0` and `C`. Suppose there are arbitrarily large `Y` for which
`G(x) ≤ C x^θ` for every real `x` in `[Y, Y^(1+δ)]`. Then zeta has no zero with real part greater
than `θ` (`riemannZeta_ne_zero_of_window` in `Masullo/Window.lean`), so the trace identity holds
for every test function at every positive width `a > θ - 1/2` (`trace_eq_efFunctional_of_ne_zero`).
The lower bound `G(x) ≥ -C x^θ` on such windows gives the same conclusion
(`riemannZeta_ne_zero_of_le_window`), and so does either bound with the side chosen for each window
(`riemannZeta_ne_zero_of_signed_windowSum`). No such bound with `θ < 1` is proved here.

A variant needs no main term. Let `R(y) = max(1/y - 1, 0)`, `w(y) = R(y) - 3R(2y) + 2R(4y)`, which
is nonnegative, `P(X) = ∑_{n ≤ X} Λ(n) w(n/X)` and `D(X) = P(2X) - 2P(X)`. If `D(x) ≤ C x^θ` on such
windows, or if `D(x) ≥ -C x^θ` on them, the same conclusions hold
(`riemannZeta_ne_zero_of_dyadicDiff_le` and `riemannZeta_ne_zero_of_le_dyadicDiff` in
`Masullo/Dyadic.lean`). The side may also change with `Y`: it suffices that one of the two bounds
holds on each such window (`riemannZeta_ne_zero_of_signed_window`), since one side then occurs on
arbitrarily late windows. Both bounds hold at `θ = 1`; neither is proved for any `θ < 1`.

Fixed-ratio windows also suffice, at the cost of the exact exponent. If there are `R > 1`,
`θ < 1` and arbitrarily large `Y` such that `D(x) ≥ -C x^θ` on all of `[Y, RY]`, or
`D(x) ≤ C x^θ` on all of it, then some zero has maximal real part or every zero has real part at
most `max(θ, 1/2)` (`exists_rightmost_of_bound` in `Masullo/Runs.lean`). Either way the trace
identity holds for every test function at some positive width below `1/2`
(`trace_width_of_bound`). Conversely, on paper, such a width gives such a bound by the explicit
formula, so this condition has exactly the strength of the trace gap. Sign runs are the case
`C = 0`; on paper they are equivalent to the maximal real part being attained, which is stronger.
The analytic input, that the zeros right of each line `re s = σ > 1/2` have summable reciprocal
ordinates, is proved in `WeilExplicit/Density.lean`. The bound holds at `θ = 1`
(`Controls.bound_at_exponent_one`); neither it for any `θ < 1` nor such runs is proved here.
A mean over `[Y, 2Y]` of one sign of `Q(x) = ψ(2x) - 5ψ(x) + 8ψ(x/2) - 4ψ(x/4)`, with `ψ`
Chebyshev's function, also suffices: a bound `C Y^θ` with `θ < 1` for arbitrarily large `Y`
gives the bound above on windows of ratio `√2` (`trace_width_of_mean` in `Masullo/Mean.lean`).
The primes can be removed altogether. Let `L(x) = ∑_{n ≤ x} λ(n)` with `λ(n) = (-1)^Ω(n)` the
Liouville function. For `θ ≥ 1/2`, a one-sided bound `L(x) ≤ C x^θ`, or `L(x) ≥ -C x^θ`, on
`[Y, Y^(1+δ)]` for arbitrarily large `Y` rules out zeros with real part greater than `θ`
(`riemannZeta_ne_zero_of_windowBound` in `Masullo/Liouville.lean`). Its exponent is exact: on
paper the Riemann hypothesis gives the bound for every `θ > 1/2`. Such zeros are also ruled out
by a bound `C x^θ` on the integral from `Y` to each `x` in the window of the positive part of one
sign of the increments `(L(t+h) - L(t))/h`, with `h ≤ Y^θ` and the sign fixed per window
(`riemannZeta_ne_zero_of_meanBound`). Its exponent is not faithful: the bound is expected only
for `θ` above about `2/3`, so it is a quasi-Riemann-hypothesis criterion. Both hold at `θ = 1`.
The same window argument applies to any `b` with `|b(n)| ≤ 1` whose Dirichlet series is `K/ζ`,
with `K` holomorphic on `re s > θ` and nonzero at the zeros of zeta there
(`riemannZeta_ne_zero_of_windowBound` in `Masullo/DirichletWindow.lean`), a case of Kaczorowski
and Pintz (1986). The Liouville criterion is the instance `K(s) = ζ(2s)`; the Möbius case `K = 1`
gives the same conclusion from a one-sided window bound on the Mertens function
`M(x) = ∑_{n ≤ x} μ(n)` for every `θ ≥ 0` (`riemannZeta_ne_zero_of_mertensWindow`). It has the
strength of the same zero-free strip. Sampling at perfect powers suffices: for `θ ≥ 1 - 1/m`, the
bound at the `m`-th powers in each window gives it at every point of the window with a larger
constant (`PowerWindowBound.windowBound`, `riemannZeta_ne_zero_of_mertensPowerWindow`); for the
Mertens function at the squares with `θ = 1/2` the conclusion is the Riemann hypothesis. For the
Jordan totient of order `-τ`, `b = μ * n^(-τ)` with `0 ≤ τ ≤ 1` and `K(s) = ζ(s + τ)`, a sign alone
suffices: one sign of `∑_{n ≤ x} b(n)` on late windows rules out zeros with real part greater
than `1 - τ` (`riemannZeta_ne_zero_of_jordanSign` in `Masullo/Jordan.lean`). On paper, eventual
negativity for some `0 < τ < 1` is equivalent to a zero-free strip `re s > 1 - η`. Chebyshev's
function fits the same argument: a window bound on `ψ(x) - x` with `θ ≥ 0` rules out zeros with
real part greater than `θ` (`riemannZeta_ne_zero_of_psiWindow` in `Masullo/ChebyshevWindow.lean`).
Möbius sums give another criterion, through Báez-Duarte's natural approximant. With `μ` the
Möbius function, `g_N = ∑_{k ≤ N} μ(k)/k` and
`E_N(x) = 1 + ∑_{k ≤ N} μ(k){1/(kx)} - N g_N {1/(Nx)}` for `0 < x ≤ 1`, `E_N` vanishes on
`(1/N, 1]` and its Mellin transform at each zero `ρ` with `re ρ > 0` is `1/ρ` for every `N ≥ 1`.
So for `σ > 0`, a bound `∫_0^1 |E_N(x)| x^(σ-1) dx ≤ C` for arbitrarily large `N` rules out zeros
with real part greater than `σ` (`riemannZeta_ne_zero_of_mellinBound` in `Masullo/BaezDuarte.lean`),
hence the trace identity at every positive width `a > σ - 1/2`. The bound holds at `σ = 1`
(`Controls.mellinBound_one`, constant 3); it is not proved here for any `σ < 1`, and no converse
is formalised.

Recurrence is another sufficient condition. Suppose that for every closed disc `K` in
`θ < re s < 1`, every `ε > 0` and every `δ > 0`, the shifts `τ ∈ [0, T]` with
`‖ζ(s + iτ) - ζ(s)‖ < ε` on all of `K` have measure at least `T^(1-δ)` for arbitrarily large `T`.
For `θ ≥ 1/2` this rules out zeros with real part greater than `θ`, hence the trace identity at
every width `a > θ - 1/2` (`trace_eq_efFunctional_of_sparselyRecurrent` in
`Masullo/Recurrence.lean`). Positive upper density, measure at least `cT` for some `c > 0`, is a
special case (`trace_eq_efFunctional_of_selfRecurrent`); its converse is Bagchi's theorem in
Steuding's width form and is not formalised. Neither condition is proved for any `θ < 1`.

A further condition is equivalent rather than sufficient. For a test function `φ` let `L_φ(t)` be
Weil's functional at the translate of `φ` by `t` in the logarithmic variable. Fix `a ≥ 0` and
`δ > 0`. Consider the condition that every nonnegative `φ` has a constant `C` such that for
arbitrarily large `U`, `L_φ(t) ≤ C e^(at)` for all `t ≥ 0` in `[U, (1+δ)U]`. It holds iff the
trace identity holds for every test function at every width `a' > a`
(`trace_eq_efFunctional_iff_probeBound` in `Masullo/Probe.lean`), and for `a = 0` iff the Riemann
hypothesis holds. At `a = 1/2` it holds unconditionally; it is not proved for any smaller `a`. One
probe suffices: some nonnegative `φ` has transform nonzero at `ρ - 1/2` for every zero `ρ` in the
strip (`TestFunction.exists_nonneg_forall_hat_ne_zero`), and for any such `φ` its bound alone is
equivalent to there being no zeros at distance more than `a` from the critical line
(`windowBound_iff`, `exists_windowBound_zero_iff_riemannHypothesis`).

The second library, `WeilExplicit`, proves Weil's explicit formula for twice continuously
differentiable test functions of compact support (`explicit_formula`), and on the way a zero count,
the inverse-square sum over zeros and heights at which `ζ'/ζ` is `O(log²)` (`good_heights`). It does
not depend on `Masullo` and can be used separately.

## Above width 5/12, conditionally

The smoothed form of Landau's criterion applies to `b = μ ∗ χ₃μ`, whose Dirichlet series is the
inverse of the Dedekind zeta function of `ℚ(√-3)`: a bound `O(D^β)` on its smoothed sums gives the
trace identity at every width `a > β - 1/2` (`hasTrace_of_smoothedBound` in
`Masullo/Smoothed.lean`). Estimate (A) of Proposition 3.1 of OpenAI, *The Quasi-Riemann
Hypothesis* (5 October 2026), a mean square over the prime ideals of the Eisenstein integers,
gives that bound for every `β > 11/12` (`Masullo/QRH/StageB.lean`, with the ideal Möbius function
in `Masullo/QRH/IdealMoebius.lean`), hence the trace identity at every width `a > 5/12`
(`hasTrace_of_meanSquareA`). Estimate (A) is derived in turn from the seven fields of
`PrintedInputs` (`meanSquareA_of_printedInputs` and `hasTrace_of_printedInputs` in
`Masullo/QRH/MeanSquare/Assembly.lean`):

- `largeSieve`: the quadratic large sieve of Goldmakher and Louvel (2013), Theorem 1.1;
- `theta`: Patterson's cubic theta series (1977), Theorem 8.1;
- `cubicReciprocity`: cubic reciprocity with its supplementary laws, Dunn and Radziwiłł (2024),
  (1.4)–(1.5);
- `cubicGaussCube`: the cube of the cubic Gauss sum, Dunn and Radziwiłł (2024), (1.7)–(1.8);
- `quadraticGauss`: the reciprocity for quadratic Gauss sums of Deloup and Turaev (2007), Theorem 1;
- `besselMellin`: the Mellin transform of the modified Bessel function, DLMF 10.43.19;
- `gammaVertical`: the vertical bound for the gamma function, DLMF 5.11.9.

The result is conditional on these inputs, and none of them is proved here. The Goldmakher–Louvel
input is stated only for the Eisenstein family with `c = (72)`: their Theorem 1.1 prints a
constant uniform over each family of their Definition 1, and that form fails for general such
families (see the docstring of `PrintedInputs`). Sources and contributions are in
[CREDITS.md](CREDITS.md#mean-square-above-512).

## What is missing

An unconditional argument that the trace at some width `a < 1/2` is Weil's functional. By the third
result this is equivalent to excluding the zeros at distance at least `a`, so it cannot come from
rearranging what is here. The operator theory used accepts any exponents in the strip and therefore
cannot supply it; an arithmetic input is needed. Above width 5/12 that input is reduced to the
printed results listed above. No zero-free half-plane `re s > θ` with `θ < 1` is proved
unconditionally, and the widths `0 < a ≤ 5/12` remain open even conditionally.

## Status

- All results are proved without `sorry` or added axioms; the two libraries depend on `propext`,
  `Classical.choice` and `Quot.sound` only. The printed inputs above are hypotheses of the
  theorems that use them, not axioms.
- The build uses a release candidate, Lean v4.37.0-rc1, sets `allowNonModules = true` in
  `lakefile.toml`, and disables `backward.isDefEq.respectTransparency` for three declarations
  (`Masullo/QRH/IdealMoebius.lean:214` and `:302`,
  `Masullo/QRH/MeanSquare/ReflectionDecay.lean:293`).
- The Lean code was written by AI models (Claude and Codex) under human direction. Models also
  reviewed the source at several stages; not every later change was reviewed again. No human expert
  has reviewed it, and no independent kernel checker has been run.
- Attributions to the literature are mostly from memory. See [CREDITS.md](CREDITS.md).
- No claim of novelty is made.

Corrections, above all from readers who know the work of Connes and Meyer, are welcome.

## Building

Install [elan](https://github.com/leanprover/elan), then run in this directory:

```sh
lake exe cache get
lake build
```

The only direct dependency is Mathlib, pinned in `lake-manifest.json`. The first command downloads
its compiled files.

## Licence

CC0 1.0; see [LICENSE.md](LICENSE.md).
