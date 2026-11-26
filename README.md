# Masullo in Lean

A Lean 4 formalisation of some analysis around the trace-formula approach to the Riemann hypothesis
in Masullo, "The Music Of The Primes", which builds on work of Connes and Meyer.

**This is not a proof of the Riemann hypothesis**, and nothing here restricts the location of any
zero of zeta. The project set out to build such a proof along these lines. What it has is the
spectral side, in the simplest case (the Riemann zeta function, no logarithmic factor in the
weight), and a precise statement of what is missing. It is independent of Masullo and is not endorsed by the
author of that work.

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

At `a = 1/2` the trace is Weil's functional unconditionally (`hasTrace_induced_half`).
At any width, the difference between Weil's functional at the translate of `φ` by `t` and the trace
is the sum over the finitely many zeros in the strip at distance at least `a` and height at most
`T`, up to an error of at most `C e^(t/2) / (1 + T²)`, where `t, T ≥ 0` and `C` depends on `φ` only
(`exists_bound` in `Masullo/Tail.lean`).

One sufficient condition is arithmetic. Let `G(x) = ∑_{n ≤ x} Λ(n)(x/n - 1) - x log x + (1 + γ)x`,
and fix real numbers `θ > 0`, `δ > 0` and `C`. Suppose there are arbitrarily large `Y > 1` for which
`G(x) ≤ C x^θ` for every real `x` in `[Y, Y^(1+δ)]`. Then zeta has no zero with real part greater
than `θ` (`riemannZeta_ne_zero_of_window` in `Masullo/Window.lean`), and the trace identity holds
for every test function at every positive width `a > θ - 1/2` (`trace_eq_efFunctional_of_window`).
No such bound with `θ < 1` is proved here.

A variant needs no main term. Let `R(y) = max(1/y - 1, 0)`, `w(y) = R(y) - 3R(2y) + 2R(4y)`, which
is nonnegative, `P(X) = ∑_{n ≤ X} Λ(n) w(n/X)` and `D(X) = P(2X) - 2P(X)`. If `D(x) ≤ C x^θ` on such
windows, or if `D(x) ≥ -C x^θ` on them, the same conclusions hold
(`trace_eq_efFunctional_of_dyadicDiff_le` and `trace_eq_efFunctional_of_le_dyadicDiff` in
`Masullo/Dyadic.lean`). Both bounds hold at `θ = 1`; neither is proved for any `θ < 1`.

A sign condition needs no exponent. If there are `R > 1` and arbitrarily large `Y` such that `D`
keeps one sign on all of `[Y, RY]`, the trace identity holds for every test function at some
positive width below `1/2` (`trace_width_of_runs` in `Masullo/Runs.lean`). Its analytic input,
that the zeros right of each line `re s = σ > 1/2` have summable reciprocal ordinates, is proved in
`WeilExplicit/Density.lean`. Such runs are not proved here.

A further condition is equivalent rather than sufficient. For a test function `φ` let `L_φ(t)` be
Weil's functional at the translate of `φ` by `t` in the logarithmic variable. Fix `a ≥ 0` and
`δ > 0`. Consider the condition that every nonnegative `φ` has a constant `C` such that for
arbitrarily large `U`, `L_φ(t) ≤ C e^(at)` for all `t ≥ 0` in `[U, (1+δ)U]`. It holds iff the
trace identity holds for every test function at every width `a' > a` (`trace_eq_efFunctional_iff_probeBound` in
`Masullo/Probe.lean`), and for `a = 0` iff the Riemann hypothesis holds. At `a = 1/2` it holds
unconditionally; it is not proved for any smaller `a`.

The second library, `WeilExplicit`, proves Weil's explicit formula for twice continuously
differentiable test functions of compact support (`explicit_formula`), and on the way a zero count,
the inverse-square sum over zeros and heights at which `ζ'/ζ` is `O(log²)` (`good_heights`). It does
not depend on `Masullo` and can be used separately.

## What is missing

An argument that the trace at some width `a < 1/2` is Weil's functional. By the third result this is
equivalent to excluding the zeros at distance at least `a`, so it cannot come from rearranging what
is here. The operator theory used accepts any exponents in the strip and therefore cannot supply it;
an arithmetic input is needed, and none was found.

## Status

- All results are proved without `sorry` or added axioms; the two libraries depend on `propext`,
  `Classical.choice` and `Quot.sound` only.
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
