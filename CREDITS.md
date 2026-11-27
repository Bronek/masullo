# Credits

The programme follows the trace-formula approach of Masullo, "The Music Of The Primes", which builds
on work of Connes and Meyer.

## Weil's explicit formula

Weil's explicit formula, the zero count, the lower bound for zeta on `Re s ≥ 2` and the heights at
which `ζ'/ζ` is bounded are in the Lean library `WeilExplicit` (`WeilExplicit.lean` and
`WeilExplicit/`), released under CC0 like the rest of this repository.

An earlier version of this repository imported Anthropic's `Zeta23` package, directory `zeta23` of
<https://github.com/anthropics/formal-math> at commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`,
copyright 2026 Anthropic, PBC, Apache License 2.0. `WeilExplicit` replaces that dependency. It was
written new by OpenAI Codex from a prose account of the argument and a list of target statements,
both prepared by Claude after reading Zeta23; Codex was instructed not to read Zeta23. No Zeta23
code was copied into this repository.

The licence in `LICENSE.md` covers this repository only.

## Spectral realisation

The vanishing part of `Masullo/Spectrum.lean` follows the spectral realisation of zeta zeros on a
quotient by theta functions, due to Alain Connes (1999) and Ralf Meyer (2005), in the weighted
setting of Masullo, as do `Masullo/Theta.lean` and the quotient in `Masullo/Trace.lean`. The seed of
`Masullo/Seed.lean` gives Riemann's integral for ξ. These attributions are from memory; the sources
were not consulted.

## Spectral synthesis

`Masullo/Synthesis/Duality.lean` uses the Carleman transform and belongs to the theory of
mean-periodic functions and spectral synthesis (Carleman; Schwartz), with a Phragmén–Lindelöf bound
(recalled; sources not consulted). The duality argument replaces a ∂̄ argument by OpenAI Codex; the
Lean proof was written by Claude. `Masullo/Synthesis.lean` uses the good heights for zeta of
`WeilExplicit`.

## Trace

`Masullo/Trace.lean` uses the inverse-square zero sum and the explicit formula of `WeilExplicit`.
The trace of scaling on the theta quotient follows Connes (1999) and Meyer (2005).
`Masullo/Trace/Operator.lean` uses standard theory of Hilbert–Schmidt and trace class operators,
Gram–Schmidt triangularisation and dissipative resolvents. The Connes, Meyer and operator theory
attributions are recalled; sources were not consulted. The Lean proofs were written by Claude.

For `Masullo/Tail.lean`, OpenAI Codex proposed the estimate up to a finite height and its proof by
subtracting the trace sum and using quartic decay of the transform. Claude wrote the Lean and its
controls; Codex shortened the proofs and supplied the control on single coefficients.

## Window criterion

The criterion for zeta, with the same prime sum, and its argument by high derivatives and a nearest
pole appear in notes of 2026 by Claude, Codex and Gemini, prepared at Michael Rubinstein's request:
<https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/>. The archive of Alpöge's proof has a
related theorem for character families, `zeroFree_of_rpow_window`. Earlier results of this
kind on power intervals are due to Kaczorowski and Pintz (1986), in the line of Landau's theorem.

`Masullo/Landau.lean` and `Masullo/Window.lean` were planned by Claude after reading parts of
those notes, and the Lean was written by Claude, with a version of the argument that allows real
poles of negative residue. No text or Lean code of these sources was copied. OpenAI Codex reviewed
the plan and the Lean, and supplied the proofs of `abs_windowSum_le` and of the sign-change control.

For `Masullo/Dyadic.lean`, Codex proposed the two-scale difference and the tent weight and computed
its multiplier and the residue signs for both bounds. Claude wrote the Lean; the proof that zeta has
no zeros in `(0, 1)`, several shortenings and the control on windows of length zero are Codex's.

## Sign runs and reciprocal ordinates

For `Masullo/Runs.lean`, OpenAI Codex proposed the fixed-ratio sign-run argument for the dyadic
prime sum and the positive two-point averages that isolate a conjugate pair; related oscillation
arguments are due to Kaczorowski and to Montgomery and Vorhauer. Claude formalised the implication
from sign runs to a rightmost zero and its trace corollary. Codex reviewed the Lean and shortened
several proofs. A Claude Fable subagent proposed replacing sign runs by a one-sided power bound
on the same windows, which has exactly the strength of the trace gap; Claude formalised it.
For `Masullo/Mean.lean`, Codex proposed the passage from a one-sided mean of the second
difference of `ψ` to such a window bound, and Claude formalised it.
For `Masullo/Liouville.lean`, Codex proposed restating the gap through one-sided bounds on the
summatory Liouville function and its short-interval increments; a Claude Fable subagent proposed
proving it with Landau's argument extended to poles of finite order (`Landau.ContinuesMero`);
Claude formalised both.
For `Masullo/BaezDuarte.lean`, Codex proposed the zero-exclusion test through Báez-Duarte's
natural approximant, a Claude Fable subagent reviewed it, and Claude formalised it.
For `Masullo/Modulation.lean` and `WeilExplicit/DensityWeighted.lean`, a Claude Fable subagent
proposed averaging the trace identity over modulations, Codex supplied the unconditional proof
from the existing density estimate, and Claude formalised it.
A Claude Fable subagent proposed its converse `trace_eq_of_integral_small`, Codex reviewed and
sharpened it to every modulation, and Claude formalised it.
A Claude Fable subagent surveyed the tree for shorter statements that subsume longer ones and
proved `Runs.ne_zero_of_dyadic_window`; Claude added it, with
`Landau.ContinuesMero.eq_empty_of_window_ge` and the removal of duplicated lemmas.

For `WeilExplicit/Density*.lean`, Codex supplied the Carlson-type mollified mean-square argument
for the summability of reciprocal ordinates of the zeros to the right of `re s = σ > 1/2`. Claude
wrote the Lean proof; Codex replaced its Gaussian Fourier estimates by Plancherel
(`WeilExplicit/DensityFourier.lean`) and shortened the divisor, shell and integral arguments.
The method of Carlson (1920) is recalled; the source was not consulted.

## Pair of widths

Hassana Labs reviewed Masullo's manuscript (<https://hassana.io/music-of-the-primes/>) and published
Lean code (<https://github.com/leochlon/music-of-the-primes-lean>, Apache License 2.0) that does not
claim the Riemann hypothesis. It shows that for one pair of widths, equality of the strip limits for
its family of tests, under its counting and transform hypotheses, makes every coefficient in the
half-open band between them vanish. `trace_eq_trace_half_iff` in `Masullo/Trace.lean` is the analogue here for
the pair `a`, `1/2`; it was proved from the results of this repository, and no Hassana code was
copied.

## Nonnegative probes

`Masullo/Probe.lean` applies the window form of Landau's theorem to the translated functional of
Weil's explicit formula. OpenAI Codex proposed translating nonnegative tests, the window argument
and a bump adapted to each zero, in a form with constants tending to zero; Claude chose the form with
one constant per test and wrote the Lean. Codex reviewed it. The power-series precedent for the role
of positivity is the Vivanti–Pringsheim theorem.
Codex proposed in review the criterion with one probe, a real tilt of a bump that avoids the
countably many bad exponents, and a Claude Opus subagent formalised it (`windowBound_iff`).
Claude Fable proposed the width form of Bagchi's recurrence criterion (Steuding, *Value-Distribution
of L-Functions*, Theorem 8.3), Codex corrected the counting in review, and a Claude Opus subagent
formalised the sufficient direction (`trace_eq_efFunctional_of_selfRecurrent`).
Claude Fable observed in review that measure `T^(1-δ)` of good shifts suffices, and a Claude Opus
subagent generalised the proof (`trace_eq_efFunctional_of_sparselyRecurrent`).
