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

## Pair of widths

Hassana Labs reviewed Masullo's manuscript (<https://hassana.io/music-of-the-primes/>) and published
Lean code (<https://github.com/leochlon/music-of-the-primes-lean>, Apache License 2.0) that does not
claim the Riemann hypothesis. It shows that equality of strip limits at one pair of widths excludes
the zeros between them. `trace_eq_trace_half_iff` in `Masullo/Trace.lean` is the analogue here for
the pair `a`, `1/2`; it was proved from the results of this repository, and no Hassana code was
copied.
