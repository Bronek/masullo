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
