# Credits

The programme follows the trace-formula approach of Masullo, "The Music Of The Primes", which builds
on work of Connes and Meyer.

Weil's explicit formula comes from the `Zeta23` package, directory `zeta23` of
<https://github.com/anthropics/formal-math> at commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`,
copyright 2026 Anthropic, PBC, Apache License 2.0. Part of that package derives from
PrimeNumberTheoremAnd (<https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>) and Mathlib, both
Apache License 2.0. Lake fetches it as a dependency; this repository contains none of its code.

The licence in `LICENSE.md` covers this repository only.

## Spectral realisation

`Masullo/Spectrum.lean` follows the spectral realisation of zeta zeros on a quotient by theta
functions, due to Alain Connes (1999) and Ralf Meyer (2005), in the weighted setting of Masullo.
The attribution is from memory; the sources were not consulted.

`Masullo/Synthesis.lean` uses the Carleman transform (recalled; sources not consulted) and Zeta23's
good heights for zeta. The duality argument replaces a ∂̄ argument by OpenAI Codex; the Lean proof
was written by Claude.
