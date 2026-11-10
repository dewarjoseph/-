# Erratum to FILE F docstring (2026-11-09)

This is a public landing copy of a wording erratum. The pinned source erratum (sha256 `a3da34b3c53f5e3dcea0a019300c88f95822b64b69ce36c53869a06f62a9aa0a`) is not rewritten. FILE F itself is unedited (source sha256 `365b8809a4d60132250f1c6b6c0ed53f1b0470a8654496064c4247e4e60c9cf1`).

## The sentence

FILE F docstring, lines 31–33:

> Specialised cubic constants `c0/N³` at the one-pair representatives (LemmaDLowerBound220/330Sharper/L1SevenCubic) remain the sharper statements there.

The same claim also appeared as: "Specialised one-pair c0/N³ bounds stay sharper where they exist."

## Correction [F] on that wording; theorems unchanged

Those specialised constants are all strictly less than 1:

- (2,2,0) and (5,2,0): 1/30
- (3,3,0) and (4,3,0): 1/34
- (1,1,0) and (6,1,0): 1/38

FILE F proves `‖F‖ ≥ 1/N³` at every integer `q` with `F ≠ 0`, including those one-pair representatives and their orbits (they are already known non-vanishing). Because `1 > 1/30 > 1/34 > 1/38`, the constant-1 bound is strictly stronger at the same exponent. Quote FILE F as the current lower bound there. The specialised `c0/N³` theorems remain correct [P, Lean] statements; they are just weaker. Infima and sharpness stay [X].

The earlier impression that the cubic route was sharper came from comparing it with the old uniform `1/N⁶` floor, which FILE F has itself replaced.

Not peer reviewed. ETH false stays [X].
