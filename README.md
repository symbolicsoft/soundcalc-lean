# soundcalc-lean

A Lean 4 port of [soundcalc](https://github.com/ethereum/soundcalc), following a pedagogical roadmap.

The calculator is a definition; the report is a theorem; the what-if is a quantified theorem.

Current state: milestone M0 seed — `secBits` and one kernel-checked cell of
`reports/sp1.md` (SP1 core query phase, 100 bits).

## Build

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans (do this before lake build)
lake build
```

Pinned to Lean `v4.30.0` / Mathlib `v4.30.0`.
