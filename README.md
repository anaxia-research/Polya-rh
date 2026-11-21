# Polya-rh

Lean 4 proof of the Pólya–Vinogradov inequality with `log log q`:

> There is an absolute constant `C` such that every primitive Dirichlet character `χ` modulo
> `q ≥ 3` satisfies `|∑_{n ≤ x} χ(n)| ≤ C √q log log q` for all `x`.

The proof follows Montgomery and Vaughan (1977). It uses the zeros of `L`-functions only through
the half-plane `SevenEighths`: no `L(s, ξ)` with `ξ` nonprincipal vanishes for `Re s > 7/8`.

| Lean name | Hypothesis |
|---|---|
| `PolyaRH.polya_vinogradov_of_sevenEighths` | `SevenEighths` |
| `PolyaRH.polya_vinogradov_of_GRH` | `GRH` (zero-free on `Re s > 1/2`) |
| `PolyaRH.polya_vinogradov` | none: `SevenEighths` is OpenAI's formal theorem `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` |
| `PolyaRH.character_sum_range{,_of_GRH,_of_sevenEighths}` | `∑_{n ≤ x} χ(n) ≪ x (log log q / log x + 1 / log q)` |

`GRH` is stated with Mathlib's `DirichletCharacter.LFunction` (`PolyaRH/Hypothesis.lean`), in the
same form as `EveryCharacter` in `anaxia-research/Openproblemsforfieldsmedal1/Closure`.

## Build

```
lake exe cache get
lake build PolyaRH                 # GRH and 7/8 versions, about 30 files
lake env lean AxiomsGRH.lean
lake build                         # adds the unconditional version (OpenAI's 2,924 files)
lake env lean Axioms.lean
```

Lean v4.34.1, Mathlib as pinned in `lake-manifest.json`. `axioms-grh.txt` is the output of
`AxiomsGRH.lean` and `axioms.txt` that of `Axioms.lean`: every theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`.
There is no `sorry`, no `axiom` and no `native_decide`.

## Layout

- `PolyaRH/Hypothesis.lean`: `GRH`, `SevenEighths`, and the class `HalfPlane` that carries the
  half-plane. The only use of the half-plane is `Vinogradov.zeroFree`.
- `PolyaRH/Main.lean`, `PolyaRH/Unconditional.lean`: the final theorems.
- `Vinogradov/`: the proof (Pólya's expansion, prime sums from the half-plane, major arcs,
  the weak Montgomery–Vaughan bound, smooth numbers).
- `OAI/`, `PrimeNumberTheoremAnd/`, `RellichKondrachov/`: third-party code, see `NOTICE`.

The code in `OAI/`, `PrimeNumberTheoremAnd/` and `RellichKondrachov/`, and the four files of
`Vinogradov/` that adapt OpenAI code (`MRT`, `Riesz`, `ContourShift`, `EulerLog`), are under the
Apache License 2.0 (`LICENSE-APACHE`); the rest is under the MIT License (`LICENSE`).
