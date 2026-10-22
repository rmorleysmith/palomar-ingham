# PalomarIngham — Ingham's theorem, Palomar-ready

**Result.** For `1/2 ≤ θ < 1`: `ζ(s) ≠ 0` for all `Re s > θ` ⟺ `ψ(x) = x + O(x^{θ+δ})` for every
`δ > 0`. Hence RH ⟺ `ψ(x) = x + O(x^{1/2+δ})` ∀δ > 0, and the zero-free half-plane `Re s > 7/8`
(OpenAI 2026, a stated hypothesis here) gives `ψ(x) = x + O(x^{7/8+δ})`.

**Read first:** [`Challenge.lean`](Challenge.lean) (≈50 lines, imports only Mathlib, no new
definitions). Proofs: [`Solution.lean`](Solution.lean) → `PalomarIngham/`.

## Check it

```bash
lake exe cache get
lake build                 # all targets; only Challenge.lean has (deliberate) sorry
lake comparator            # Lean v4.35.0 built-in Comparator (needs bubblewrap)
```

Last run (this machine): `Lean default kernel accepts the solution — Your solution is okay!`

## Layout

| Path | Content |
|---|---|
| `Challenge.lean`, `Solution.lean`, `comparator.json` | the Palomar triple |
| `formalization.yaml` | metadata (fill the `TEMPLATE` person fields before submitting) |
| `PalomarIngham/QuasiRH/` | easy direction (partial summation, Mellin holomorphy, identity theorem), RH ⟺ zero-free right of ½ |
| `PalomarIngham/Ingham/` | hard direction: log-derivative bound (Borel–Carathéodory), contour bounds, assembly |
| `PalomarIngham/Vendor/PNT/` | 13 files of PrimeNumberTheoremAnd @ `127b50e` (Apache-2.0), converted to the module system, blueprint annotations removed |

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (`56a0058…`), matching as Palomar
requires (minimum toolchain `v4.35.0-rc2`). Every `.lean` file is a `module`, the largest is
3511 lines.

## Provenance

Developed in `../Formal` (chapters 1–5) and `../FormalPNT` (chapter 6) against OpenAI's exact
pins (Lean v4.34.1, Mathlib `d13f23b`), then ported here. One fidelity bug was caught while
writing the Challenge: an unannotated `∀ δ > 0` elaborated `δ` as a **natural number** (making
`1/2 + δ` mean `0 + δ`); Comparator's type check exposed it, and the Challenge now says
`∀ δ : ℝ, 0 < δ → …`.

## To submit (requires the human maintainer)

1. Fill the `TEMPLATE` fields in `formalization.yaml`.
2. Push this directory as a public GitHub repository (root = this directory), commit everything
   including `lake-manifest.json`, copy the 40-character SHA.
3. Submit at <https://submit.palomar-registry.org/> and keep the status page link.
