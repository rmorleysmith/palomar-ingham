# PalomarIngham — Ingham's theorem, Palomar-ready

**Result.** For `1/2 ≤ θ < 1`: `ζ(s) ≠ 0` for all `Re s > θ` ⟺ `ψ(x) = x + O(x^{θ+δ})` for every
`δ > 0`. Hence RH ⟺ `ψ(x) = x + O(x^{1/2+δ})` ∀δ > 0, and the zero-free half-plane `Re s > 7/8`
(OpenAI 2026, a stated hypothesis here) gives `ψ(x) = x + O(x^{7/8+δ})`.

**Second entry (same repository):** primes in progressions — if `ζ` and all `L(s,χ)` mod `q`
are zero-free right of `θ`, then `ψ(x; q, a) = x/φ(q) + O(x^{θ+δ})`; with OpenAI's Dirichlet
theorem as hypothesis, `O(x^{7/8+δ})`. Files: [`ChallengeAP.lean`](ChallengeAP.lean),
[`SolutionAP.lean`](SolutionAP.lean), [`comparatorAP.json`](comparatorAP.json),
[`formalization-ap.yaml`](formalization-ap.yaml) (submit with the non-default Comparator-config
and metadata paths).

**Read first:** [`Challenge.lean`](Challenge.lean) (≈50 lines, imports only Mathlib, no new
definitions). Proofs: [`Solution.lean`](Solution.lean) → `PalomarIngham/`.

## How AI was used

The ideas in this work are Richard Morley-Smith's: the questions, the links between areas of
mathematics, and the choices of what to pursue. AI was used as a tool, in two phases.

- **May–June 2026, the original exploration.** The exploration was carried out in conversation
  with AI coding assistants, chiefly Anthropic's Claude through Claude Code (the design document
  also quotes Google's Gemini). The assistants wrote most of the code, Lean files and documents
  from the author's ideas and direction, quickly and without later editing. Those files are kept
  unchanged in [hsln-archive](https://github.com/rmorleysmith/hsln-archive).
- **October 2026 onwards.** Claude, through Claude Code, helps the author formalise the ideas in
  Lean 4, audit and tidy the earlier files, and write out the working: the steps between an
  intuition and a precise statement.

Checking the results does not rely on trusting the AI. Every Lean theorem is verified by the
Lean kernel against Mathlib, and `#print axioms` shows only Lean's three standard axioms. Every
script asserts the numbers it reports and can be rerun. Every grade in the audit cites the
evidence it rests on.

## Check it

```bash
lake exe cache get
lake build                 # all targets; only Challenge.lean has (deliberate) sorry
lake comparator            # Lean v4.35.0 built-in Comparator (needs bubblewrap)
lake comparator --config=comparatorAP.json
```

Last run (this machine), both configs: `Lean default kernel accepts the solution — Your solution is okay!`

## Layout

| Path | Content |
|---|---|
| `Challenge.lean`, `Solution.lean`, `comparator.json` | the Palomar triple |
| `formalization.yaml` | metadata Palomar requires (authors, sources, AI use, scope) |
| `PalomarIngham/QuasiRH/` | easy direction (partial summation, Mellin holomorphy, identity theorem), RH ⟺ zero-free right of ½ |
| `PalomarIngham/Ingham/` | hard direction: log-derivative bound (Borel–Carathéodory), contour bounds, assembly |
| `PalomarIngham/Dirichlet/` | the same for `L(s,χ)`, `χ ≠ 1`: continuation to `Re s > 0` with growth bound, log-derivative bound, twisted smoothing and contour shift, assembly; orthogonality → progressions |
| `PalomarIngham/Vendor/PNT/` | 13 files of PrimeNumberTheoremAnd @ `127b50e` (Apache-2.0), converted to the module system, blueprint annotations removed |

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (`56a0058…`), matching as Palomar
requires (minimum toolchain `v4.35.0-rc2`). Every `.lean` file is a `module`, the largest is
3511 lines.

## Provenance

Developed in `../Formal` (chapters 1–5) and `../FormalPNT` (chapter 6) against OpenAI's exact
pins (Lean v4.34.1, Mathlib `d13f23b`), then ported here. One fidelity bug was caught while
writing the Challenge (and again in the Dirichlet `Main`): an unannotated `∀ δ > 0` elaborated `δ` as a **natural number** (making
`1/2 + δ` mean `0 + δ`); Comparator's type check exposed it, and the Challenge now says
`∀ δ : ℝ, 0 < δ → …`.

## To submit (requires the human maintainer)

The repository is public and both metadata files are complete. For each entry:

1. Copy the full 40-character SHA of the commit to submit (`git rev-parse HEAD`).
2. Open <https://submit.palomar-registry.org/>, sign in with GitHub, and enter the repository and
   SHA. For the second entry, give `comparatorAP.json` and `formalization-ap.yaml` as the
   non-default paths.
3. Keep the status page link; it is the only way back to the submission.
