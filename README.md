# Two-dimensional Euler nonuniqueness with finite Lp vorticity

**Authors: Tao Tao and Haiqi Zhang**

[![Lean verification](https://github.com/geogleswift-glitch/-euler2d-finite-lp-nonuniqueness-palomar/actions/workflows/lean.yml/badge.svg)](https://github.com/geogleswift-glitch/-euler2d-finite-lp-nonuniqueness-palomar/actions/workflows/lean.yml)
[![Palomar checks](https://github.com/geogleswift-glitch/-euler2d-finite-lp-nonuniqueness-palomar/actions/workflows/palomar.yml/badge.svg)](https://github.com/geogleswift-glitch/-euler2d-finite-lp-nonuniqueness-palomar/actions/workflows/palomar.yml)
[![Palomar registered](https://img.shields.io/badge/Palomar-registered-blue)](https://palomar-registry.org/entry?id=PALOMAR-2026-10-28-000008&version=1)

This repository develops a Lean proof of nonuniqueness for the unforced,
incompressible two-dimensional Euler equations on
`T² = R² / (2π Z)²`, with vorticity bounded in time in any prescribed finite
spatial `Lp` class. The selected declaration is
[`PalomarEuler.main_result`](Solution.lean).

The development has passed the full Lean 4.35.0-rc4 build, a clean
project rebuild, complete statement and axiom audits, and the official
sandboxed Comparator. Lean, NanoDa, and con-ron independently accept the
selected theorem and its exported proof dependencies. The theorem uses
only `propext`, `Quot.sound`, and `Classical.choice`.

Registered in Palomar on **28 October 2026** as
**[PALOMAR-2026-10-28-000008, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-28-000008&version=1)**.
The registration pins the
[verified source snapshot](https://github.com/geogleswift-glitch/-euler2d-finite-lp-nonuniqueness-palomar/tree/ad7deb36ea565f34bdb784e9153073c5a220d46a),
commit `ad7deb36ea565f34bdb784e9153073c5a220d46a`.
Later documentation updates on `main` do not change that registered snapshot.

Palomar's [verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/40527737182)
and [machine-readable record](https://data.palomar-registry.org/entries/PALOMAR-2026-10-28-000008-v1.json)
are public. The record reports an automated editorial outcome of `neutral`,
with no recorded warnings. Registration is not independent human peer review
or a certificate of novelty or priority.

## Mathematical statement

For every `T > 0` and every real `1 ≤ p < ∞`, there exist a mean-zero,
divergence-free datum `u₀ ∈ L²(T²; R²) ∩ W¹ᵖ(T²; R²)` and two paths
`u₁, u₂ ∈ C([0,T]; L²(T²; R²))` such that:

- Both paths solve the unforced Euler equations in the distributional,
  divergence-free test-field formulation and start from the same `u₀`.
- There are strongly measurable vorticity paths
  `ωᵢ : R → Lp(T²)` in `L∞([0,T]; Lp(T²))`, with
  `ωᵢ(t) = curl uᵢ(t)` distributionally at every `t ∈ [0,T]`.
  The development also proves uniform pointwise-in-time curl bounds.
- Their space-time squared distance is strictly positive:
  `∫₀ᵀ ‖u₁(t) − u₂(t)‖²₂ dt > 0`.

The only numerical hypotheses of the selected theorem are `T > 0` and
`1 ≤ p`, with `p` a real number and hence finite. The initial datum is
allowed to depend on `T` and `p`. There is no supplied existence,
compactness, transport, spectral-instability, or measurability premise.

Spatial integration uses ordinary Lebesgue measure on `[0,2π)²`.
Smooth spatially periodic test functions encode the torus. The weak equation
includes the initial term, and the time paths are continuous in the actual
spatial `L²` space. The vorticity statement uses Mathlib's literal Bochner
`MemLp` predicate, in addition to the every-time distributional curl bounds.

## Relation to Problem 6 and scope

The theorem answers the **two-dimensional finite-Lp vorticity question** in
Problem 6 of Tristan Buckmaster and Vlad Vicol,
[*Convex integration and phenomenologies in turbulence*, Surveys in
Mathematical Sciences 6 (2019), 173–263](https://ems.press/journals/emss/articles/16808)
([arXiv:1901.09023](https://arxiv.org/abs/1901.09023)). The separate,
more general comparison of Onsager and uniqueness regularity thresholds
also mentioned in Problem 6 is outside the selected theorem.

The mathematical context distinguishes nonuniqueness for a restricted
spatial exponent from the assertion for every prescribed finite exponent.
For example, Bruè, Colombo, and Kumar's
[*Flexibility of Two-Dimensional Euler Flows with Integrable
Vorticity*](https://arxiv.org/abs/2408.07934) establishes unforced
nonuniqueness for some exponent greater than one. Mengual's
[*Non-uniqueness of Admissible Solutions for the 2D Euler Equation with
Lp Vortex Data*](https://doi.org/10.1007/s00220-024-05065-9) concerns
arbitrary finite-exponent **initial** vorticity; its solution conclusion
does not retain that vorticity class at positive times. These works are
background references, rather than proofs imported by this development.

A recent [Hexagon preprint, 2610.00314v1](https://hexagonmath.org/2610.00314v1),
deposited on 17 October 2026, also claims nonuniqueness at arbitrary finite
exponents greater than two, with the stronger vanishing-viscosity property
on the plane. Its deposit explicitly describes an AI-generated manuscript
whose mathematics has not yet been understood by the contributors. That
claim is background context, not a result checked or imported here. The
selected theorem of this repository concerns weak solutions on the torus
and does not assert that they are vanishing-viscosity limits.

The original manuscript's main statement for `1 < p < ∞` is retained as
`Euler2D.main_nonuniqueness`. The release theorem applies it at
`q = max(p, 2)` and uses finite-measure exponent inclusion, which also
gives the endpoint `p = 1`. A separate formal bridge derives actual
strongly measurable Bochner vorticities from the existing curl bounds
and velocity continuity, using injective Fourier coordinates.

The development also includes an uncountable delayed family of distinct
solutions. The manuscript's additional energy-conservation and
`W¹∞`-in-time conclusions are **not included** in the formalized refinement
or the selected Palomar declaration. No three-dimensional theorem,
`p = ∞` counterexample, or single datum working for all exponents is claimed.

## Proof account and formal correspondence

The main proof constructs a stationary initial velocity from an infinite
family of circular vortex cells. Its finite approximations are actual
vortex-patch Euler solutions. The contour dynamics, unstable directions,
backward orbits, and interaction estimates are proved for these concrete
fields, and the velocity departure is transferred from the contour
construction to those same finite solutions.

The scale and amplitude parameters are chosen before the finite
truncation index. Uniform curl estimates, convergence of the initial data,
and a fixed positive velocity departure therefore concern one compatible
sequence of solutions. Compactness then produces a genuine weak Euler
solution from the stationary datum. The weak identity and initial trace
pass to the limit, while the departure survives at a positive time.
Pairing this departing solution with the stationary path yields strictly
positive space-time `L²` distance. The principal assembly is
`Euler2D.circular_actual_limit_solution`, consumed by
`Euler2D.limit_solution` and `Euler2D.main_nonuniqueness`.

The release bridge chooses `q = max(p, 2)`, lowers the spatial exponents,
and constructs measurable vorticity paths. The latter step uses the
continuous Fourier coordinates of the velocity's distributional curl:
the countable coordinate map is an injection on finite-exponent spatial
`Lq`, so its measurable embedding transfers time measurability to the
vorticity itself. The uniform curl estimate gives genuine Bochner
`L∞` membership. These steps strengthen the final statement without
asking the caller to supply any of the construction's analytic inputs.

## Errata and deviations

The [source-correspondence record](docs/ERRATA-AND-DEVIATIONS.md) lists
**0 manuscript errata and 3 scope or proof-representation deviations** for
the pinned author manuscript. These entries cover the `p = 1` extension,
the explicit Bochner-vorticity realization, and the exclusion of the
additional energy and time-regularity claims from the separate corollary.

The record also documents three generic formal-helper measurability repairs,
three reselected internal bounds or dominating functions, and removal of
build-time debug output. All needed measurability premises are proved inside
the development; these compatibility changes add no input to the main theorem.

## Authorship and development

The original informal mathematical proof was developed by **Tao Tao and
Haiqi Zhang**, with assistance from ChatGPT. Aristotle and Codex developed
the Lean formalization from the authors' original informal proof, including
proof construction, integration, debugging, and automated statement audits.
Some proof code was generated by these tools. AI-assisted checks do not
constitute independent human peer review. The original TeX manuscript is
not distributed in this repository.

## Files and reproduction

| File | Purpose |
| --- | --- |
| `Challenge.lean` | Small, independently readable statement; imports only Mathlib and contains one deliberate statement hole |
| `Solution.lean` | Proof of the exact selected declaration; never imports Challenge |
| `RequestProject/Euler/Theorems.lean` | Original principal results |
| `RequestProject/Euler/FiniteLpNonuniqueness.lean` | Finite-exponent release theorem, including `p = 1` |
| `RequestProject/Euler/BochnerVorticity.lean` | Strong measurability and genuine Bochner-vorticity bridge |
| `Verification/Audit.lean` | Exact statement application and enforced axiom audits |
| `docs/ERRATA-AND-DEVIATIONS.md` | Pinned source correspondence, version changes, and explicit scope limitations |
| `formalization.yaml` | Provenance, scope, classification, automation, and review metadata |
| `comparator.json` | Challenge/Solution comparison with the three standard axioms |

The toolchain is pinned to **Lean 4.35.0-rc4**, with canonical Mathlib at
`1f414401f69059aa7eead47b53ee40bd38455eeb`. Install
[elan](https://github.com/leanprover/elan). The commands below use Linux with
Python 3.10 or newer, PyYAML, `flock` (from `util-linux`), and `bubblewrap`.
On Ubuntu, install these prerequisites with `sudo apt-get install python3-pip
python3-venv util-linux bubblewrap` and install PyYAML in a Python virtual
environment outside the repository. The Comparator requires unprivileged user
namespaces; the workflow configures them on its disposable Ubuntu runner.
Then run from the repository root, with that virtual environment activated:

```sh
lake exe cache get
python3 scripts/check_sources.py
python3 scripts/validate_metadata.py
bash scripts/build-bounded.sh
lake env lean Verification/Audit.lean
bash scripts/verify-comparator.sh
```

The bounded build limits compiler concurrency without changing the proof
checker. A push with `[fresh-project]` in its commit message disables
restoration of project build artifacts. The workflow checks that the project
build directory is empty before compiling every source; dependency caches
remain available. This mode supplies the clean project rebuild required for
release verification.

The final comparison uses the pinned toolchain's Comparator and the
Lean, NanoDa, and con-ron checkers. Its sandboxed invocation requires Linux
and `bubblewrap`; the GitHub workflow provides this environment. The
deliberate `sorry` in Challenge records the statement being checked;
the proof development and Solution must have none and must not depend
on `sorryAx`. The permitted axioms are `propext`, `Quot.sound`, and
`Classical.choice`.

The repository is licensed under Apache-2.0. Palomar checks and submission
instructions are maintained in the
[official contributor guide](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
Release preparation also consulted
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills)
and the [Pólya formalization example](https://github.com/QuanyuTang/polya-dirichlet-simply-connected-formalization-Palomar-version).

## Citation

Cite the immutable registered version, rather than the moving `main` branch:

```bibtex
@misc{tao_zhang_2026_finite_lp_euler,
  author = {Tao, Tao and Zhang, Haiqi},
  title = {Finite-{Lp} vorticity nonuniqueness for two-dimensional {Euler}},
  year = {2026},
  howpublished = {Palomar registry, PALOMAR-2026-10-28-000008, version 1},
  url = {https://palomar-registry.org/entry?id=PALOMAR-2026-10-28-000008&version=1},
  note = {Registered 2026-10-28; source commit ad7deb36ea565f34bdb784e9153073c5a220d46a}
}
```
