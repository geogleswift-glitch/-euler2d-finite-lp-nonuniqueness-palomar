# Source correspondence and deviations

Authors: Tao Tao and Haiqi Zhang

This record concerns the authors' private manuscript and the selected theorem
`PalomarEuler.main_result`. It does not assert a correction to the manuscript's
main mathematical theorem. The manuscript is not distributed here. The source
snapshot used for comparison has SHA-256
`9c5dea303cfbd479c84371d97e0aeb0da9860e51f8b027a9b4255caf4459d4d9`.

## Mathematical scope

| Item | Formalization and scope |
| --- | --- |
| Main result | For each positive time length and each prescribed finite real exponent `p ≥ 1`, two distinct unforced weak Euler solutions on the square torus have one common existential initial datum and vorticity in Bochner `L∞([0,T]; Lp)` |
| Source exponent | The manuscript's main statement for `1 < p < ∞` is retained in `Euler2D.main_nonuniqueness`; the selected declaration also includes `p = 1` by applying that theorem at `q = max(p,2)` and lowering exponents |
| Choice of datum | The datum may depend on `T` and `p`; the theorem does not provide one datum simultaneously for all exponents or nonuniqueness for every prescribed datum |
| Torus model | Lebesgue measure on `[0,2π)²`, with smooth spatially periodic test functions; all velocity norms, curl identities, and weak equations use this same measure and model |
| Vorticity measurability | A proved additional bridge supplies strongly measurable spatial `Lp`-valued paths, literal Mathlib `MemLp` at time exponent infinity, and the distributional curl identity at every time in `[0,T]` |
| Additional manuscript refinement | The development includes an uncountable delayed family, but the manuscript's additional energy-conservation and `W¹∞`-in-time assertions are not part of the formalized refinement or selected declaration |
| Survey Problem 6 | The selected theorem concerns its first, two-dimensional finite-`Lp` question; no separate Onsager/uniqueness threshold comparison or three-dimensional result is asserted |

The main theorem accepts only `T > 0` and the finite real exponent bound
`1 ≤ p`. Its local `Fact (1 ≤ ENNReal.ofReal p)` instance is constructed from
that numerical inequality inside the proposition and proof. It is not an
additional caller-supplied analytic assumption.

## Lean-version compatibility

The project was originally checked with Lean 4.28. The submission candidate
uses the canonical Mathlib revision and Lean toolchain pinned in the repository.
Compatibility changes explicitly unfold pointwise function operations, expose
existing derivative equalities, adapt library argument order, and obtain
measurability from existing `MemLp` proofs. These changes must not add premises
to the selected principal results or change their mathematical definitions.

One unused helper, `Euler2D.twoInterface_eLpNorm_top`, now explicitly assumes
measurability of both label domains. The newer Mathlib extended `Lp` norm
assigns infinity to functions without the required strong measurability, so the
old unrestricted helper is not valid under that newer convention. This is a
repair to a formal helper, not a claimed manuscript erratum. It has no callers
in this project and adds no premise to any principal result.

Two generic norm estimates in `SmoothSobolev.lean`,
`eLpNorm_le_torusSobolevBound` and
`eLpNorm_le_torusLocalizedSobolevBound`, now also state the necessary
`AEStronglyMeasurable` premise explicitly. Their four internal applications
obtain that premise from already available continuity proofs. Both higher-level
`C¹` Sobolev results keep their original statements, and the localized estimate
still applies to an arbitrary set without a new set-measurability assumption.
This is another compatibility repair to generic formal helpers; it adds no
analytic premise to the main theorem.

Three smoothing proofs now estimate the evaluated multiplication map directly.
In `BoundedVelocityMollification.lean` and `PlanarSmoothKernel.lean`, an
existential Lipschitz-bound witness is reselected;
`BoundedVelocityMollificationSpatialC1.lean` uses a new integrable dominating
function. These internal bounds are not asserted to be numerically equal to
their earlier expressions. The public statements, actual mollifiers and
kernels, and derivative convolution formulas retain their original definitions.

The source-facing files `RequestProject/Euler/Basic.lean` and
`RequestProject/Euler/Theorems.lean` retain the original source bytes. The
additional finite-exponent and Bochner bridges prove a stronger final statement
using the same underlying definitions.

## Build portability cleanup

Eight build-time debug file writes and twenty debug console writes were removed
from four modules: `CircularCoupledActualRotatingMaterialDynamics.lean`,
`CircularCoupledDeepestEarlierEntry.lean`,
`CircularDeepestCaptureScaleTrajectory.lean`, and
`CircularParentCaptureScaleTrajectory.lean`. One removed command was at module
scope; the remaining writes were debugging tactics. They did not read data back
or construct proof terms. Mathematical statements, definitions, proof inputs,
and the actual data and witnesses remain unchanged.

An earlier source preflight masked literal strings before its proof-token
checks and did not detect these filesystem paths or side effects. The
preflight now checks common absolute private paths in raw public text and
rejects direct filesystem and debug-output calls in Lean proof sources. This
targeted guard does not claim to audit arbitrary metaprogram execution.

## Verification state

**Release verification remains pending.** Original-toolchain compilation,
explicit statement applications, and standard-axiom audits have passed locally.
The full pinned-toolchain build, fresh Linux workflows, sandboxed Comparator
comparison, and independent kernel replay must finish before release readiness
is asserted. Workflow badges and logs identify the actual checked commit.

The sole deliberate proof hole is the statement placeholder in `Challenge.lean`.
`Solution.lean` and its entire proof dependency closure do not import Challenge
and may not contain proof holes or depend on `sorryAx`. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted.

Automated source and statement reviews are not independent human mathematical
peer review. No Palomar acceptance or registration is claimed.
