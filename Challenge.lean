module

public import Mathlib

/-!
# Two-dimensional Euler on the torus: definitions and principal statements

This file formalizes Section 1 of the paper (*Definitions and principal statements*):
the square torus `𝕋² = ℝ² / (2π ℤ)²`, weak Euler solutions (Definition `def:weak-euler`),
and the objects in which the main theorem (`Theorem main`) is stated.

## Modelling conventions

* A field on the torus is modelled by a field on `ℝ²` restricted to the fundamental square
  `torusBox = [0, 2π)²`.  Elements of `L²(𝕋²; ℝ²)` are elements of the Lebesgue space
  `Lp ℝ² 2` for the Lebesgue measure restricted to `torusBox` (total mass `4π²`).
* Periodicity enters through the test functions: all test functions are smooth and
  `2π`-periodic in each space variable, so that distributional derivatives are the
  distributional derivatives on the torus.
* The space–time `L²((0,T) × 𝕋²)` norm is written as the iterated integral
  `∫₀ᵀ ‖u(t)‖²_{L²(𝕋²)} dt`.
* `L^∞(0,T; L^p)` bounds on the vorticity are stated as a uniform bound valid at *every*
  time `t ∈ [0,T]` (which is what the paper proves).
-/

@[expose] public section

open MeasureTheory Real
open scoped ContDiff

namespace Euler2D

/-- The Euclidean plane `ℝ²`. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- The fundamental square `[0,2π)²` of the torus `𝕋² = ℝ²/(2πℤ)²`. -/
def torusBox : Set R2 := {x | ∀ i, x i ∈ Set.Ico 0 (2 * π)}

/-- Lebesgue measure on the torus (realized on the fundamental square), of total mass `4π²`. -/
noncomputable abbrev μT : Measure R2 := volume.restrict torusBox

/-- `L²(𝕋²; ℝ²)`. -/
noncomputable abbrev L2T := Lp R2 2 μT

/-- A function on `ℝ²` is `2π`-periodic in each coordinate, i.e. it descends to `𝕋²`. -/
def IsTorusPeriodic {α : Type*} (f : R2 → α) : Prop :=
  ∀ (x : R2) (i : Fin 2), f (x + EuclideanSpace.single i (2 * π)) = f x

/-- The partial derivative `∂ᵢ f(x)`. -/
noncomputable def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 2) (f : R2 → F) (x : R2) : F :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- Smooth scalar test functions on the torus. -/
def IsScalarTest (ψ : R2 → ℝ) : Prop := ContDiff ℝ ∞ ψ ∧ IsTorusPeriodic ψ

/-- Distributional divergence-freeness of an `L²` field on the torus:
`∫ u · ∇ψ = 0` for every smooth periodic `ψ`. -/
def DivFree (u : R2 → R2) : Prop :=
  ∀ ψ : R2 → ℝ, IsScalarTest ψ → ∫ x in torusBox, ∑ i, u x i * pd i ψ x = 0

/-- `w` is the distributional curl `∂₁u₂ - ∂₂u₁` of `u` on the torus:
`∫ w ψ = ∫ (u₁ ∂₂ψ - u₂ ∂₁ψ)` for every smooth periodic `ψ`. -/
def IsCurl (u : R2 → R2) (w : R2 → ℝ) : Prop :=
  ∀ ψ : R2 → ℝ, IsScalarTest ψ →
    ∫ x in torusBox, w x * ψ x = ∫ x in torusBox, (u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x)

/-- `u ∈ W^{1,p}(𝕋²; ℝ²)`: `u ∈ Lᵖ` and every distributional partial derivative `∂ᵢ u_j`
is (represented by) an `Lᵖ` function `G i j`. -/
def MemW1p (p : ENNReal) (u : R2 → R2) : Prop :=
  MemLp u p μT ∧ ∃ G : Fin 2 → Fin 2 → R2 → ℝ, (∀ i j, MemLp (G i j) p μT) ∧
    ∀ i j, ∀ ψ : R2 → ℝ, IsScalarTest ψ →
      ∫ x in torusBox, u x j * pd i ψ x = -∫ x in torusBox, G i j x * ψ x

/-- Admissible test fields for the weak Euler equations on `[0,T) × 𝕋²`:
smooth in `(t,x)`, periodic in `x`, divergence free, and vanishing for `t ≥ T'` for some
`T' < T` (i.e. compactly supported in `[0,T) × 𝕋²`). -/
structure IsEulerTest (T : ℝ) (φ : ℝ → R2 → R2) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry φ)
  periodic : ∀ t, IsTorusPeriodic (φ t)
  divFree : ∀ t x, pd 0 (φ t) x 0 + pd 1 (φ t) x 1 = 0
  support : ∃ T' < T, ∀ t ≥ T', ∀ x, φ t x = 0

/-- The space–time integrand `u · ∂ₜφ + (u ⊗ u) : ∇φ` of the weak Euler formulation. -/
noncomputable def eulerIntegrand (v : R2 → R2) (φ : ℝ → R2 → R2) (t : ℝ) (x : R2) : ℝ :=
  ∑ i, v x i * deriv (fun s => φ s x i) t + ∑ i, ∑ j, v x i * v x j * pd j (φ t) x i

/-- **Definition (Weak Euler solution).** `u ∈ C([0,T]; L²(𝕋²;ℝ²))`, divergence free at every
time, with `u(0) = u₀`, and
`∫₀ᵀ∫ [u·∂ₜφ + (u⊗u):∇φ] dx dt + ∫ u₀ · φ(0,x) dx = 0` for every admissible test field. -/
structure IsWeakEulerSolution (T : ℝ) (u₀ : L2T) (u : ℝ → L2T) : Prop where
  continuous : ContinuousOn u (Set.Icc 0 T)
  divFree : ∀ t ∈ Set.Icc 0 T, DivFree (u t)
  initial : u 0 = u₀
  weak : ∀ φ, IsEulerTest T φ →
    (∫ t in (0 : ℝ)..T, ∫ x in torusBox, eulerIntegrand (u t) φ t x) +
      ∫ x in torusBox, ∑ i, u₀ x i * φ 0 x i = 0

/-- The vorticity bound with constant `M`: at every time `t ∈ [0,T]` the distributional curl of
`u(t)` is an `Lᵖ` function of `Lᵖ` norm at most `M`. -/
def CurlBoundedBy (T : ℝ) (p : ENNReal) (M : ℝ) (u : ℝ → L2T) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∃ w : R2 → ℝ,
    MemLp w p μT ∧ IsCurl (u t) w ∧ (eLpNorm w p μT).toReal ≤ M

/-- `curl u ∈ L^∞(0,T; Lᵖ(𝕋²))`: at every time the distributional curl is an `Lᵖ` function,
with a bound uniform in `t ∈ [0,T]`. -/
def CurlBounded (T : ℝ) (p : ENNReal) (u : ℝ → L2T) : Prop :=
  ∃ M : ℝ, CurlBoundedBy T p M u

/-- The squared space–time `L²((0,T)×𝕋²)` distance of two time-dependent fields. -/
noncomputable def spaceTimeDistSq (T : ℝ) (u v : ℝ → L2T) : ℝ :=
  ∫ t in (0 : ℝ)..T, ‖u t - v t‖ ^ 2

/-! The statement of the main theorem (`Theorem main`), its reduction to Proposition
`cp:limit`, and the refinement (`Corollary intro:refinement`) are in
`RequestProject/Euler/Theorems.lean`. -/

end Euler2D

end

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open Euler2D

namespace PalomarEuler

/-- For every positive time horizon and every finite real spatial exponent
`p ≥ 1`, there are two unforced weak Euler solutions on the square torus
with the same mean-zero divergence-free `L² ∩ W¹ᵖ` initial datum, actual
strongly measurable Bochner `L∞ₜ Lp` vorticities, and positive space-time
`L²` distance. All definitions have their ordinary distributional meaning.
This is the two-dimensional finite-`Lp` question in Problem 6 of
Buckmaster and Vicol, Surveys in Mathematical Sciences 6 (2019), 173–263.
The separate comparison of critical regularity thresholds in that problem
is outside this statement. -/
theorem main_result (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 ≤ p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∃ u₀ : L2T, (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧
      MemW1p (ENNReal.ofReal p) u₀ ∧
      ∃ u₁ u₂ : ℝ → L2T, ∃ ω₁ ω₂ : ℝ → Lp ℝ (ENNReal.ofReal p) μT,
        IsWeakEulerSolution T u₀ u₁ ∧ IsWeakEulerSolution T u₀ u₂ ∧
        CurlBounded T (ENNReal.ofReal p) u₁ ∧ CurlBounded T (ENNReal.ofReal p) u₂ ∧
        StronglyMeasurable ω₁ ∧ StronglyMeasurable ω₂ ∧
        MemLp ω₁ ∞ (volume.restrict (Icc 0 T)) ∧
        MemLp ω₂ ∞ (volume.restrict (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, IsCurl (u₁ t) (ω₁ t)) ∧
        (∀ t ∈ Icc 0 T, IsCurl (u₂ t) (ω₂ t)) ∧
        0 < spaceTimeDistSq T u₁ u₂ := by
  sorry

end PalomarEuler

end
