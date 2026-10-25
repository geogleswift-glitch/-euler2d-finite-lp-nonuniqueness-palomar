module

public import RequestProject.Euler.FiniteContourPlanarVelocity
public import RequestProject.Euler.ComplexPlanarBiotSavart
public import RequestProject.Euler.PlanarLogFlowMeasure
public import RequestProject.Euler.BoundedVelocityMollificationSpatialC1

/-! The unchanged genuine finite-patch planar velocity supplies
the actual incompressibility and smooth approximation hypotheses.
Its true planar forward and inverse particle maps preserve area. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

section FiniteContours

variable {γ : ℝ≥0} {ι : Type*} [Fintype ι] {T : ℝ}
  (hT : 0 ≤ T) (g : ι → ℝ)
  (Z : Icc (0 : ℝ) T → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
  (r : ι → ℝ) (hr : ∀ i, 0 < r i)
  (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
  (hsmall : ∀ t i, ‖Z t i - Z₀ i‖ ≤ r i / 4)

theorem isPlanarWeaklyDivergenceFree_finiteContourPlanarVelocity (t : ℝ) :
    IsPlanarWeaklyDivergenceFree (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall t) := by
  apply isPlanarWeaklyDivergenceFree_velocityC
    (integrable_finiteContourC1PatchVorticity g (Z (projIcc 0 T hT t)) Z₀ r hr href (hsmall _))
  intro z
  simpa only [Real.norm_eq_abs] using
    abs_finiteContourC1PatchVorticity_le g (Z (projIcc 0 T hT t)) Z₀ r hr href (hsmall _) z

theorem isC1SpatialVelocity_finiteContourPlanarApproximation
    (hZ : ∀ i, Continuous (fun t => Z t i)) (n : ℕ) :
    IsC1SpatialVelocity (smoothBoundedLogVelocityApproximation
      (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) n) := by
  exact isC1SpatialVelocity_boundedVelocityMollification (planarVelocityMollifier_compact _)
    (planarVelocityMollifier_smooth _)
    (continuous_finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall hZ)
    (norm_finiteContourPlanarVelocity_le hT g Z Z₀ r hr href hsmall)

theorem divergence_finiteContourPlanarApproximation_zero
    (hZ : ∀ i, Continuous (fun t => Z t i)) (n : ℕ) (t : ℝ) (x : R2) :
    pd 0 (smoothBoundedLogVelocityApproximation (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) n t) x 0 +
      pd 1 (smoothBoundedLogVelocityApproximation (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) n t) x 1 = 0 := by
  exact divergence_boundedVelocityMollification_zero (planarVelocityMollifier_compact _)
    (planarVelocityMollifier_smooth _)
    (continuous_finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall hZ)
    (isPlanarWeaklyDivergenceFree_finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) t x

theorem exists_finiteContour_measurePreserving_planarLogParticleFlow
    (hZ : ∀ i, Continuous (fun t => Z t i)) :
    ∃ S : PlanarLogParticleFlow (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) T,
      ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume := by
  obtain ⟨M, C, K, hvn, hs, hmod, hconv⟩ :=
    exists_smoothApproximation_finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall hZ
  exact exists_measurePreserving_planarLogParticleFlow
    (continuous_finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall hZ)
    (smoothBoundedLogVelocityApproximation (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall))
    K M C hvn hmod hconv
    (isC1SpatialVelocity_finiteContourPlanarApproximation hT g Z Z₀ r hr href hsmall hZ)
    (divergence_finiteContourPlanarApproximation_zero hT g Z Z₀ r hr href hsmall hZ) hT

end FiniteContours

end Euler2D

end
