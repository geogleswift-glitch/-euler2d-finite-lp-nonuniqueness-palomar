module

public import RequestProject.Euler.TorusGreenCorrection
public import RequestProject.Euler.VorticityMomentum
public import RequestProject.Euler.TorusTransport

/-!
# Global bounds for the actual smooth periodic correction velocity

The compact fundamental square bounds every continuous periodic field.
Periodicity of its genuine Fréchet derivative then bounds the derivative
on the whole covering plane, so the mean value theorem gives a global
Lipschitz constant.  These conclusions are instantiated for the actual
perpendicular gradient of the constructed Green correction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace Euler2D

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Periodicity commutes with the actual Fréchet derivative, even before
any differentiability assumptions are imposed. -/
lemma IsTorusPeriodic.fderiv {f : R2 → F} (hf : IsTorusPeriodic f) :
    IsTorusPeriodic (fderiv ℝ f) := by
  intro x i
  have he : (fun y => f (y + EuclideanSpace.single i (2 * π))) = f :=
    funext (fun y => hf y i)
  have h := congrArg (fun g : R2 → F => _root_.fderiv ℝ g x) he
  change _root_.fderiv ℝ (fun y => f (y + EuclideanSpace.single i (2 * π))) x =
    _root_.fderiv ℝ f x at h
  rw [fderiv_comp_add_right] at h
  exact h

omit [NormedSpace ℝ F] in
/-- Every continuous periodic field has a genuine global bound on the
covering plane, not just an almost-everywhere bound in the square. -/
theorem exists_global_bound_of_continuous_periodic {f : R2 → F}
    (hf : Continuous f) (hp : IsTorusPeriodic f) :
    ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_closedBox.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, fun x => ?_⟩
  change ‖f x‖ ≤ max C 0
  calc
    ‖f x‖ = ‖f (torusWrap x)‖ := congrArg norm (hp.eq_torusWrap x).symm
    _ ≤ C := hC _ (torusBox_subset_closedBox (torusRep_mem (torusProj x)))
    _ ≤ max C 0 := le_max_left _ _

/-- A continuously differentiable periodic field has a globally bounded
Fréchet derivative. -/
theorem exists_global_fderiv_bound_of_contDiff_periodic {f : R2 → F}
    (hf : ContDiff ℝ 1 f) (hp : IsTorusPeriodic f) :
    ∃ C : ℝ≥0, ∀ x, ‖fderiv ℝ f x‖ ≤ C :=
  exists_global_bound_of_continuous_periodic (hf.continuous_fderiv one_ne_zero) hp.fderiv

/-- The global derivative bound yields an actual global Lipschitz
constant by the mean value theorem on the whole Euclidean plane. -/
theorem exists_lipschitzWith_of_contDiff_periodic {f : R2 → F}
    (hf : ContDiff ℝ 1 f) (hp : IsTorusPeriodic f) :
    ∃ C : ℝ≥0, LipschitzWith C f := by
  obtain ⟨C, hC⟩ := exists_global_fderiv_bound_of_contDiff_periodic hf hp
  exact ⟨C, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero)
    (fun x => NNReal.coe_le_coe.mp (hC x))⟩

/-- One common constant controls the field, its actual derivative, and
its global Lipschitz estimate. -/
theorem exists_bounded_lipschitz_of_contDiff_periodic {f : R2 → F}
    (hf : ContDiff ℝ 1 f) (hp : IsTorusPeriodic f) :
    ∃ C : ℝ≥0, (∀ x, ‖f x‖ ≤ C) ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ C) ∧ LipschitzWith C f := by
  obtain ⟨A, hA⟩ := exists_global_bound_of_continuous_periodic hf.continuous hp
  obtain ⟨B, hB⟩ := exists_global_fderiv_bound_of_contDiff_periodic hf hp
  have hB' (x : R2) : ‖fderiv ℝ f x‖ ≤ (max A B : ℝ≥0) :=
    (hB x).trans (by exact_mod_cast le_max_right A B)
  refine ⟨max A B, (fun x => (hA x).trans ?_), hB', ?_⟩
  · exact_mod_cast le_max_left A B
  · exact lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero)
      (fun x => NNReal.coe_le_coe.mp (hB' x))

/-- Global bounds for the genuine smooth correction in the torus
Biot--Savart kernel. -/
theorem exists_torusGreenCorrection_perpGradient_bounds :
    ∃ C : ℝ≥0,
      (∀ x, ‖perpGradient torusGreenCorrection x‖ ≤ C) ∧
      (∀ x, ‖fderiv ℝ (perpGradient torusGreenCorrection) x‖ ≤ C) ∧
      LipschitzWith C (perpGradient torusGreenCorrection) :=
  exists_bounded_lipschitz_of_contDiff_periodic
    ((contDiff_perpGradient torusGreenCorrection_smooth).of_le (by decide))
    (isTorusPeriodic_perpGradient torusGreenCorrection_periodic)

end Euler2D

end
