module

public import RequestProject.Euler.ContourLogPotentialRegularization
public import RequestProject.Euler.PlanarKernelIntegrals
public import RequestProject.Euler.AnnularDepartureTest

/-! The inverse-distance majorant is genuinely integrable on bounded
planar domains, with its actual singularity retained. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory Metric

namespace Euler2D

theorem integrableOn_inverse_norm_R2_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun y : R2 => ‖y‖⁻¹) (closedBall (0 : R2) R) := by
  have hi := (integrableOn_norm_kernelK_closedBall hR).const_mul (2 * Real.pi)
  apply hi.congr
  exact ae_of_all _ (fun y => by
    change (2 * Real.pi) * ‖kernelK y‖ = ‖y‖⁻¹
    rw [norm_planar_kernelK]
    field_simp [Real.pi_ne_zero])

theorem integrableOn_inverse_norm_complex_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun y : ℂ => ‖y‖⁻¹) (closedBall (0 : ℂ) R) := by
  apply (measurePreserving_planeComplexEquiv.integrableOn_comp_preimage
    planeComplexEquiv.measurableEmbedding).mp
  have hp : planeComplexEquiv ⁻¹' closedBall (0 : ℂ) R = closedBall (0 : R2) R := by
    ext y
    simp only [mem_preimage, mem_closedBall_zero_iff, norm_planeComplexEquiv]
  simpa only [hp, Function.comp_def, norm_planeComplexEquiv] using
    integrableOn_inverse_norm_R2_closedBall hR

theorem integrableOn_inverse_distance_complex_closedBall (x : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun y : ℂ => ‖y - x‖⁻¹) (closedBall x R) := by
  have ht := (measurePreserving_sub_right (volume : Measure ℂ) x).integrableOn_comp_preimage
    (MeasurableEquiv.subRight x).measurableEmbedding
    (f := fun y : ℂ => ‖y‖⁻¹) (s := closedBall (0 : ℂ) R)
  have hp : (fun y : ℂ => y - x) ⁻¹' closedBall (0 : ℂ) R = closedBall x R := by
    ext y
    simp only [mem_preimage, mem_closedBall_zero_iff, mem_closedBall, dist_eq_norm, sub_zero]
  simpa only [hp, Function.comp_def] using
    ht.mpr (integrableOn_inverse_norm_complex_closedBall hR)

theorem integrableOn_inverse_distance_complex_of_subset_closedBall (x : ℂ)
    {D : Set ℂ} {R : ℝ} (hR : 0 ≤ R) (hD : D ⊆ closedBall (0 : ℂ) R) :
    IntegrableOn (fun y : ℂ => ‖y - x‖⁻¹) D := by
  apply (integrableOn_inverse_distance_complex_closedBall x (add_nonneg hR (norm_nonneg x))).mono_set
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_sub_le y x).trans (add_le_add (mem_closedBall_zero_iff.mp (hD hy)) le_rfl)

end Euler2D

end
