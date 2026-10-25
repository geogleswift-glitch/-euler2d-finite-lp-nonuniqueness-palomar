module

public import RequestProject.Euler.TorusMassAmplitudeVelocity
public import RequestProject.Euler.TorusPhysicalSourceMass

/-! Every label uses the same actual Euler inverse map. Its mass and
amplitude are preserved before applying the original periodic kernel. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D

theorem integral_abs_periodicCenteredSource {w : R2 → ℝ}
    (hzero : ∀ x, 1 ≤ ‖x‖ → w x = 0) :
    (∫ x in torusBox, |periodicCenteredSource w x|) = ∫ x, |w x| := by
  have hz : ∀ x, 1 ≤ ‖x‖ → |w x| = 0 := by intro x hx; rw [hzero x hx, abs_zero]
  have he (x : R2) : |periodicCenteredSource w x| = periodicCenteredSource (fun y => |w y|) x := by
    rw [periodicCenteredSource_eq_wrapped hzero, periodicCenteredSource_eq_wrapped hz]
  simp_rw [he]
  exact integral_periodicCenteredSource hz

theorem integral_abs_planarScaledDensity (A : ℝ) {r : ℝ} (hr : 0 ≤ r) (w : R2 → ℝ) :
    (∫ x, |A * w (r⁻¹ • x)|) = |A| * r ^ 2 * ∫ x, |w x| := by
  simp_rw [abs_mul]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun x => |w x|) hr]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  ring

theorem norm_periodicCenteredSource_le {w : R2 → ℝ} {B : ℝ}
    (hzero : ∀ x, 1 ≤ ‖x‖ → w x = 0) (hB : ∀ x, ‖w x‖ ≤ B) (x : R2) :
    ‖periodicCenteredSource w x‖ ≤ B := by
  rw [periodicCenteredSource_eq_wrapped hzero]
  exact hB _

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem integrable_transportedScalar_of_integrable {w : R2 → ℝ}
    (hw : Integrable w μT) (t : ℝ) : Integrable (S.transportedScalar w t) μT :=
  (S.backward_area t).integrable_comp_of_integrable hw

theorem integral_abs_transportedScalar {w : R2 → ℝ}
    (hw : Integrable w μT) (hper : IsTorusPeriodic w) (t : ℝ) :
    (∫ x in torusBox, |S.transportedScalar w t x|) = ∫ x in torusBox, |w x| := by
  simp_rw [S.transportedScalar_eq_of_periodic hper]
  exact (S.backward_area t).integral_comp hw.abs.aestronglyMeasurable
    (fun x i => congrArg abs (hper x i))

theorem exists_transportedLabelVelocity_scaled_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : R2 → ℝ} {A r B₁ Binf : ℝ},
      Integrable w μT → IsTorusPeriodic w → 0 ≤ A → 0 < r → r ≤ 1 →
      0 ≤ B₁ → 0 ≤ Binf → (∀ᵐ y ∂μT, ‖w y‖ ≤ Binf * A) →
      (∫ y in torusBox, |w y|) ≤ B₁ * A * r ^ 2 → ∀ t x,
      ‖torusKernelVelocity (S.transportedScalar w t) x‖ ≤
        (Binf + B₁ + C * B₁) * A * r := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelVelocity_scaled_mass_amplitude_bound
  refine ⟨C, hC, ?_⟩
  intro w A r B₁ Binf hw hp hA hr hr1 hB₁ hBinf hM hm t x
  exact hbound (S.integrable_transportedScalar_of_integrable hw t) hA hr hr1 hB₁ hBinf
    (S.norm_transportedScalar_ae_le hM t)
    (by rwa [S.integral_abs_transportedScalar hw hp t]) x

end BoundedEulerParticleSystem

end Euler2D

end
