module

public import RequestProject.Euler.RegularizedParticleSystem
public import RequestProject.Euler.FourfoldTorusKernelApproximation

/-! Actual smooth systems for the explicitly symmetrized kernel, with
the common speed and logarithmic bounds needed by flow compactness. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff

namespace Euler2D

theorem exists_fourfoldRegularizedTorusParticleSystem
    {w : R2 → ℝ} (hw : Integrable w μT) {T : ℝ} (hT : 0 ≤ T)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ≥0, Nonempty
      (SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel ε hε) w T C C) := by
  obtain ⟨C, hM, _hD, hL⟩ := fourfoldRegularizedTorusKernel_bounds hε hε1
  refine ⟨C, exists_smoothRegularizedParticleSystem
    ((fourfoldRegularizedTorusKernel_smooth hε hε1).of_le (by simp)) hL hM
    (fourfoldRegularizedTorusKernel_periodic ε hε)
    (fourfoldRegularizedTorusKernel_divergence hε hε1) hw hT⟩

theorem norm_fourfoldRegularizedParticleVelocity_le
    {ε T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {w : R2 → ℝ} {L M : ℝ≥0}
    (S : SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel ε hε) w T L M)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂μT, ‖w y‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    ‖S.velocity t x‖ ≤ B * ∫ y in torusBox, ‖torusBiotSavartKernel y‖ := by
  rw [S.transported_integral t ht x]
  exact norm_fourfoldRegularizedTorusVelocity_le hε hε1 hB0 (S.ae_bound_transported hB t) x

theorem norm_fourfoldRegularizedParticleVelocity_sub_le
    {ε T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {w : R2 → ℝ} {L M : ℝ≥0}
    (S : SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel ε hε) w T L M)
    (hw : AEStronglyMeasurable w μT) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ y ∂μT, ‖w y‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x z : R2) :
    ‖S.velocity t x - S.velocity t z‖ ≤ B * torusKernelTranslationError (x - z) := by
  have hwt : AEStronglyMeasurable (fun y => w (torusWrap (S.backward t y))) μT :=
    hw.comp_quasiMeasurePreserving (S.backward_area t).quasiMeasurePreserving
  rw [S.transported_integral t ht x, S.transported_integral t ht z]
  exact norm_fourfoldRegularizedTorusVelocity_sub_le hε hε1 hwt hB0
    (S.ae_bound_transported hB t) x z

theorem exists_uniform_logLip_fourfoldRegularizedParticleVelocity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (w : R2 → ℝ) (T : ℝ) (L M : ℝ≥0)
        (S : SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel ε hε) w T L M)
        (B : ℝ), AEStronglyMeasurable w μT → 0 ≤ B →
        (∀ᵐ y ∂μT, ‖w y‖ ≤ B) → ∀ t ∈ Icc (0 : ℝ) T,
        ∀ x z, ‖x - z‖ ≤ 1 / 2 → ‖S.velocity t x - S.velocity t z‖ ≤
          (B * C) * logFlowModulus ‖x - z‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  refine ⟨C, hC, fun ε hε hε1 w T L M S B hw hB0 hB t ht x z hxz => ?_⟩
  exact (norm_fourfoldRegularizedParticleVelocity_sub_le hε hε1 S hw hB0 hB ht x z).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound (x - z) hxz) hB0)

end Euler2D

end
