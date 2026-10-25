module

public import RequestProject.Euler.RegularizedTorusParticleSystem
public import RequestProject.Euler.RegularizedKernelVelocityBounds

/-!
# Bounds for the actual self-consistent regularized particle velocities

The kernel bounds apply to the Eulerian density supplied by the actual
inverse particle map.  Their constants are independent of the smoothing
scale and of the Lipschitz constants used to construct each smooth flow.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff

namespace Euler2D

theorem norm_regularizedParticleVelocity_le
    {w : R2 → ℝ} {T ε : ℝ} {L M : ℝ≥0} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (S : SmoothRegularizedParticleSystem (regularizedTorusKernel ε hε) w T L M)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂μT, ‖w y‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    ‖S.velocity t x‖ ≤ B * ∫ y in torusBox, ‖torusBiotSavartKernel y‖ := by
  rw [S.transported_integral t ht x]
  exact norm_regularizedTorusVelocity_le hε hε1 hB0 (S.ae_bound_transported hB t) x

/-- One logarithmic regularity constant works for every genuinely
self-consistent smooth-kernel system and every smoothing scale. -/
theorem exists_uniform_logLip_regularizedParticleVelocity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (w : R2 → ℝ) (T : ℝ) (L M : ℝ≥0)
        (S : SmoothRegularizedParticleSystem (regularizedTorusKernel ε hε) w T L M)
        (B : ℝ), AEStronglyMeasurable w μT → 0 ≤ B →
        (∀ᵐ y ∂μT, ‖w y‖ ≤ B) → ∀ t ∈ Icc (0 : ℝ) T,
        ∀ x z, ‖x - z‖ ≤ 1 / 2 →
        ‖S.velocity t x - S.velocity t z‖ ≤ (B * C) * logFlowModulus ‖x - z‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_logLip_regularizedKernelVelocity
  refine ⟨C, hC, fun ε hε hε1 w T L M S B hw hB0 hB t ht x z hxz => ?_⟩
  rw [S.transported_integral t ht x, S.transported_integral t ht z]
  exact hb ε hε hε1 (fun y => w (torusWrap (S.backward t y))) B
    (hw.comp_quasiMeasurePreserving (S.backward_area t).quasiMeasurePreserving)
    hB0 (S.ae_bound_transported hB t) x z hxz

end Euler2D

end
