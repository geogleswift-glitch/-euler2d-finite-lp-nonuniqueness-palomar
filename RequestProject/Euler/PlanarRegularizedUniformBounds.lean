module

public import RequestProject.Euler.PlanarRegularizedApproximationSystem
public import RequestProject.Euler.PlanarSmoothedVelocityBounds

/-! The actual nonlinear regularized planar systems have a common
speed and logarithmic spatial modulus, independent of the smoothing
scale. Their true velocities approximate the original Biot--Savart
velocities of the same actually transported densities. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D
namespace SmoothPlanarRegularizedParticleSystem

variable {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}
  (S : SmoothPlanarRegularizedParticleSystem K w T L M)

theorem integrable_vorticity (hw : Integrable w μT) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Integrable (S.vorticity t) volume :=
  (S.backward_area t ht).integrable_comp_of_integrable (integrable_planarBoxSource hw)

theorem integral_norm_vorticity {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ x, ‖S.vorticity t x‖) = ∫ x, ‖planarBoxSource w x‖ :=
  (S.backward_area t ht).integral_comp (S.particles.homeomorph ⟨t, ht⟩).symm.measurableEmbedding
    (fun x : R2 => ‖planarBoxSource w x‖)

end SmoothPlanarRegularizedParticleSystem

section UniformBounds

variable {n : ℕ} {w : R2 → ℝ} {T B A : ℝ} {L M : ℝ≥0}
  (S : SmoothPlanarRegularizedParticleSystem (planarSmoothedBiotSavartKernel n) w T L M)
  (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B)
  (hA : ∫ x, ‖planarBoxSource w x‖ ≤ A)

include hw hB hwB hA

theorem norm_planarRegularized_velocity_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    ‖S.velocity t x‖ ≤ planarBiotSavartMassBound B A := by
  rw [S.velocity_eq_planarKernelVelocity ht x]
  exact norm_planarSmoothedKernelVelocity_le_massBound (S.integrable_vorticity hw ht)
    (S.norm_vorticity_le hB hwB t) ((S.integral_norm_vorticity ht).trans_le hA) n x

theorem planarRegularized_velocity_logFlowModulus_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {x y : R2} (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖S.velocity t x - S.velocity t y‖ ≤ (8 * (B + A)) * logFlowModulus ‖x - y‖ := by
  rw [S.velocity_eq_planarKernelVelocity ht x, S.velocity_eq_planarKernelVelocity ht y]
  exact planarSmoothedKernelVelocity_logFlowModulus_le (S.integrable_vorticity hw ht)
    (S.norm_vorticity_le hB hwB t) ((S.integral_norm_vorticity ht).trans_le hA) n hxy

theorem norm_planarRegularized_velocity_sub_original_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    ‖S.velocity t x - planarKernelVelocity kernelK (S.vorticity t) x‖ ≤
      (8 * (B + A)) * logFlowModulus (planarVelocityApproxScale n) := by
  rw [S.velocity_eq_planarKernelVelocity ht x]
  exact norm_planarSmoothedKernelVelocity_sub_le (S.integrable_vorticity hw ht)
    (S.norm_vorticity_le hB hwB t) ((S.integral_norm_vorticity ht).trans_le hA) n x

end UniformBounds

theorem exists_uniform_planarBiotSavart_regularized_systems
    {w : R2 → ℝ} {B : ℝ} (hw : Integrable w μT) (hB : 0 ≤ B)
    (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B) {T : ℝ} (hT : 0 ≤ T) :
    ∃ L M : ℕ → ℝ≥0,
    ∃ S : ∀ n, SmoothPlanarRegularizedParticleSystem (planarSmoothedBiotSavartKernel n) w T (L n) (M n),
    ∃ V C : ℝ, 0 ≤ V ∧ 0 ≤ C ∧
      (∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x, ‖(S n).velocity t x‖ ≤ V) ∧
      (∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
        ‖(S n).velocity t x - (S n).velocity t y‖ ≤ C * logFlowModulus ‖x - y‖) ∧
      ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x,
        ‖(S n).velocity t x - planarKernelVelocity kernelK ((S n).vorticity t) x‖ ≤
          C * logFlowModulus (planarVelocityApproxScale n) := by
  obtain ⟨L, M, S, hK⟩ := exists_planarBiotSavart_regularized_system_sequence hw hT
  let A := ∫ x, ‖planarBoxSource w x‖
  have hA0 : 0 ≤ A := integral_nonneg (fun x => norm_nonneg _)
  refine ⟨L, M, S, planarBiotSavartMassBound B A, 8 * (B + A), ?_, by positivity, ?_, ?_, ?_⟩
  · unfold planarBiotSavartMassBound
    positivity
  · intro n t ht x
    exact norm_planarRegularized_velocity_le (S n) hw hB hwB le_rfl ht x
  · intro n t ht x y hxy
    exact planarRegularized_velocity_logFlowModulus_le (S n) hw hB hwB le_rfl ht hxy
  · intro n t ht x
    exact norm_planarRegularized_velocity_sub_original_le (S n) hw hB hwB le_rfl ht x

end Euler2D

end
