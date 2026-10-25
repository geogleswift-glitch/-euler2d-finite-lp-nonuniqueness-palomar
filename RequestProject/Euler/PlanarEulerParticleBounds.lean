module

public import RequestProject.Euler.PlanarParticleEquationLimit

/-! The actual singular-kernel particle solutions preserve the full
planar density norms and have bounds independent of the time horizon. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D
namespace PlanarEulerParticleSystem

variable {w : R2 → ℝ} {T : ℝ} (S : PlanarEulerParticleSystem w T)

def vorticity (t : ℝ) (x : R2) : ℝ := w (S.particles.backward t x)

theorem velocity_eq (t : ℝ) (x : R2) :
    S.velocity t x = planarKernelVelocity kernelK (S.vorticity t) x := S.selfconsistent t x

theorem vorticity_zero (hT : 0 ≤ T) : S.vorticity 0 = w := by
  funext x
  have hi := S.particles.left_inv 0 ⟨le_rfl, hT⟩ x
  rw [S.particles.initial] at hi
  exact congrArg w hi

theorem integrable_vorticity (hw : Integrable w) (t : ℝ) :
    Integrable (S.vorticity t) := (S.backward_area t).integrable_comp_of_integrable hw

theorem integral_norm_vorticity (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ x, ‖S.vorticity t x‖) = ∫ x, ‖w x‖ :=
  (S.backward_area t).integral_comp (S.particles.homeomorph ⟨t, ht⟩).symm.measurableEmbedding
    (fun x : R2 => ‖w x‖)

theorem norm_vorticity_le {B : ℝ} (hB : ∀ x, ‖w x‖ ≤ B) (t : ℝ) (x : R2) :
    ‖S.vorticity t x‖ ≤ B := hB _

theorem eLpNorm_vorticity (hw : Integrable w) (p : ℝ≥0∞)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : eLpNorm (S.vorticity t) p volume = eLpNorm w p volume :=
  eLpNorm_comp_measurePreserving hw.aestronglyMeasurable (S.backward_area t)

theorem norm_velocity_le {B : ℝ} (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    ‖S.velocity t x‖ ≤ planarBiotSavartMassBound B (∫ y, ‖w y‖) := by
  rw [S.velocity_eq]
  exact norm_planarBiotSavart_le_massBound (S.integrable_vorticity hw t) (S.norm_vorticity_le hB t)
    (S.integral_norm_vorticity t ht).le x

theorem velocity_logFlowModulus_le {B : ℝ} (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x y : R2} (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖S.velocity t x - S.velocity t y‖ ≤
      (8 * (B + ∫ z, ‖w z‖)) * logFlowModulus ‖x - y‖ := by
  rw [S.velocity_eq, S.velocity_eq]
  exact planarBiotSavart_logFlowModulus_le (S.integrable_vorticity hw t)
    (S.norm_vorticity_le hB t) (S.integral_norm_vorticity t ht).le hxy

end PlanarEulerParticleSystem

theorem exists_expanding_planarEulerParticleSystems {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B) :
    ∃ S : ∀ n : ℕ, PlanarEulerParticleSystem (planarBoxSource w) ((n : ℝ) + 1),
    ∃ V C : ℝ, 0 ≤ V ∧ 0 ≤ C ∧
      (∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) → ∀ x, ‖(S n).velocity t x‖ ≤ V) ∧
      ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
        ‖(S n).velocity t x - (S n).velocity t y‖ ≤ C * logFlowModulus ‖x - y‖ := by
  let S (n : ℕ) := Classical.choice (exists_planarEulerParticleSystem hw hB hwB
    (by positivity : 0 ≤ (n : ℝ) + 1))
  let A := ∫ y, ‖planarBoxSource w y‖
  have hA : 0 ≤ A := integral_nonneg (fun y => norm_nonneg _)
  refine ⟨S, planarBiotSavartMassBound B A, 8 * (B + A), ?_, by positivity, ?_, ?_⟩
  · unfold planarBiotSavartMassBound
    positivity
  · intro n t ht x
    exact (S n).norm_velocity_le (integrable_planarBoxSource hw) (norm_planarBoxSource_le hB hwB) ht x
  · intro n t ht x y hxy
    exact (S n).velocity_logFlowModulus_le (integrable_planarBoxSource hw)
      (norm_planarBoxSource_le hB hwB) ht hxy

end Euler2D

end
