module

public import RequestProject.Euler.PlanarMaterialLabelComparison
public import RequestProject.Euler.UniformLabelParticleUniqueness

/-! Uniqueness for actual self-consistent planar material particle
flows with a bounded Lipschitz kernel. The whole initial density is
integrated against the actual particle positions. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

structure PlanarMaterialParticleFlow (K : R2 → R2) (w : R2 → ℝ) (T : ℝ) where
  velocity : ℝ → R2 → R2
  forward : ℝ → R2 → R2
  continuous_velocity : Continuous (Function.uncurry velocity)
  continuous_forward : Continuous (Function.uncurry forward)
  initial : ∀ a, forward 0 a = a
  derivative : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => forward s a) (velocity t (forward t a)) t
  source_integral : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
    velocity t x = planarMaterialLabelVelocity K w (forward t) x

namespace PlanarMaterialParticleFlow

variable {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} (P : PlanarMaterialParticleFlow K w T)

theorem norm_forward_sub_initial_le {M : ℝ≥0} (hw : Integrable w)
    (hM : ∀ x, ‖K x‖ ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    ‖P.forward t a - a‖ ≤ ((M : ℝ) * ∫ b, ‖w b‖) * t := by
  have hV (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (x : R2) :
      ‖P.velocity s x‖ ≤ (M : ℝ) * ∫ b, ‖w b‖ := by
    rw [P.source_integral s hs x]
    exact norm_planarMaterialLabelVelocity_le hw hM _ _
  have he := norm_trajectory_sub_time_le (fun s hs => P.derivative s hs a) hV
    (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, ht.1.trans ht.2⟩) ht
  simpa only [P.initial, sub_zero, abs_of_nonneg ht.1] using he

theorem forward_eq (Q : PlanarMaterialParticleFlow K w T) {L M : ℝ≥0}
    (hw : Integrable w) (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M) (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, P.forward t a = Q.forward t a := by
  let V : ℝ := (M : ℝ) * ∫ b, ‖w b‖
  have hA : 0 ≤ ∫ b, ‖w b‖ := integral_nonneg (fun b => norm_nonneg _)
  have hV : 0 ≤ V := mul_nonneg M.coe_nonneg hA
  let vx : ℝ → R2 → R2 := fun t a => P.velocity t (P.forward t a)
  let vy : ℝ → R2 → R2 := fun t a => Q.velocity t (Q.forward t a)
  have hvc (a : R2) : Continuous (fun t => vx t a) := P.continuous_velocity.comp
    (continuous_id.prodMk (P.continuous_forward.comp (continuous_id.prodMk continuous_const)))
  have hwc (a : R2) : Continuous (fun t => vy t a) := Q.continuous_velocity.comp
    (continuous_id.prodMk (Q.continuous_forward.comp (continuous_id.prodMk continuous_const)))
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) : ‖P.forward t a - Q.forward t a‖ ≤ 2 * V * T := by
    have hp := P.norm_forward_sub_initial_le hw hM ht a
    have hq := Q.norm_forward_sub_initial_le hw hM ht a
    calc
      _ ≤ ‖P.forward t a - a‖ + ‖a - Q.forward t a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ V * t + V * t := add_le_add hp (by simpa only [norm_sub_rev] using hq)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hV]
  apply uniform_label_particle_uniqueness (B := 2 * V * T)
    (K := 2 * (L : ℝ) * ∫ b, ‖w b‖) (by positivity) (by positivity)
    P.forward Q.forward vx vy hvc hwc P.derivative Q.derivative
    (fun a => (P.initial a).trans (Q.initial a).symm) hbound
  intro t ht D hD hDist a
  dsimp only [vx, vy]
  rw [P.source_integral t ht, Q.source_integral t ht]
  exact norm_planarMaterialLabelVelocity_sub_le hw hK hM
    (P.continuous_forward.comp (continuous_const.prodMk continuous_id))
    (Q.continuous_forward.comp (continuous_const.prodMk continuous_id)) hDist a

end PlanarMaterialParticleFlow

def SmoothPlanarRegularizedParticleSystem.toMaterialFlow
    {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}
    (S : SmoothPlanarRegularizedParticleSystem K w T L M) :
    PlanarMaterialParticleFlow K (planarBoxSource w) T where
  velocity := S.velocity
  forward := S.particles.forward
  continuous_velocity := S.bounded.continuous
  continuous_forward := S.particles.continuous_forward
  initial := S.particles.initial
  derivative := S.particles.derivative
  source_integral := fun t ht x => S.velocity_eq_materialLabelVelocity ht x

end Euler2D

end
