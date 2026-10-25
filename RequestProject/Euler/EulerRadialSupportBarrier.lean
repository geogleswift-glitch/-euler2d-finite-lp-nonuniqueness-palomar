module

public import RequestProject.Euler.EulerVelocitySupportWindow

/-! A radius barrier for the actual torus Euler particles.  Only the
radial component of the real velocity is used, so arbitrarily large
solid rotations do not enlarge the support estimate. -/

@[expose] public section

set_option maxHeartbeats 2100000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open scoped RealInnerProductSpace

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem forward_radius_le_of_radial_barrier {H a₀ a₁ B V L F : ℝ}
    (hH : 0 ≤ H) (hHT : H ≤ T) (ha₀ : 0 ≤ a₀) (ha₀₁ : a₀ ≤ a₁)
    (ha₁ : 0 < a₁) (hB : 0 < B) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hF : V + L * B ^ 3 < F) (hbudget : a₁ + F * H ≤ B)
    (hradial : ∀ t ∈ Icc (0 : ℝ) H, ∀ x, ‖x - torusCenter‖ ≤ B →
      inner ℝ (x - torusCenter) (particleVelocityRepresentative f S.backward S.backward_area t x) ≤
        ‖x - torusCenter‖ * (V + L * ‖x - torusCenter‖ ^ 3))
    {y : R2} (hy : ‖y - torusCenter‖ ≤ a₀) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) :
    ‖S.forward t y - torusCenter‖ ≤ a₁ + F * t := by
  have hFpos : 0 < F := (add_nonneg hV (mul_nonneg hL (pow_nonneg hB.le 3))).trans_lt hF
  have htime (s : ℝ) (hs : s ∈ Icc (0 : ℝ) H) : 0 < a₁ + F * s := by
    nlinarith [mul_nonneg hFpos.le hs.1]
  let G : ℝ → ℝ := fun s => ‖S.forward s y - torusCenter‖ ^ 2
  let G' : ℝ → ℝ := fun s => 2 *
    inner ℝ (S.forward s y - torusCenter)
      (particleVelocityRepresentative f S.backward S.backward_area s (S.forward s y))
  have hc : ContinuousOn G (Icc (0 : ℝ) H) :=
    (((S.forward_continuous.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2).continuousOn
  have hd : ∀ s ∈ Ico (0 : ℝ) H, HasDerivWithinAt G (G' s) (Ici s) s := by
    intro s hs
    exact ((S.derivative s ⟨hs.1, hs.2.le.trans hHT⟩ y).sub_const torusCenter).norm_sq.hasDerivWithinAt
  have hinit : G 0 ≤ (a₁ + F * 0) ^ 2 := by
    simp only [G, S.initial, mul_zero, add_zero]
    exact pow_le_pow_left₀ (norm_nonneg _) (hy.trans ha₀₁) 2
  have hbd (s : ℝ) : HasDerivAt (fun s => (a₁ + F * s) ^ 2) (2 * (a₁ + F * s) * F) s := by
    have hbarrier := ((hasDerivAt_const s a₁).add ((hasDerivAt_id s).const_mul F)).pow 2
    simp only [Pi.add_def, Pi.pow_def] at hbarrier
    convert hbarrier using 1 <;> dsimp <;> ring
  have hbound := image_le_of_deriv_right_lt_deriv_boundary hc hd hinit hbd (fun s hs he => by
    have hscc : s ∈ Icc (0 : ℝ) H := ⟨hs.1, hs.2.le⟩
    have hp := htime s hscc
    have hnorm : ‖S.forward s y - torusCenter‖ = a₁ + F * s := by
      dsimp [G] at he
      nlinarith [norm_nonneg (S.forward s y - torusCenter)]
    have hlocal : ‖S.forward s y - torusCenter‖ ≤ B := by
      rw [hnorm]
      exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs.2.le hFpos.le)).trans hbudget
    have hrad := hradial s hscc (S.forward s y) hlocal
    have hpow := pow_le_pow_left₀ (norm_nonneg (S.forward s y - torusCenter)) hlocal 3
    have hdot := hrad.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hL)) (norm_nonneg _))
    dsimp [G']
    calc
      _ ≤ 2 * (‖S.forward s y - torusCenter‖ * (V + L * B ^ 3)) :=
        mul_le_mul_of_nonneg_left hdot (by norm_num)
      _ < 2 * (‖S.forward s y - torusCenter‖ * F) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hF (by rw [hnorm]; exact hp)) (by norm_num)
      _ = _ := by rw [hnorm]; ring)
  have hh := hbound ht
  have hp := htime t ht
  dsimp [G] at hh
  nlinarith [norm_nonneg (S.forward t y - torusCenter)]

end BoundedEulerParticleSystem
end Euler2D

end
