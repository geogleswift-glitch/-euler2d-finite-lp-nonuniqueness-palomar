module

public import RequestProject.Euler.CircularFiniteUniformVelocity

/-! The cutoff-uniform speed of the original finite Euler system
controls all its initial particles and any initial label supported in
the same ball. No cancellation of the full density is used to infer
support of a complementary label. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_finiteEuler_label_active_window :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T H c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 ≤ A₀) (_hb : 0 < b)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1)
        (_hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ H → H ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * H < c → c * R < 1 →
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      (∀ t ∈ Icc (0 : ℝ) H, ∀ y, ‖y - torusCenter‖ ≤ (5 / 4) * R →
        ‖S.forward t y - torusCenter‖ < c * R) ∧
      ∀ w : R2 → ℝ,
        (∀ y ∈ torusBox, (5 / 4) * R < ‖y - torusCenter‖ → w y = 0) →
        ∀ t ∈ Icc (0 : ℝ) H, ∀ x ∈ torusBox,
          c * R < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
  obtain ⟨C, hC, hvelocity⟩ := P.exists_uniform_finiteEuler_velocity_bound
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T H c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hH hHT hc hcR N S
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  let U := C * A₀ / (1 - ρ / b)
  have hU : 0 ≤ U := div_nonneg (mul_nonneg hC.le hA) hden.le
  have hvel : ∀ v ∈ Icc (0 : ℝ) T, ∀ x,
      ‖particleVelocityRepresentative
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
        S.backward S.backward_area v x‖ ≤ U * R := by
    intro v _ x
    refine (hvelocity hs hA hb hR hRmax hρ hρ1 hρb hq hqE N S v x).trans_eq ?_
    dsimp only [U]
    ring
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) :
      (5 / 4) * R + (U * R) * t < c * R := by
    have htU := mul_le_mul_of_nonneg_left ht.2 hU
    have hh : (5 / 4 : ℝ) + U * t < c := by
      change (5 / 4 : ℝ) + U * H < c at hc
      linarith
    nlinarith [mul_lt_mul_of_pos_right hh hR]
  refine ⟨?_, ?_⟩
  · intro t ht y hy
    have hd := S.displacement_le_of_velocity_bound (hH.trans hHT) hvel
      ⟨ht.1, ht.2.trans hHT⟩ y
    have htri : ‖S.forward t y - torusCenter‖ ≤
        ‖S.forward t y - y‖ + ‖y - torusCenter‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (S.forward t y - y) (y - torusCenter)
    have hh := htime t ht
    linarith
  · intro w hw t ht x hx hxt
    exact S.transportedScalar_support_of_velocity_bound (hH.trans hHT)
      (mul_nonneg hU hR.le) hvel (by positivity) hcR hw
      ⟨ht.1, ht.2.trans hHT⟩ (htime t ht) x hx hxt

end CircularMaterialTransferProfile
end Euler2D

end
