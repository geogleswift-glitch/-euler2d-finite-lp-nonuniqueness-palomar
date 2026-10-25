module

public import RequestProject.Euler.CircularFiniteCommonWindow

/-! A common true torus source window also gives the active-particle
distance hypothesis of mixed torus/plane material identification. -/

@[expose] public section

set_option maxHeartbeats 2600000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_finiteEuler_active_window :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T H c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 ≤ A₀) (_hb : 0 < b)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1)
        (_hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ H → H ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * H < c → c * R ≤ 1 / 4 →
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      (∀ t ∈ Icc (0 : ℝ) H, ∀ x ∈ torusBox,
        c * R < ‖x - torusCenter‖ →
          S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) H, ∀ a, ‖a - torusCenter‖ ≤ (5 / 4) * R →
        ∀ b, ‖b - torusCenter‖ ≤ (5 / 4) * R → ‖S.forward t a - S.forward t b‖ ≤ 1 / 2) ∧
      (∀ t ∈ Icc (0 : ℝ) H, ∀ a, ‖a - torusCenter‖ ≤ (5 / 4) * R →
        ∀ y, P.finiteInitialPlanarDensity s A₀ b R ρ N (y - torusCenter) ≠ 0 →
          ‖S.forward t a - S.forward t y‖ ≤ 1 / 2) := by
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  obtain ⟨Cv, hCv, hvelocity⟩ := P.exists_uniform_finiteEuler_velocity_bound
  let C := max Cs Cv
  have hC : 0 < C := hCs.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T H c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hH hHT hc hcR N S
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hCsC : Cs ≤ C := le_max_left _ _
  have hCvC : Cv ≤ C := le_max_right _ _
  have hcS : (5 / 4 : ℝ) + (Cs * A₀ / (1 - ρ / b)) * H < c := by
    have hm := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCsC hA) hden.le) hH
    linarith
  have hsupp := hsupport hs hA hb hR hRmax hρ hρ1 hρb hq hqE hH hHT hcS
    (by linarith : c * R < 1) N S
  let U := C * A₀ / (1 - ρ / b)
  have hU : 0 ≤ U := div_nonneg (mul_nonneg hC.le hA) hden.le
  have hvel : ∀ v ∈ Icc (0 : ℝ) T, ∀ x,
      ‖particleVelocityRepresentative
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
        S.backward S.backward_area v x‖ ≤ U * R := by
    intro v _ x
    refine (hvelocity hs hA hb hR hRmax hρ hρ1 hρb hq hqE N S v x).trans ?_
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCvC hA) hR.le) hden.le
    exact hh.trans_eq (by dsimp only [U]; ring)
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) (a : R2)
      (ha : ‖a - torusCenter‖ ≤ (5 / 4) * R) : ‖S.forward t a - torusCenter‖ < c * R := by
    have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hHT⟩
    have hd := S.displacement_le_of_velocity_bound (hH.trans hHT) hvel htT a
    have htri : ‖S.forward t a - torusCenter‖ ≤ ‖S.forward t a - a‖ + ‖a - torusCenter‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (S.forward t a - a) (a - torusCenter)
    have htU := mul_le_mul_of_nonneg_left ht.2 hU
    have hsmall : (5 / 4 : ℝ) + U * t < c := by
      change (5 / 4 : ℝ) + U * H < c at hc
      linarith
    have hh := mul_lt_mul_of_pos_right hsmall hR
    nlinarith
  have hpair : ∀ t ∈ Icc (0 : ℝ) H, ∀ a, ‖a - torusCenter‖ ≤ (5 / 4) * R →
      ∀ b, ‖b - torusCenter‖ ≤ (5 / 4) * R → ‖S.forward t a - S.forward t b‖ ≤ 1 / 2 := by
    intro t ht a ha b hb
    have htri : ‖S.forward t a - S.forward t b‖ ≤
        ‖S.forward t a - torusCenter‖ + ‖S.forward t b - torusCenter‖ := by
      simpa only [sub_sub_sub_cancel_right] using
        norm_sub_le (S.forward t a - torusCenter) (S.forward t b - torusCenter)
    have ha' := hpoint t ht a ha
    have hb' := hpoint t ht b hb
    linarith
  refine ⟨hsupp, hpair, ?_⟩
  intro t ht a ha y hy
  apply hpair t ht a ha y
  apply le_of_not_gt
  intro hn
  exact hy (P.finiteInitialPlanarDensity_eq_zero_of_radius hs hR hρ hρ1 N hn)

end CircularMaterialTransferProfile
end Euler2D

end
