module

public import RequestProject.Euler.CircularFiniteUniformVelocity

/-! A common physical support window for every actual finite Euler
cutoff. The velocity estimate is a sum of the individually transported
labels, so the window does not shrink with their maximal amplitude. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_finiteEuler_support_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T H c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 ≤ A₀) (_hb : 0 < b)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1)
        (_hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ H → H ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * H < c → c * R < 1 →
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ t ∈ Icc (0 : ℝ) H, ∀ x ∈ torusBox,
        c * R < ‖x - torusCenter‖ →
          S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0 := by
  obtain ⟨C, hC, hvelocity⟩ := P.exists_uniform_finiteEuler_velocity_bound
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T H c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hH hHT hc hcR N S t ht
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  let U := C * A₀ / (1 - ρ / b)
  have hU : 0 ≤ U := div_nonneg (mul_nonneg hC.le hA) hden.le
  have hT : 0 ≤ T := hH.trans hHT
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hHT⟩
  have heV : C * A₀ * R / (1 - ρ / b) = U * R := by dsimp only [U]; ring
  have hvel : ∀ v ∈ Icc (0 : ℝ) T, ∀ x,
      ‖particleVelocityRepresentative
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
        S.backward S.backward_area v x‖ ≤ U * R := by
    intro v _ x
    rw [← heV]
    exact hvelocity hs hA hb hR hRmax hρ hρ1 hρb hq hqE N S v x
  have hw : ∀ x ∈ torusBox, (5 / 4) * R < ‖x - torusCenter‖ →
      P.finiteInitialPeriodicDensity s A₀ b R ρ N x = 0 := by
    intro x hx hn
    rw [P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx]
    exact P.finiteInitialPlanarDensity_eq_zero_of_radius hs hR hρ hρ1 N hn
  have htime : (5 / 4) * R + (U * R) * t < c * R := by
    have htU := mul_le_mul_of_nonneg_left ht.2 hU
    have hbase : 5 / 4 + U * t < c := by
      change 5 / 4 + U * H < c at hc
      linarith
    have hh := mul_lt_mul_of_pos_right hbase hR
    nlinarith
  exact S.transportedScalar_support_of_velocity_bound hT (mul_nonneg hU hR.le) hvel
    (by positivity) hcR hw htT htime

end CircularMaterialTransferProfile
end Euler2D

end
