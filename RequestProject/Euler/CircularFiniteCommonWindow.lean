module

public import RequestProject.Euler.CircularFiniteUniformSupport

/-! A nonempty support interval common to all physical shrinking radii
and all finite cutoffs of the actual Euler family. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_common_finiteEuler_support_window {A₀ b ρ T : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρb : ρ < b) (hT : 0 < T) :
    ∃ ε > 0, ε ≤ T ∧ ∀ {s q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
      (hs : s ≤ 0) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      ∀ {R : ℝ} (hR : 0 < R), R ≤ 1 / 2 →
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
        (3 / 2) * R < ‖x - torusCenter‖ →
          S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0 := by
  obtain ⟨C, hC, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  let U := C * A₀ / (1 - ρ / b)
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hU : 0 ≤ U := div_nonneg (mul_nonneg hC.le hA) hden.le
  have hUd : 0 < 8 * (U + 1) := by positivity
  let ε := min T (1 / (8 * (U + 1)))
  have hε : 0 < ε := lt_min hT (div_pos (by norm_num) hUd)
  have hεT : ε ≤ T := min_le_left _ _
  have hεd : ε * (8 * (U + 1)) ≤ 1 :=
    (le_div_iff₀ hUd).mp (min_le_right _ _)
  have hsmall : (5 / 4 : ℝ) + (C * A₀ / (1 - ρ / b)) * ε < 3 / 2 := by
    change (5 / 4 : ℝ) + U * ε < 3 / 2
    nlinarith [mul_nonneg hU hε.le]
  refine ⟨ε, hε, hεT, ?_⟩
  intro s q _ hs hq hqE R hR hRmax N S
  exact hsupport hs hA hb hR hRmax hρ hρ1 hρb hq hqE hε.le hεT hsmall
    (by nlinarith : (3 / 2 : ℝ) * R < 1) N S

end CircularMaterialTransferProfile
end Euler2D

end
