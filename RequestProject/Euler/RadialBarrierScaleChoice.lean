module

public import RequestProject.Euler.CircularFiniteStageRadialSupport

/-! An explicit before-scale radius constant for the genuine radial
fence. The paper's rho^2 (1+D)^3 smallness condition supplies the cubic
budget; no finite-layer or physical-scale choice enters the constant. -/

@[expose] public section

set_option maxHeartbeats 2200000

noncomputable section

open MeasureTheory Set

namespace Euler2D

def radialStageRadiusConstant (C Cw b : ℝ) : ℝ :=
  Cw + 2 + 4 * C / (b * (1 - b))

theorem radialStageRadiusConstant_pos {C Cw b : ℝ}
    (hC : 0 < C) (hCw : 0 ≤ Cw) (hb : 0 < b) (hb1 : b < 1) :
    0 < radialStageRadiusConstant C Cw b := by
  have hbb : 0 < 1 - b := sub_pos.mpr hb1
  unfold radialStageRadiusConstant
  positivity

theorem radialStage_linear_budget {C Cw b A r ρ D τ : ℝ}
    (hC : 0 < C) (hCw : 0 ≤ Cw) (hb : 0 < b) (hb1 : b < 1)
    (hA : 0 < A) (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ ≤ b / 2)
    (hD : 0 ≤ D) (hτ : 0 ≤ τ) (hτD : τ ≤ D / ((1 - b) * A)) :
    (Cw + 1) * ρ * r +
      2 * (C * A * r * (ρ / b) / (1 - ρ / b)) * τ ≤
      radialStageRadiusConstant C Cw b * ρ * r * (1 + D) := by
  have hbb : 0 < 1 - b := sub_pos.mpr hb1
  have hκ : 0 ≤ ρ / b := div_nonneg hρ.le hb.le
  have hκhalf : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith)
  have hden : 0 < 1 - ρ / b := by linarith
  have hquot : (ρ / b) / (1 - ρ / b) ≤ 2 * ρ / b := by
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left (by linarith : (1 / 2 : ℝ) ≤ 1 - ρ / b) (by positivity : 0 ≤ 2 * ρ / b)
    calc
      _ = (2 * ρ / b) * (1 / 2) := by ring
      _ ≤ _ := hh
  have hV : C * A * r * (ρ / b) / (1 - ρ / b) ≤ (2 * C / b) * A * r * ρ := by
    calc
      _ = (C * A * r) * ((ρ / b) / (1 - ρ / b)) := by ring
      _ ≤ (C * A * r) * (2 * ρ / b) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = _ := by ring
  let E := 4 * C / (b * (1 - b))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have htime : 2 * (C * A * r * (ρ / b) / (1 - ρ / b)) * τ ≤ E * ρ * r * D := by
    calc
      _ ≤ (2 * ((2 * C / b) * A * r * ρ)) * (D / ((1 - b) * A)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num)) hτD hτ (by positivity)
      _ = _ := by dsimp [E]; field_simp [hb.ne', hA.ne', ne_of_gt (sub_pos.mpr hb1)] <;> ring
  have hleft : Cw + 1 ≤ radialStageRadiusConstant C Cw b := by
    change Cw + 1 ≤ Cw + 2 + E
    linarith
  have hright : E ≤ radialStageRadiusConstant C Cw b := by
    change E ≤ Cw + 2 + E
    linarith
  calc
    _ ≤ (Cw + 1) * ρ * r + E * ρ * r * D := add_le_add le_rfl htime
    _ = ((Cw + 1) + E * D) * (ρ * r) := by ring
    _ ≤ (radialStageRadiusConstant C Cw b + radialStageRadiusConstant C Cw b * D) * (ρ * r) :=
      mul_le_mul_of_nonneg_right (add_le_add hleft (mul_le_mul_of_nonneg_right hright hD)) (by positivity)
    _ = _ := by ring

theorem radialStage_cubic_budget {C b A r ρ D Bc L Lu : ℝ}
    (hC : 0 < C) (hb : 0 < b) (hA : 0 < A) (hr : 0 < r)
    (hρ : 0 < ρ) (hρb : ρ < b) (hD : 0 ≤ D) (hBc : 0 ≤ Bc)
    (hL : 0 ≤ L) (hLu : L ≤ Lu)
    (hsmall : b * Lu * Bc ^ 3 * ρ ^ 2 * (1 + D) ^ 3 ≤ C / 2) :
    (L * A / r ^ 2) * (Bc * ρ * r * (1 + D)) ^ 3 ≤
      (C * A * r * (ρ / b) / (1 - ρ / b)) / 2 := by
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hsc : L * Bc ^ 3 * ρ ^ 2 * (1 + D) ^ 3 ≤ C / (2 * b) := by
    have hh : b * L * Bc ^ 3 * ρ ^ 2 * (1 + D) ^ 3 ≤ C / 2 :=
      (by gcongr : b * L * Bc ^ 3 * ρ ^ 2 * (1 + D) ^ 3 ≤
        b * Lu * Bc ^ 3 * ρ ^ 2 * (1 + D) ^ 3).trans hsmall
    apply (le_div_iff₀ (by positivity : 0 < 2 * b)).mpr
    nlinarith
  have hq : ρ / b ≤ (ρ / b) / (1 - ρ / b) := by
    apply (le_div_iff₀ hden).mpr
    exact mul_le_of_le_one_right (by positivity) (by linarith [div_nonneg hρ.le hb.le])
  have hV : C * A * r * (ρ / b) ≤ C * A * r * (ρ / b) / (1 - ρ / b) := by
    calc
      _ ≤ (C * A * r) * ((ρ / b) / (1 - ρ / b)) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring
  calc
    _ = (L * Bc ^ 3 * ρ ^ 2 * (1 + D) ^ 3) * (A * r * ρ) := by field_simp [hr.ne'] <;> ring
    _ ≤ (C / (2 * b)) * (A * r * ρ) := mul_le_mul_of_nonneg_right hsc (by positivity)
    _ = (C * A * r * (ρ / b)) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hV (by norm_num)

end Euler2D

end
