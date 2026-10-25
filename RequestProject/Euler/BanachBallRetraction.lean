module

public import Mathlib

/-! A genuine bounded two-Lipschitz radial retraction in any real
normed space. It supplies an actual global ODE extension around a
moving reference curve, without assuming compact Banach balls. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialClosedBallRetraction (r : ℝ) (x : E) : E := (r / max r ‖x‖) • x

theorem norm_radialClosedBallRetraction_le {r : ℝ} (hr : 0 < r) (x : E) :
    ‖radialClosedBallRetraction r x‖ ≤ r := by
  have hd : 0 < max r ‖x‖ := hr.trans_le (le_max_left _ _)
  rw [radialClosedBallRetraction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le hd.le)]
  calc
    _ ≤ (r / max r ‖x‖) * max r ‖x‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg hr.le hd.le)
    _ = r := div_mul_cancel₀ r hd.ne'

theorem radialClosedBallRetraction_eq {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x‖ ≤ r) :
    radialClosedBallRetraction r x = x := by
  rw [radialClosedBallRetraction, max_eq_left hx, div_self hr.ne', one_smul]

theorem norm_radialClosedBallRetraction_sub_le_of_norm_le {r : ℝ} (hr : 0 < r)
    (x y : E) (hxy : ‖x‖ ≤ ‖y‖) :
    ‖radialClosedBallRetraction r x - radialClosedBallRetraction r y‖ ≤ 2 * ‖x - y‖ := by
  let a := max r ‖x‖
  let b := max r ‖y‖
  have ha : 0 < a := hr.trans_le (le_max_left _ _)
  have hb : 0 < b := hr.trans_le (le_max_left _ _)
  have hab : a ≤ b := max_le_max le_rfl hxy
  have hcoef0 : 0 ≤ r / a - r / b := sub_nonneg.mpr
    (div_le_div_of_nonneg_left hr.le ha hab)
  have hcoef1 : r / b ≤ 1 := (div_le_one hb).mpr (le_max_left _ _)
  have hrb : 0 ≤ r / b := div_nonneg hr.le hb.le
  have hba : b - a ≤ ‖x - y‖ := by
    have hm : b ≤ a + ‖x - y‖ := by
      apply max_le
      · exact (le_max_left r ‖x‖).trans (le_add_of_nonneg_right (norm_nonneg _))
      · have hh := norm_sub_norm_le y x
        rw [norm_sub_rev y x] at hh
        have hx := le_max_right r ‖x‖
        change ‖x‖ ≤ a at hx
        linarith only [hh, hx]
    linarith only [hm]
  have hsecond : (r / a - r / b) * ‖x‖ ≤ ‖x - y‖ := by
    calc
      _ ≤ (r / a - r / b) * a := mul_le_mul_of_nonneg_left (le_max_right _ _) hcoef0
      _ = (r / b) * (b - a) := by field_simp
      _ ≤ (r / b) * ‖x - y‖ := mul_le_mul_of_nonneg_left hba hrb
      _ ≤ ‖x - y‖ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hcoef1 (norm_nonneg _)
  have heq : radialClosedBallRetraction r x - radialClosedBallRetraction r y =
      (r / b) • (x - y) + (r / a - r / b) • x := by
    dsimp only [radialClosedBallRetraction, a, b]
    module
  rw [heq]
  calc
    _ ≤ ‖(r / b) • (x - y)‖ + ‖(r / a - r / b) • x‖ := norm_add_le _ _
    _ = (r / b) * ‖x - y‖ + (r / a - r / b) * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hrb, abs_of_nonneg hcoef0]
    _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef1 (norm_nonneg _)) hsecond
    _ = _ := by ring

theorem lipschitzWith_radialClosedBallRetraction {r : ℝ} (hr : 0 < r) :
    LipschitzWith 2 (radialClosedBallRetraction r : E → E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  by_cases hh : ‖x‖ ≤ ‖y‖
  · exact norm_radialClosedBallRetraction_sub_le_of_norm_le hr x y hh
  · have ht := norm_radialClosedBallRetraction_sub_le_of_norm_le hr y x (le_of_not_ge hh)
    simpa only [norm_sub_rev] using ht

def centeredBallRetraction (r : ℝ) (c x : E) : E := c + radialClosedBallRetraction r (x - c)

theorem centeredBallRetraction_mem_closedBall {r : ℝ} (hr : 0 < r) (c x : E) :
    centeredBallRetraction r c x ∈ closedBall c r := by
  rw [mem_closedBall, dist_eq_norm, centeredBallRetraction, add_sub_cancel_left]
  exact norm_radialClosedBallRetraction_le hr _

theorem centeredBallRetraction_eq {r : ℝ} (hr : 0 < r) {c x : E}
    (hx : x ∈ closedBall c r) : centeredBallRetraction r c x = x := by
  have hn : ‖x - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hx
  rw [centeredBallRetraction, radialClosedBallRetraction_eq hr hn]
  abel

theorem lipschitzWith_centeredBallRetraction {r : ℝ} (hr : 0 < r) (c : E) :
    LipschitzWith 2 (centeredBallRetraction r c : E → E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [centeredBallRetraction, dist_add_left, dist_sub_right, NNReal.coe_ofNat] using
    (lipschitzWith_radialClosedBallRetraction hr).dist_le_mul (x - c) (y - c)

theorem continuous_centeredBallRetraction {r : ℝ} (hr : 0 < r) :
    Continuous (fun p : E × E => centeredBallRetraction r p.1 p.2) :=
  continuous_fst.add ((lipschitzWith_radialClosedBallRetraction hr).continuous.comp
    (continuous_snd.sub continuous_fst))

end Euler2D

end
