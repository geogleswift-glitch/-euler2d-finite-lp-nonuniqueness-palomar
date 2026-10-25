module

public import RequestProject.Euler.LogLipschitz
public import RequestProject.Euler.Osgood

/-! The genuine planar Biot--Savart estimate in the exact modulus used
by particle uniqueness, including the entire half-unit neighborhood. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory

namespace Euler2D

theorem velocityC_logFlowModulus_le {f : ℂ → ℝ} {M A : ℝ}
    (hf : Integrable f) (hM : ∀ x, |f x| ≤ M)
    (hA : ∫ x, |f x| ≤ A) {x y : ℂ} (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖velocityC f x - velocityC f y‖ ≤ (8 * (M + A)) * logFlowModulus ‖x - y‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hA0 : 0 ≤ A := (integral_nonneg (fun x => abs_nonneg (f x))).trans hA
  have hsum : 0 ≤ M + A := add_nonneg hM0 hA0
  have hd : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hlog : Real.log ‖x - y‖ ≤ 0 := Real.log_nonpos hd (by linarith)
  have hmod : ‖x - y‖ ≤ logFlowModulus ‖x - y‖ := by
    unfold logFlowModulus
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hd hlog]
  have hmod0 : 0 ≤ logFlowModulus ‖x - y‖ := hd.trans hmod
  by_cases hz : x = y
  · simp [hz, logFlowModulus]
  have hd0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  by_cases hquarter : ‖x - y‖ ≤ 1 / 4
  · have he := velocity_log_lipschitz hf hM hd0 hquarter
    have hrewrite : ‖x - y‖ * (1 + Real.log (1 / ‖x - y‖)) =
        logFlowModulus ‖x - y‖ := by
      rw [one_div, Real.log_inv]
      unfold logFlowModulus
      ring
    calc
      ‖velocityC f x - velocityC f y‖ ≤
          5 * (M + ∫ x, |f x|) * logFlowModulus ‖x - y‖ := by
        simpa only [mul_assoc, hrewrite] using he
      _ ≤ 5 * (M + A) * logFlowModulus ‖x - y‖ := by
        gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) hmod0
  · have hbig : 1 / 4 ≤ ‖x - y‖ := (lt_of_not_ge hquarter).le
    have hb (z : ℂ) : ‖velocityC f z‖ ≤ M + A := by
      have hv := velocity_bound_split hf hM z (d := 1) (by norm_num)
      have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hAI : 0 ≤ ∫ x, |f x| := integral_nonneg (fun x => abs_nonneg _)
      have hdiv : (∫ x, |f x|) / (2 * Real.pi) ≤ A :=
        (div_le_self hAI hπ).trans hA
      simp only [mul_one] at hv
      exact hv.trans (add_le_add_right hdiv M)
    calc
      ‖velocityC f x - velocityC f y‖ ≤ ‖velocityC f x‖ + ‖velocityC f y‖ := norm_sub_le _ _
      _ ≤ 2 * (M + A) := by linarith [hb x, hb y]
      _ ≤ 8 * (M + A) * logFlowModulus ‖x - y‖ := by
        nlinarith [mul_le_mul_of_nonneg_left (hbig.trans hmod) hsum]

end Euler2D
