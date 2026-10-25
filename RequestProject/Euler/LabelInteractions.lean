module

public import Mathlib
public import RequestProject.Euler.ClusterField

/-!
# Interactions between separated near-circular labels (Lemmas `ib:out`, `ib:in`, planar `C⁰`)

Let `η` be the perturbation of a near-circular label of radius `r_l` (as produced by
Lemma `ib:lem:annular`, `annular_perturbation`), with `‖η‖₁ ≤ K r_l² q_l`.

* `outer_label_interaction` (Lemma `ib:out`): if `η` vanishes in `B_{c r_l}` and the target
  point satisfies `|x| ≤ C r_j ≤ c r_l / 2`, the normalized velocity is
  `r_j⁻¹ |K * η(x)| ≤ 8 C³ K / (15π c⁴) · (r_j / r_l)² q_l`.
* `inner_label_interaction` (Lemma `ib:in`): if `η` has zero mass, is supported in
  `B̄_{C r_l}`, and the target satisfies `|x| ≥ c r_j ≥ 2 C r_l`, then
  `r_j⁻¹ |K * η(x)| ≤ 8 C⁴ K / (15π c⁵) · (r_l / r_j)⁶ q_l`.

Only the values of the fields are treated (not their `c^{1,γ}` contour norms or source
derivatives), and only the planar Biot–Savart kernel.
-/

@[expose] public section

open MeasureTheory Complex

namespace Euler2D

/-- `∫ |y|⁴ |η| ≤ S⁴ ‖η‖₁` for `η` supported in `B̄_S`. -/
lemma fourth_le_mass {η : ℂ → ℝ} {S : ℝ} (hη : Integrable η)
    (hsupp : ∀ w, S < ‖w‖ → η w = 0) :
    ∫ w, ‖w‖ ^ 4 * |η w| ≤ S ^ 4 * ∫ w, |η w| := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_norm_pow_mul_of_supp hη hsupp 4) (hη.abs.const_mul _)
    fun w => ?_
  by_cases hw : η w = 0
  · simp [hw]
  have hwS : ‖w‖ ≤ S := not_lt.mp fun h => hw (hsupp w h)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hwS 4) (abs_nonneg _)

/-- **Lemma `ib:out`** (planar, value of the field). -/
theorem outer_label_interaction {η : ℂ → ℝ} {c C K q rl rj : ℝ} (hc : 0 < c) (hrl : 0 < rl)
    (hrj : 0 < rj) (hη : Integrable η) (hsym : ∀ w, η (I * w) = η w)
    (hzero : ∀ w, ‖w‖ < c * rl → η w = 0) (hL1 : ∫ w, |η w| ≤ K * rl ^ 2 * q)
    (hsep : C * rj ≤ c * rl / 2) {x : ℂ} (hx : ‖x‖ ≤ C * rj) :
    ‖velocityC η x‖ / rj ≤ 8 * C ^ 3 * K / (15 * Real.pi * c ^ 4) * (rj / rl) ^ 2 * q := by
  have hcrl : 0 < c * rl := mul_pos hc hrl
  have h := outer_perturbation_field hcrl hη hsym hzero (hx.trans hsep)
  have hA0 : 0 ≤ ∫ w, |η w| := integral_nonneg fun w => abs_nonneg _
  have hCr : 0 ≤ C * rj := (norm_nonneg _).trans hx
  have hx3 : ‖x‖ ^ 3 ≤ (C * rj) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hx 3
  have step : 8 / (15 * Real.pi) * ‖x‖ ^ 3 / (c * rl) ^ 4 * ∫ w, |η w| ≤
      8 / (15 * Real.pi) * (C * rj) ^ 3 / (c * rl) ^ 4 * (K * rl ^ 2 * q) := by
    refine mul_le_mul ?_ hL1 hA0 (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx3 (by positivity))
      (by positivity)
  refine (div_le_div_of_nonneg_right (h.trans step) hrj.le).trans (le_of_eq ?_)
  field_simp

/-- **Lemma `ib:in`** (planar, value of the field). -/
theorem inner_label_interaction {η : ℂ → ℝ} {c C K q rl rj : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hrl : 0 < rl) (hrj : 0 < rj) (hη : Integrable η) (hsym : ∀ w, η (I * w) = η w)
    (hmass : ∫ w, η w = 0) (hsupp : ∀ w, C * rl < ‖w‖ → η w = 0)
    (hL1 : ∫ w, |η w| ≤ K * rl ^ 2 * q) (hsep : C * rl ≤ c * rj / 2) {x : ℂ}
    (hx : c * rj ≤ ‖x‖) :
    ‖velocityC η x‖ / rj ≤ 8 * C ^ 4 * K / (15 * Real.pi * c ^ 5) * (rl / rj) ^ 6 * q := by
  have h := cluster_field_bound (S := C * rl) (mul_nonneg hC hrl.le) hrj hc hη hsupp hmass hsym
    hsep hx
  have hM4 := fourth_le_mass hη hsupp
  have hM4' : ∫ w, ‖w‖ ^ 4 * |η w| ≤ (C * rl) ^ 4 * (K * rl ^ 2 * q) :=
    hM4.trans (mul_le_mul_of_nonneg_left hL1 (by positivity))
  refine h.trans ((mul_le_mul_of_nonneg_left hM4' (by positivity)).trans (le_of_eq ?_))
  field_simp

end Euler2D
