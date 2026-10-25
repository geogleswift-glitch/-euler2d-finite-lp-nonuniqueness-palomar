module

public import Mathlib
public import RequestProject.Euler.TorusCancellation

/-!
# Far field of a zero-mass source (Lemma `bv:kernel`, estimate `bv:tail`)

For an integrable `f` supported in `B̄_R` with `∫ f = 0`,
`|K * f(x)| ≤ π⁻¹ |x|⁻² ∫ |y| |f(y)| dy` whenever `|x| ≥ 2R` (`velocity_tail_bound`).

The proof subtracts `K(x) ∫ f = 0` and uses
`K(x − y) − K(x) = (i/2π) \bar y / (\overline{(x − y)} \bar x)`.
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate

namespace Euler2D

/-- The planar kernel in complex form: `i z / (2π |z|²) = (i/2π) \bar z⁻¹` (both sides vanish at
`z = 0`). -/
lemma kernel_eq_inv_conj (z : ℂ) :
    I * z / (2 * Real.pi * ‖z‖ ^ 2) = I / (2 * Real.pi) * (conj z)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hc : conj z ≠ 0 := (map_ne_zero _).mpr hz
  have h2 : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast at h2
  rw [h2]
  field_simp

/-- `|K(x − y) − K(x)| ≤ |y| / (π |x|²)` for `|y| ≤ |x|/2`. -/
lemma kernel_diff_bound {x y : ℂ} (hx : x ≠ 0) (hy : 2 * ‖y‖ ≤ ‖x‖) :
    ‖I / (2 * Real.pi) * ((conj (x - y))⁻¹ - (conj x)⁻¹)‖ ≤ ‖y‖ / (Real.pi * ‖x‖ ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxy : ‖x‖ / 2 ≤ ‖x - y‖ := by
    have := norm_sub_norm_le x y
    linarith
  have hxy0 : x - y ≠ 0 := norm_pos_iff.mp (by linarith)
  have hc1 : conj (x - y) ≠ 0 := (map_ne_zero _).mpr hxy0
  have hc2 : conj x ≠ 0 := (map_ne_zero _).mpr hx
  rw [inv_sub_inv hc1 hc2, show conj x - conj (x - y) = conj y by rw [map_sub]; ring]
  have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]; norm_num
  rw [norm_mul, norm_div, norm_div, Complex.norm_I, h2, norm_mul, Complex.norm_conj,
    Complex.norm_conj, Complex.norm_conj]
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have hy0 := norm_nonneg y
  have : ‖x‖ * ‖x‖ ≤ 2 * (‖x - y‖ * ‖x‖) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hpi.le hy0)]

/-- **Estimate `bv:tail`.** -/
theorem velocity_tail_bound {f : ℂ → ℝ} {R : ℝ} (hR : 0 < R) (hf : Integrable f)
    (hsupp : ∀ y, R < ‖y‖ → f y = 0) (hmass : ∫ y, f y = 0) {x : ℂ} (hx : 2 * R ≤ ‖x‖) :
    ‖velocityC f x‖ ≤ (∫ y, ‖y‖ * |f y|) / (Real.pi * ‖x‖ ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxpos : 0 < ‖x‖ := by linarith
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
  set D : ℂ → ℂ := fun w => I / (2 * Real.pi) * ((conj (x - w))⁻¹ - (conj x)⁻¹) with hD
  have hDb : ∀ w, ‖(f w : ℂ) * D w‖ ≤ ‖w‖ * |f w| / (Real.pi * ‖x‖ ^ 2) := by
    intro w
    by_cases hw : f w = 0
    · simp [hw]
    have hwR : ‖w‖ ≤ R := not_lt.mp fun h => hw (hsupp w h)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := kernel_diff_bound hx0 (by linarith : 2 * ‖w‖ ≤ ‖x‖)
    calc |f w| * ‖D w‖ ≤ |f w| * (‖w‖ / (Real.pi * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = ‖w‖ * |f w| / (Real.pi * ‖x‖ ^ 2) := by ring
  have hI : Integrable (fun y => ‖y‖ * |f y|) := by
    simpa using integrable_norm_pow_mul_of_supp hf hsupp 1
  have hDm : Measurable D := by
    simp only [hD]
    fun_prop
  have hfD : Integrable (fun w => (f w : ℂ) * D w) := by
    refine Integrable.mono' (hI.div_const
      (Real.pi * ‖x‖ ^ 2)) ((Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1).mul
        hDm.aestronglyMeasurable) (Filter.Eventually.of_forall fun w => ?_)
    simpa using hDb w
  have hfc : Integrable (fun w => (f w : ℂ) * (I / (2 * Real.pi) * (conj x)⁻¹)) :=
    (hf.ofReal).mul_const _
  have hsplit : velocityC f x = ∫ w, ((f w : ℂ) * D w +
      (f w : ℂ) * (I / (2 * Real.pi) * (conj x)⁻¹)) := by
    unfold velocityC
    congr 1
    funext w
    rw [kernel_eq_inv_conj, hD]
    ring
  have hzero : ∫ w, (f w : ℂ) * (I / (2 * Real.pi) * (conj x)⁻¹) = 0 := by
    rw [integral_mul_const, integral_complex_ofReal, hmass]; simp
  rw [hsplit, integral_add hfD hfc, hzero, add_zero, ← integral_div]
  refine norm_integral_le_of_norm_le (hI.div_const _)
    (Filter.Eventually.of_forall fun w => ?_)
  simpa using hDb w

end Euler2D
