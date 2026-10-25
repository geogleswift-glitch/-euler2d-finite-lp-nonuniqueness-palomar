module

public import Mathlib
public import RequestProject.Euler.TorusCancellation

/-!
# The complete inner-cluster field (Lemma `ib:lem:cluster`, planar `C⁰` part)

Let `ζ` be an integrable, fourfold-symmetric, zero-mass density supported in `B̄_S`, and put
`M₄^{abs} = ∫ |y|⁴ |ζ(y)| dy`. For a target point with `|z| ≥ c r` and `S ≤ c r / 2`:

* `cluster_field_bound`: `r⁻¹ |K * ζ(z)| ≤ 8/(15π c⁵) · r⁻⁶ M₄^{abs}`;
* `cluster_remainder_bound`: after subtracting the leading fourth-moment term
  `(i/2π) N₄ \bar z⁻⁵`, `r⁻¹ |remainder| ≤ 8/(15π c⁹) · r⁻¹⁰ ∫ |y|⁸ |ζ|
  ≤ 8/(15π c⁹) · r⁻¹⁰ S⁴ M₄^{abs}`.

Only the value of the field (the `C⁰` norm) is treated; the bounds on rescaled derivatives
(`C^m`, `m ≥ 1`) are not formalized, and densities are functions rather than measures.
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate

namespace Euler2D

/-- `|N₄| ≤ M₄^{abs}`. -/
lemma norm_momentN_le_abs (ζ : ℂ → ℝ) (m : ℕ) : ‖momentN ζ m‖ ≤ ∫ w, ‖w‖ ^ m * |ζ w| := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Filter.Eventually.of_forall fun w => ?_)))
  simp [norm_pow, mul_comm]

/-- `∫ |y|⁸ |ζ| ≤ S⁴ ∫ |y|⁴ |ζ|` for `ζ` supported in `B̄_S`. -/
lemma eighth_le_fourth {ζ : ℂ → ℝ} {S : ℝ} (hζ : Integrable ζ)
    (hsupp : ∀ w, S < ‖w‖ → ζ w = 0) :
    ∫ w, ‖w‖ ^ 8 * |ζ w| ≤ S ^ 4 * ∫ w, ‖w‖ ^ 4 * |ζ w| := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_norm_pow_mul_of_supp hζ hsupp 8)
    ((integrable_norm_pow_mul_of_supp hζ hsupp 4).const_mul _) fun w => ?_
  by_cases hw : ζ w = 0
  · simp [hw]
  have hwS : ‖w‖ ≤ S := not_lt.mp fun h => hw (hsupp w h)
  have h4 : ‖w‖ ^ 4 ≤ S ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hwS 4
  calc ‖w‖ ^ 8 * |ζ w| = ‖w‖ ^ 4 * (‖w‖ ^ 4 * |ζ w|) := by ring
    _ ≤ S ^ 4 * (‖w‖ ^ 4 * |ζ w|) := by gcongr

/-- Exterior field of a fourfold-symmetric zero-mass cluster:
`|K * ζ(z)| ≤ 8/(15π) |z|⁻⁵ M₄^{abs}` for `2S ≤ |z|`. -/
lemma cluster_field_pointwise {ζ : ℂ → ℝ} {S : ℝ} (hS : 0 ≤ S) (hζ : Integrable ζ)
    (hsupp : ∀ w, S < ‖w‖ → ζ w = 0) (hmass : ∫ w, ζ w = 0) (hsym : ∀ w, ζ (I * w) = ζ w)
    {z : ℂ} (hz0 : z ≠ 0) (hz : 2 * S ≤ ‖z‖) :
    ‖velocityC ζ z‖ ≤ 8 / (15 * Real.pi) * (∫ w, ‖w‖ ^ 4 * |ζ w|) / ‖z‖ ^ 5 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set M4 := ∫ w, ‖w‖ ^ 4 * |ζ w| with hM4
  have hM40 : 0 ≤ M4 := integral_nonneg fun w => by positivity
  set L := I / (2 * Real.pi) * momentN ζ 4 * (conj z ^ 5)⁻¹ with hL
  have hLn : ‖L‖ ≤ M4 / (2 * Real.pi * ‖z‖ ^ 5) := by
    have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]; norm_num
    rw [hL, norm_mul, norm_mul, norm_div, Complex.norm_I, h2, norm_inv, norm_pow,
      Complex.norm_conj]
    have := norm_momentN_le_abs ζ 4
    have he : ‖momentN ζ 4‖ * (‖z‖ ^ 5)⁻¹ / (2 * Real.pi) =
        ‖momentN ζ 4‖ / (2 * Real.pi * ‖z‖ ^ 5) := by
      field_simp
    simp only [one_div] at *
    rw [show (2 * Real.pi)⁻¹ * ‖momentN ζ 4‖ * (‖z‖ ^ 5)⁻¹ =
      ‖momentN ζ 4‖ * (‖z‖ ^ 5)⁻¹ / (2 * Real.pi) by ring, he]
    gcongr
  have hrem := exterior_multipole_remainder hζ hsupp hmass hsym hz0 hz
  have h8 := eighth_le_fourth hζ hsupp
  have hS4 : S ^ 4 ≤ ‖z‖ ^ 4 / 16 := by
    have : S ≤ ‖z‖ / 2 := by linarith
    calc S ^ 4 ≤ (‖z‖ / 2) ^ 4 := pow_le_pow_left₀ hS this 4
      _ = ‖z‖ ^ 4 / 16 := by ring
  have hremb : 8 / (15 * Real.pi) * (∫ w, ‖w‖ ^ 8 * |ζ w|) / ‖z‖ ^ 9 ≤
      8 / (15 * Real.pi) * (‖z‖ ^ 4 / 16 * M4) / ‖z‖ ^ 9 := by
    gcongr
    exact h8.trans (mul_le_mul_of_nonneg_right hS4 hM40)
  calc ‖velocityC ζ z‖ = ‖(velocityC ζ z - L) + L‖ := by rw [sub_add_cancel]
    _ ≤ ‖velocityC ζ z - L‖ + ‖L‖ := norm_add_le _ _
    _ ≤ 8 / (15 * Real.pi) * (‖z‖ ^ 4 / 16 * M4) / ‖z‖ ^ 9 + M4 / (2 * Real.pi * ‖z‖ ^ 5) :=
        add_le_add (hrem.trans hremb) hLn
    _ = 8 / (15 * Real.pi) * M4 / ‖z‖ ^ 5 := by
        field_simp
        ring

/-- **Lemma `ib:lem:cluster`** (normalized field on the target annulus). -/
theorem cluster_field_bound {ζ : ℂ → ℝ} {S r c : ℝ} (hS : 0 ≤ S) (hr : 0 < r) (hc : 0 < c)
    (hζ : Integrable ζ) (hsupp : ∀ w, S < ‖w‖ → ζ w = 0) (hmass : ∫ w, ζ w = 0)
    (hsym : ∀ w, ζ (I * w) = ζ w) (hSc : S ≤ c * r / 2) {z : ℂ} (hz : c * r ≤ ‖z‖) :
    ‖velocityC ζ z‖ / r ≤ 8 / (15 * Real.pi * c ^ 5) * r⁻¹ ^ 6 * ∫ w, ‖w‖ ^ 4 * |ζ w| := by
  have hcr : 0 < c * r := mul_pos hc hr
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hcr.trans_le hz)
  have hM40 : 0 ≤ ∫ w, ‖w‖ ^ 4 * |ζ w| := integral_nonneg fun w => by positivity
  have h := cluster_field_pointwise hS hζ hsupp hmass hsym hz0 (by linarith)
  have hz5 : (c * r) ^ 5 ≤ ‖z‖ ^ 5 := pow_le_pow_left₀ hcr.le hz 5
  calc ‖velocityC ζ z‖ / r ≤ 8 / (15 * Real.pi) * (∫ w, ‖w‖ ^ 4 * |ζ w|) / ‖z‖ ^ 5 / r := by
        gcongr
    _ ≤ 8 / (15 * Real.pi) * (∫ w, ‖w‖ ^ 4 * |ζ w|) / (c * r) ^ 5 / r := by
        gcongr
    _ = 8 / (15 * Real.pi * c ^ 5) * r⁻¹ ^ 6 * ∫ w, ‖w‖ ^ 4 * |ζ w| := by
        field_simp

/-- **Lemma `ib:lem:cluster`** (normalized remainder after the fourth-moment term). -/
theorem cluster_remainder_bound {ζ : ℂ → ℝ} {S r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hζ : Integrable ζ) (hsupp : ∀ w, S < ‖w‖ → ζ w = 0) (hmass : ∫ w, ζ w = 0)
    (hsym : ∀ w, ζ (I * w) = ζ w) (hSc : S ≤ c * r / 2) {z : ℂ} (hz : c * r ≤ ‖z‖) :
    ‖velocityC ζ z - I / (2 * Real.pi) * momentN ζ 4 * (conj z ^ 5)⁻¹‖ / r ≤
        8 / (15 * Real.pi * c ^ 9) * r⁻¹ ^ 10 * ∫ w, ‖w‖ ^ 8 * |ζ w| ∧
      8 / (15 * Real.pi * c ^ 9) * r⁻¹ ^ 10 * ∫ w, ‖w‖ ^ 8 * |ζ w| ≤
        8 / (15 * Real.pi * c ^ 9) * r⁻¹ ^ 10 * S ^ 4 * ∫ w, ‖w‖ ^ 4 * |ζ w| := by
  have hcr : 0 < c * r := mul_pos hc hr
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hcr.trans_le hz)
  have hE0 : 0 ≤ ∫ w, ‖w‖ ^ 8 * |ζ w| := integral_nonneg fun w => by positivity
  have h := exterior_multipole_remainder hζ hsupp hmass hsym hz0 (by linarith)
  have hz9 : (c * r) ^ 9 ≤ ‖z‖ ^ 9 := pow_le_pow_left₀ hcr.le hz 9
  refine ⟨?_, ?_⟩
  · have h' := div_le_div_of_nonneg_right h hr.le
    refine h'.trans ?_
    have hK : 0 ≤ 8 / (15 * Real.pi) * ∫ w, ‖w‖ ^ 8 * |ζ w| := mul_nonneg (by positivity) hE0
    have h2 := div_le_div_of_nonneg_left hK (by positivity) hz9
    refine (div_le_div_of_nonneg_right h2 hr.le).trans (le_of_eq ?_)
    rw [inv_pow, mul_pow]
    field_simp
  · rw [mul_assoc _ (S ^ 4)]
    exact mul_le_mul_of_nonneg_left (eighth_le_fourth hζ hsupp) (by positivity)

end Euler2D
