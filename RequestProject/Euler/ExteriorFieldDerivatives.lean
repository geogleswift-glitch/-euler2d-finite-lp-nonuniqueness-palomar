module

public import RequestProject.Euler.ClusterField

/-! Spatial derivatives of the actual exterior field. Complex
differentiation under the original Cauchy kernel integral gives
holomorphy; Cauchy's estimate transfers the genuine eighth-moment
remainder to every order of spatial differentiation. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex ComplexConjugate MeasureTheory Set Filter Topology Metric

namespace Euler2D

def planarCauchyTransform (w : ℂ → ℝ) (z : ℂ) : ℂ :=
  ∫ y, (w y : ℂ) * (z - y)⁻¹

theorem integrable_planarCauchyKernel {w : ℂ → ℝ} (hw : Integrable w)
    {z : ℂ} {d : ℝ} (hd : 0 < d) (hsep : ∀ y, w y ≠ 0 → d ≤ ‖z - y‖) :
    Integrable (fun y => (w y : ℂ) * (z - y)⁻¹) := by
  refine Integrable.mono' (hw.abs.div_const d)
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul
      ((measurable_const.sub measurable_id).inv.aestronglyMeasurable)) (ae_of_all _ (fun y => ?_))
  by_cases hy : w y = 0
  · simp [hy, hd.le]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hd (hsep y hy)

/-- The actual derivative is the integral of the differentiated original
kernel. No analytic continuation or derivative bound is an input. -/
theorem hasDerivAt_planarCauchyTransform {w : ℂ → ℝ} {S : ℝ}
    (hw : Integrable w) (hsupp : ∀ y, S < ‖y‖ → w y = 0)
    {z : ℂ} (hz : S < ‖z‖) :
    HasDerivAt (planarCauchyTransform w)
      (∫ y, -(w y : ℂ) * ((z - y) ^ 2)⁻¹) z := by
  let d := (‖z‖ - S) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hsep : ∀ x ∈ ball z d, ∀ y, w y ≠ 0 → d ≤ ‖x - y‖ := by
    intro x hx y hy
    have hyS : ‖y‖ ≤ S := not_lt.mp (fun h => hy (hsupp y h))
    have hdist : ‖x - z‖ < d := mem_ball_iff_norm.mp hx
    have hzx := norm_sub_norm_le z x
    rw [norm_sub_rev z x] at hzx
    have hxy := norm_sub_norm_le x y
    dsimp [d] at *
    linarith
  have hzB : z ∈ ball z d := mem_ball_self hd
  have hm (x : ℂ) : AEStronglyMeasurable (fun y => -(w y : ℂ) * ((x - y) ^ 2)⁻¹) :=
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).neg).mul
      (((measurable_const.sub measurable_id).pow_const 2).inv.aestronglyMeasurable)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x y => (w y : ℂ) * (x - y)⁻¹)
    (F' := fun x y => -(w y : ℂ) * ((x - y) ^ 2)⁻¹)
    (bound := fun y => |w y| / d ^ 2)
    (ball_mem_nhds z hd)
    (Eventually.of_forall (fun x =>
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul
        ((measurable_const.sub measurable_id).inv.aestronglyMeasurable)))
    (integrable_planarCauchyKernel hw hd (hsep z hzB))
    (hm z)
    (ae_of_all _ (fun y x hx => ?_))
    (hw.abs.div_const (d ^ 2))
    (ae_of_all _ (fun y x hx => ?_))).2
  · by_cases hy : w y = 0
    · simp [hy, hd.le]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_inv, norm_pow,
      ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      (pow_le_pow_left₀ hd.le (hsep x hx y hy) 2)
  · by_cases hy : w y = 0
    · simp only [hy, ofReal_zero, zero_mul, neg_zero]
      exact hasDerivAt_const x 0
    have hxy : x - y ≠ 0 := norm_pos_iff.mp (hd.trans_le (hsep x hx y hy))
    convert (((hasDerivAt_id x).sub_const y).inv hxy).const_mul (w y : ℂ) using 1 <;>
      (try funext s) <;>
      simp only [Pi.inv_apply, id_eq] <;> ring

def exteriorFourthRemainder (w : ℂ → ℝ) (z : ℂ) : ℂ :=
  velocityC w z - I / (2 * Real.pi) * momentN w 4 * (conj z ^ 5)⁻¹

def exteriorFourthRemainderCauchy (w : ℂ → ℝ) (z : ℂ) : ℂ :=
  conj (exteriorFourthRemainder w z)

theorem exteriorFourthRemainderCauchy_eq (w : ℂ → ℝ) (z : ℂ) :
    exteriorFourthRemainderCauchy w z =
      -(I / (2 * Real.pi)) * planarCauchyTransform w z -
        conj (I / (2 * Real.pi) * momentN w 4) * (z ^ 5)⁻¹ := by
  simp only [exteriorFourthRemainderCauchy, exteriorFourthRemainder,
    map_sub, map_mul, map_inv₀, map_pow, conj_conj, conj_velocityC, planarCauchyTransform]

theorem differentiableAt_exteriorFourthRemainderCauchy {w : ℂ → ℝ} {S : ℝ}
    (hw : Integrable w) (hsupp : ∀ y, S < ‖y‖ → w y = 0)
    {z : ℂ} (hz : S < ‖z‖) (hz0 : z ≠ 0) :
    DifferentiableAt ℂ (exteriorFourthRemainderCauchy w) z := by
  have he : exteriorFourthRemainderCauchy w = fun x =>
      -(I / (2 * Real.pi)) * planarCauchyTransform w x -
        conj (I / (2 * Real.pi) * momentN w 4) * (x ^ 5)⁻¹ :=
    funext (exteriorFourthRemainderCauchy_eq w)
  rw [he]
  exact ((hasDerivAt_planarCauchyTransform hw hsupp hz).differentiableAt.const_mul _).sub
    (((differentiableAt_id.pow 5).inv (pow_ne_zero 5 hz0)).const_mul _)

/-- Every exterior derivative has the correct scale. The eighth
absolute moment is that of the actual physical density. -/
theorem norm_iteratedDeriv_exteriorFourthRemainderCauchy
    {w : ℂ → ℝ} {S : ℝ} (hS : 0 ≤ S) (hw : Integrable w)
    (hsupp : ∀ y, S < ‖y‖ → w y = 0) (hmass : ∫ y, w y = 0)
    (hsym : ∀ y, w (I * y) = w y) {z : ℂ} (hz0 : z ≠ 0)
    (hz : 4 * S ≤ ‖z‖) (m : ℕ) :
    ‖iteratedDeriv m (exteriorFourthRemainderCauchy w) z‖ ≤
      (m.factorial : ℝ) * (8 / (15 * Real.pi) *
        (∫ y : ℂ, ‖y‖ ^ 8 * |w y|) / (‖z‖ / 2) ^ 9) / (‖z‖ / 2) ^ m := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hhalf : 0 < ‖z‖ / 2 := by positivity
  have hlower : ∀ x ∈ closedBall z (‖z‖ / 2), ‖z‖ / 2 ≤ ‖x‖ := by
    intro x hx
    have hh := mem_closedBall_iff_norm.mp hx
    have ht := norm_sub_norm_le z x
    rw [norm_sub_rev z x] at ht
    linarith
  have hdiff : DifferentiableOn ℂ (exteriorFourthRemainderCauchy w)
      (closedBall z (‖z‖ / 2)) := by
    intro x hx
    have hxnorm := hlower x hx
    exact (differentiableAt_exteriorFourthRemainderCauchy hw hsupp
      (by linarith) (norm_pos_iff.mp (hhalf.trans_le hxnorm))).differentiableWithinAt
  have hclosure : DifferentiableOn ℂ (exteriorFourthRemainderCauchy w)
      (closure (ball z (‖z‖ / 2))) := by
    simpa only [closure_ball z hhalf.ne'] using hdiff
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hhalf
    hclosure.diffContOnCl
  intro x hx
  have hxnorm := hlower x (sphere_subset_closedBall hx)
  have hxp : 0 < ‖x‖ := hhalf.trans_le hxnorm
  have hb := exterior_multipole_remainder hw hsupp hmass hsym
    (norm_pos_iff.mp hxp) (show 2 * S ≤ ‖x‖ by linarith)
  change ‖conj (exteriorFourthRemainder w x)‖ ≤ _
  rw [norm_conj]
  exact hb.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hhalf.le hxnorm 9))

theorem norm_fderiv_exteriorFourthRemainder_le {w : ℂ → ℝ} {S : ℝ}
    (hw : Integrable w) (hsupp : ∀ y, S < ‖y‖ → w y = 0)
    {z : ℂ} (hz : S < ‖z‖) (hz0 : z ≠ 0) :
    ‖fderiv ℝ (exteriorFourthRemainder w) z‖ ≤
      ‖deriv (exteriorFourthRemainderCauchy w) z‖ := by
  have hd := (differentiableAt_exteriorFourthRemainderCauchy hw hsupp hz hz0).hasDerivAt
  have hdR := Complex.conjCLE.hasFDerivAt.comp z (hd.hasFDerivAt.restrictScalars ℝ)
  have he : (fun x => Complex.conjCLE (exteriorFourthRemainderCauchy w x)) =
      exteriorFourthRemainder w := by
    funext x
    exact conj_conj _
  change HasFDerivAt (fun x => Complex.conjCLE (exteriorFourthRemainderCauchy w x)) _ z at hdR
  rw [he] at hdR
  rw [hdR.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (by
    rw [Complex.conjCLE_norm, ContinuousLinearMap.norm_restrictScalars, one_mul]
    simp only [ContinuousLinearMap.norm_toSpanSingleton])

theorem differentiableAt_exteriorFourthRemainder {w : ℂ → ℝ} {S : ℝ}
    (hw : Integrable w) (hsupp : ∀ y, S < ‖y‖ → w y = 0)
    {z : ℂ} (hz : S < ‖z‖) (hz0 : z ≠ 0) :
    DifferentiableAt ℝ (exteriorFourthRemainder w) z := by
  have hd := (differentiableAt_exteriorFourthRemainderCauchy hw hsupp hz hz0).restrictScalars ℝ
  have he : (fun x => Complex.conjCLE (exteriorFourthRemainderCauchy w x)) =
      exteriorFourthRemainder w := by
    funext x
    exact conj_conj _
  rw [← he]
  exact Complex.conjCLE.differentiableAt.comp z hd

/-- The first derivative bound is for the original real spatial
velocity, rather than for a formal holomorphic surrogate. -/
theorem norm_fderiv_exteriorFourthRemainder {w : ℂ → ℝ} {S : ℝ}
    (hS : 0 ≤ S) (hw : Integrable w) (hsupp : ∀ y, S < ‖y‖ → w y = 0)
    (hmass : ∫ y, w y = 0) (hsym : ∀ y, w (I * y) = w y)
    {z : ℂ} (hz0 : z ≠ 0) (hz : 4 * S ≤ ‖z‖) :
    ‖fderiv ℝ (exteriorFourthRemainder w) z‖ ≤
      (8 / (15 * Real.pi) * (∫ y : ℂ, ‖y‖ ^ 8 * |w y|) /
        (‖z‖ / 2) ^ 9) / (‖z‖ / 2) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  refine (norm_fderiv_exteriorFourthRemainder_le hw hsupp (by linarith) hz0).trans ?_
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
    using norm_iteratedDeriv_exteriorFourthRemainderCauchy hS hw hsupp hmass hsym hz0 hz 1

end Euler2D

end
