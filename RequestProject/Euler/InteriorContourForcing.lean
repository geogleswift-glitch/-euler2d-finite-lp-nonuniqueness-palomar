module

public import RequestProject.Euler.CircularPhysicalContourLittle

/-! Genuine derivatives and original little-contour norms of the
interior velocity of a fourfold annular perturbation.  Differentiability
is obtained under the real kernel integral; no differentiability of the
source density is required. -/

@[expose] public section

set_option maxHeartbeats 2600000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem hasDerivAt_planarCauchyTransform_interior {w : ℂ → ℝ} {a : ℝ}
    (hw : Integrable w) (hzero : ∀ y, ‖y‖ < a → w y = 0)
    {z : ℂ} (hz : ‖z‖ < a) :
    HasDerivAt (planarCauchyTransform w)
      (∫ y, -(w y : ℂ) * ((z - y) ^ 2)⁻¹) z := by
  let d := (a - ‖z‖) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hsep : ∀ x ∈ ball z d, ∀ y, w y ≠ 0 → d ≤ ‖x - y‖ := by
    intro x hx y hy
    have hay : a ≤ ‖y‖ := not_lt.mp (fun h => hy (hzero y h))
    have hdist : ‖x - z‖ < d := mem_ball_iff_norm.mp hx
    have hzx := norm_sub_norm_le x z
    have hxy := norm_sub_norm_le y x
    rw [norm_sub_rev y x] at hxy
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
      simp only [id_eq] <;> try ring
    funext u
    simp only [Pi.inv_apply, sub_eq_add_neg, add_comm]

theorem analyticOnNhd_conj_velocityC_interior {w : ℂ → ℝ} {a : ℝ}
    (hw : Integrable w) (hzero : ∀ y, ‖y‖ < a → w y = 0) :
    AnalyticOnNhd ℂ (fun z => conj (velocityC w z)) {z | ‖z‖ < a} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_norm continuous_const)
  intro z hz
  have hh := (hasDerivAt_planarCauchyTransform_interior hw hzero hz).const_mul (-(I / (2 * Real.pi)))
  have he : (fun x => -(I / (2 * Real.pi)) * planarCauchyTransform w x) =
      (fun x => conj (velocityC w x)) := by
    funext x
    exact (conj_velocityC w x).symm
  rw [he] at hh
  exact hh.differentiableAt.differentiableWithinAt

def interiorSpatialDerivativeBudget (M a r : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * (8 / (15 * Real.pi) * (2 * r) ^ 3 / a ^ 4 * M) / r ^ m

def interiorContourNormBudget (γ M a r L : ℝ) : ℝ :=
  max (interiorSpatialDerivativeBudget M a r 0)
    (2 * (interiorSpatialDerivativeBudget M a r 1 + Real.pi ^ (1 - γ) *
      interiorSpatialDerivativeBudget M a r 2 * L) * L)

theorem interiorSpatialDerivativeBudget_nonneg {M a r : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (m : ℕ) :
    0 ≤ interiorSpatialDerivativeBudget M a r m := by
  unfold interiorSpatialDerivativeBudget
  positivity

theorem norm_iteratedDeriv_conj_velocityC_interior {w : ℂ → ℝ} {a r M : ℝ}
    (hw : Integrable w) (hy : ∀ y, w (I * y) = w y)
    (hzero : ∀ y, ‖y‖ < a → w y = 0) (hM : ∫ y, |w y| ≤ M)
    (ha : 0 < a) (hr : 0 < r) (hsep : 4 * r ≤ a)
    {z : ℂ} (hz : ‖z‖ ≤ r) (m : ℕ) :
    ‖iteratedDeriv m (fun x => conj (velocityC w x)) z‖ ≤
      interiorSpatialDerivativeBudget M a r m := by
  have hMn : 0 ≤ M := (integral_nonneg (fun y => abs_nonneg _)).trans hM
  have hupper : ∀ x ∈ closedBall z r, ‖x‖ ≤ 2 * r := by
    intro x hx
    have hh := mem_closedBall_iff_norm.mp hx
    have ht := norm_sub_norm_le x z
    linarith
  have hF := analyticOnNhd_conj_velocityC_interior hw hzero
  have hdiff : DifferentiableOn ℂ (fun x => conj (velocityC w x)) (closure (ball z r)) := by
    rw [closure_ball z hr.ne']
    intro x hx
    have hxnorm := hupper x hx
    exact (hF x (by change ‖x‖ < a; linarith)).differentiableAt.differentiableWithinAt
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hr hdiff.diffContOnCl
  intro x hx
  have hxnorm := hupper x (sphere_subset_closedBall hx)
  rw [norm_conj]
  have hp := outer_perturbation_field ha hw hy hzero (show ‖x‖ ≤ a / 2 by linarith)
  exact hp.trans (mul_le_mul
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxnorm 3) (by positivity))
      (by positivity)) hM (integral_nonneg (fun y => abs_nonneg _)) (by positivity))

theorem interiorContourNormBudget_mono_length {γ M a r L K : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hL : 0 ≤ L) (hLK : L ≤ K) :
    interiorContourNormBudget γ M a r L ≤ interiorContourNormBudget γ M a r K := by
  have h₁ := interiorSpatialDerivativeBudget_nonneg (a := a) hM hr 1
  have h₂ := interiorSpatialDerivativeBudget_nonneg (a := a) hM hr 2
  have hK : 0 ≤ K := hL.trans hLK
  unfold interiorContourNormBudget
  apply max_le_max le_rfl
  gcongr <;> positivity

theorem interiorContourNormBudget_physical_scale {γ M a r rl rj : ℝ}
    (hM : 0 ≤ M) (hRl : 0 < rl) (hRj : 0 < rj) (ha : 0 < a) (hr : 0 < r) (L : ℝ) :
    interiorContourNormBudget γ M (a * rl) (r * rj) (rj * L) =
      (M * rj ^ 3 / rl ^ 4) * interiorContourNormBudget γ 1 a r L := by
  have hfac : 0 ≤ M * rj ^ 3 / rl ^ 4 := by positivity
  unfold interiorContourNormBudget
  rw [mul_max_of_nonneg _ _ hfac]
  apply congrArg₂ max
  · unfold interiorSpatialDerivativeBudget
    norm_num only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, div_one, mul_pow, div_pow]
    field_simp [hRl.ne', hRj.ne', ha.ne', hr.ne']
    <;> ring
  · unfold interiorSpatialDerivativeBudget
    norm_num only [Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
      pow_one, one_mul, mul_pow, div_pow]
    field_simp [hRl.ne', hRj.ne', ha.ne', hr.ne']
    <;> ring

/-- A genuine fourfold source outside a core produces an original
Little contour field, with cubic target-radius cancellation. -/
theorem exists_interiorContourFieldLittle {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {w : ℂ → ℝ} {a r M : ℝ} (hw : Integrable w)
    (hy : ∀ y, w (I * y) = w y) (hzero : ∀ y, ‖y‖ < a → w y = 0)
    (hM : ∫ y, |w y| ≤ M) (ha : 0 < a) (hr : 0 < r) (hsep : 8 * r ≤ a)
    (Z : LittleContourSpace γ) (hZ : ∀ x, ‖ContourC1Space.toBCF γ Z.val x‖ ≤ r) :
    ∃ Q : LittleContourSpace γ,
      (∀ θ, LittleContourSpace.lift γ Q θ = velocityC w (LittleContourSpace.lift γ Z θ)) ∧
      ‖Q‖ ≤ interiorContourNormBudget (γ : ℝ) M a r ‖Z‖ := by
  let U : Set ℂ := {z | ‖z‖ < a}
  have hU : IsOpen U := isOpen_lt continuous_norm continuous_const
  have hF := analyticOnNhd_conj_velocityC_interior hw hzero
  have hZu : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U := by
    intro x
    have hx := hZ x
    change ‖ContourC1Space.toBCF γ Z.val x‖ < a
    linarith
  have hMn : 0 ≤ M := (integral_nonneg (fun y => abs_nonneg _)).trans hM
  have hB (m : ℕ) := interiorSpatialDerivativeBudget_nonneg (a := a) hMn hr m
  have hder (m : ℕ) (x : ContourCircle) := norm_iteratedDeriv_conj_velocityC_interior
    hw hy hzero hM ha hr (by linarith) (hZ x) m
  have h₀ : ∀ x, ‖conj (velocityC w (ContourC1Space.toBCF γ Z.val x))‖ ≤
      interiorSpatialDerivativeBudget M a r 0 := by
    simpa only [iteratedDeriv_zero] using hder 0
  have h₁ : ∀ x, ‖deriv (fun z => conj (velocityC w z)) (ContourC1Space.toBCF γ Z.val x)‖ ≤
      interiorSpatialDerivativeBudget M a r 1 := by
    simpa only [iteratedDeriv_one] using hder 1
  have h₂ : ∀ x, ‖deriv (deriv (fun z => conj (velocityC w z))) (ContourC1Space.toBCF γ Z.val x)‖ ≤
      interiorSpatialDerivativeBudget M a r 2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hder 2
  let Q := contourC1Conjugate (analyticContourComposition hγ1 hF Z.val hZu (hB 2) h₂)
  have hQ : ∀ θ, ContourC1Space.lift γ Q θ = velocityC w (LittleContourSpace.lift γ Z θ) := by
    intro θ
    rw [show ContourC1Space.lift γ Q θ =
      conj (conj (velocityC w (LittleContourSpace.lift γ Z θ))) from rfl]
    exact conj_conj _
  have hn : ‖Q‖ ≤ interiorContourNormBudget (γ : ℝ) M a r ‖Z‖ :=
    (norm_contourC1Conjugate_le _).trans
      (norm_analyticContourComposition_le hγ1 hF Z.val hZu (hB 0) (hB 1) (hB 2) h₀ h₁ h₂)
  let V : Set ℂ := {z | ‖z‖ < 2 * r}
  have hV : IsOpen V := isOpen_lt continuous_norm continuous_const
  have hVF : AnalyticOnNhd ℂ (fun z => conj (velocityC w z)) V :=
    hF.mono (fun x hx => by change ‖x‖ < 2 * r at hx; change ‖x‖ < a; linarith)
  have hZv : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ V := by
    intro x
    have hx := hZ x
    change ‖ContourC1Space.toBCF γ Z.val x‖ < 2 * r
    linarith
  have hVB (m : ℕ) := interiorSpatialDerivativeBudget_nonneg (a := a) (r := 2 * r)
    hMn (mul_pos (by norm_num) hr) m
  have hvb (m : ℕ) : ∀ z ∈ V,
      ‖iteratedDeriv m (fun x => conj (velocityC w x)) z‖ ≤
        interiorSpatialDerivativeBudget M a (2 * r) m := by
    intro z hz
    exact norm_iteratedDeriv_conj_velocityC_interior hw hy hzero hM ha
      (mul_pos (by norm_num) hr) (by linarith) (le_of_lt hz) m
  have hmem : Q ∈ (LittleContourSpace γ : Set (ContourC1Space γ)) := by
    apply contour_conjugate_analytic_composition_mem_little hγ1 hV hVF Z hZv
      (hVB 1) (hVB 2) (hVB 3)
      (by simpa only [iteratedDeriv_one] using hvb 1)
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hvb 2)
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hvb 3) Q
    intro θ
    rw [hQ θ]
    exact (conj_conj _).symm
  exact ⟨⟨Q, hmem⟩, hQ, hn⟩

/-- Original Little-space version of the outer-label interaction:
the actual field has the squared ratio of target to source scales. -/
theorem exists_outerLabelContourFieldLittle_ratio {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {w : ℂ → ℝ} {c B K q rl rj L : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hrl : 0 < rl) (hrj : 0 < rj) (hw : Integrable w)
    (hy : ∀ y, w (I * y) = w y) (hzero : ∀ y, ‖y‖ < c * rl → w y = 0)
    (hM : ∫ y, |w y| ≤ K * rl ^ 2 * q) (hsep : 8 * (B * rj) ≤ c * rl)
    (Z : LittleContourSpace γ) (hZ : ∀ x, ‖ContourC1Space.toBCF γ Z.val x‖ ≤ B * rj)
    (hL : ‖Z‖ ≤ rj * L) :
    ∃ Q : LittleContourSpace γ,
      (∀ θ, LittleContourSpace.lift γ Q θ = velocityC w (LittleContourSpace.lift γ Z θ)) ∧
      ‖Q‖ / rj ≤ interiorContourNormBudget (γ : ℝ) 1 c B L * K * (rj / rl) ^ 2 * q := by
  obtain ⟨Q, hQ, hn⟩ := exists_interiorContourFieldLittle hγ1 hw hy hzero hM
    (mul_pos hc hrl) (mul_pos hB hrj) hsep Z hZ
  have hMn : 0 ≤ K * rl ^ 2 * q := (integral_nonneg (fun y => abs_nonneg _)).trans hM
  have hn' := hn.trans (interiorContourNormBudget_mono_length hMn (mul_pos hB hrj)
    (norm_nonneg Z) hL)
  rw [interiorContourNormBudget_physical_scale hMn hrl hrj hc hB L] at hn'
  refine ⟨Q, hQ, (div_le_div_of_nonneg_right hn' hrj.le).trans_eq ?_⟩
  field_simp [hrl.ne', hrj.ne']
  <;> ring

end Euler2D

end
