module

public import RequestProject.Euler.FourierRegularization
public import RequestProject.Euler.LimitPassage
public import RequestProject.Euler.CellCurl
public import RequestProject.Euler.CurlLimit

/-!
# The actual zero-mean inverse curl on the physical torus

The velocity is constructed by the bounded Fourier symbols
`i k₁ / |k|²` and `-i k₀ / |k|²`.  Both symbols vanish at zero.  All
fields are transferred back through the actual box--quotient isometry.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace BiotSavartConstruction

abbrev CoeffL2 := lp (fun _ : Fin 2 → ℤ => ℂ) 2

lemma sum_norm_coeff_le (a : CoeffL2) (s : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ s, ‖a k‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have h := (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a).summable
  have hs := h.sum_le_tsum s (fun k _ => by positivity)
  have heq : (∑' k, ‖a k‖ ^ 2) = ‖a‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a).tsum_eq
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, heq] using hs

def multiplierSeq (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1)
    (a : CoeffL2) : CoeffL2 :=
  ⟨fun k => m k * a k, memℓp_gen' (C := ‖a‖ ^ 2) fun s => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply le_trans _ (sum_norm_coeff_le a s)
    apply Finset.sum_le_sum
    intro k hk
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [norm_mul, one_mul] using
      mul_le_mul_of_nonneg_right (hm k) (norm_nonneg (a k))⟩

lemma multiplierSeq_norm_le (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1)
    (a : CoeffL2) : ‖multiplierSeq m hm a‖ ≤ ‖a‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg a)
  intro s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply le_trans _ (sum_norm_coeff_le a s)
  apply Finset.sum_le_sum
  intro k hk
  change ‖m k * a k‖ ^ 2 ≤ ‖a k‖ ^ 2
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa only [norm_mul, one_mul] using
    mul_le_mul_of_nonneg_right (hm k) (norm_nonneg (a k))

def multiplier (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1) :
    CoeffL2 →L[ℂ] CoeffL2 :=
  LinearMap.mkContinuous
    { toFun := multiplierSeq m hm
      map_add' := by
        intro a b
        ext k
        change m k * (a k + b k) = m k * a k + m k * b k
        exact mul_add _ _ _
      map_smul' := by intro c a; ext k; simp [multiplierSeq, mul_left_comm] }
    1 (by
      intro a
      change ‖multiplierSeq m hm a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using multiplierSeq_norm_le m hm a)

lemma multiplier_apply (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1)
    (a : CoeffL2) (k : Fin 2 → ℤ) : multiplier m hm a k = m k * a k := rfl

def fourierMultiplier (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1) :
    FourierL2 →L[ℂ] FourierL2 :=
  UnitAddTorus.mFourierBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((multiplier m hm).comp
      UnitAddTorus.mFourierBasis.repr.toLinearIsometry.toContinuousLinearMap)

lemma fourierMultiplier_coeff (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1)
    (f : FourierL2) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fourierMultiplier m hm f) k =
      m k * UnitAddTorus.mFourierCoeff f k := by
  simp only [← UnitAddTorus.mFourierBasis_repr]
  change UnitAddTorus.mFourierBasis.repr
    (UnitAddTorus.mFourierBasis.repr.symm
      (multiplier m hm (UnitAddTorus.mFourierBasis.repr f))) k = _
  rw [UnitAddTorus.mFourierBasis.repr.apply_symm_apply]
  rfl

lemma fourierMultiplier_norm_le (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1)
    (f : FourierL2) : ‖fourierMultiplier m hm f‖ ≤ ‖f‖ := by
  change ‖UnitAddTorus.mFourierBasis.repr.symm
    (multiplier m hm (UnitAddTorus.mFourierBasis.repr f))‖ ≤ _
  rw [UnitAddTorus.mFourierBasis.repr.symm.norm_map]
  exact (multiplierSeq_norm_le m hm _).trans_eq
    (UnitAddTorus.mFourierBasis.repr.norm_map f)

def boxMultiplier (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1) :
    BoxFourierL2 →L[ℂ] BoxFourierL2 :=
  torusL2Equiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((fourierMultiplier m hm).comp torusL2Equiv.toLinearIsometry.toContinuousLinearMap)

lemma boxMultiplier_coeff (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1)
    (f : BoxFourierL2) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusL2Equiv (boxMultiplier m hm f)) k =
      m k * UnitAddTorus.mFourierCoeff (torusL2Equiv f) k := by
  change UnitAddTorus.mFourierCoeff (torusL2Equiv (torusL2Equiv.symm _)) k = _
  rw [torusL2Equiv.apply_symm_apply]
  exact fourierMultiplier_coeff m hm _ k

lemma boxMultiplier_norm_le (m : (Fin 2 → ℤ) → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1)
    (f : BoxFourierL2) : ‖boxMultiplier m hm f‖ ≤ ‖f‖ := by
  change ‖torusL2Equiv.symm (fourierMultiplier m hm (torusL2Equiv f))‖ ≤ _
  rw [torusL2Equiv.symm.norm_map]
  exact (fourierMultiplier_norm_le m hm _).trans_eq (torusL2Equiv.norm_map f)

lemma abs_intCast_le_square (n : ℤ) : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
  have hi : |n| ≤ n ^ 2 := by
    simpa only [Int.natCast_natAbs] using Int.natAbs_le_self_sq n
  exact_mod_cast hi

lemma abs_frequency_le (k : Fin 2 → ℤ) (i : Fin 2) :
    |(k i : ℝ)| ≤ frequencySq k := by
  have h := abs_intCast_le_square (k i)
  fin_cases i
  · change |(k 0 : ℝ)| ≤ (k 0 : ℝ) ^ 2 at h
    exact h.trans (le_add_of_nonneg_right (sq_nonneg (k 1 : ℝ)))
  · change |(k 1 : ℝ)| ≤ (k 1 : ℝ) ^ 2 at h
    exact h.trans (le_add_of_nonneg_left (sq_nonneg (k 0 : ℝ)))

/-- The physical inverse curl symbol, including its zero frequency. -/
def symbol (j : Fin 2) (k : Fin 2 → ℤ) : ℂ :=
  Complex.I * (if j = 0 then (k 1 : ℂ) else -(k 0 : ℂ)) / (frequencySq k : ℂ)

lemma symbol_norm_le (j : Fin 2) (k : Fin 2 → ℤ) : ‖symbol j k‖ ≤ 1 := by
  by_cases hz : frequencySq k = 0
  · simp [symbol, hz]
  have hp : 0 < frequencySq k := lt_of_le_of_ne (frequencySq_nonneg k) (Ne.symm hz)
  fin_cases j
  · change ‖Complex.I * (k 1 : ℂ) / (frequencySq k : ℂ)‖ ≤ 1
    simpa only [norm_div, norm_mul, Complex.norm_I, one_mul, ← Complex.ofReal_intCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (frequencySq_nonneg k)] using
      (div_le_one hp).mpr (abs_frequency_le k 1)
  · change ‖Complex.I * -(k 0 : ℂ) / (frequencySq k : ℂ)‖ ≤ 1
    simpa only [norm_div, norm_mul, Complex.norm_I, one_mul, norm_neg, ← Complex.ofReal_intCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (frequencySq_nonneg k)] using
      (div_le_one hp).mpr (abs_frequency_le k 0)

@[simp] lemma symbol_zero (j : Fin 2) : symbol j 0 = 0 := by
  simp [symbol, frequencySq]

lemma frequencySq_eq_zero_iff (k : Fin 2 → ℤ) : frequencySq k = 0 ↔ k = 0 := by
  constructor
  · intro h
    have h₀ : (k 0 : ℝ) = 0 := by
      unfold frequencySq at h
      nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]
    have h₁ : (k 1 : ℝ) = 0 := by
      unfold frequencySq at h
      nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]
    ext i
    fin_cases i
    · exact_mod_cast h₀
    · exact_mod_cast h₁
  · rintro rfl
    simp [frequencySq]

lemma symbol_div (k : Fin 2 → ℤ) :
    (k 0 : ℂ) * symbol 0 k + (k 1 : ℂ) * symbol 1 k = 0 := by
  simp only [symbol, Fin.isValue, ite_true, one_ne_zero, ite_false]
  ring

lemma symbol_curl (k : Fin 2 → ℤ) (hk : k ≠ 0) :
    Complex.I * ((k 0 : ℂ) * symbol 1 k - (k 1 : ℂ) * symbol 0 k) = 1 := by
  have hz : (frequencySq k : ℂ) ≠ 0 := by
    exact_mod_cast (frequencySq_eq_zero_iff k).not.mpr hk
  simp only [symbol, Fin.isValue, ite_true, one_ne_zero, ite_false]
  field_simp
  simp only [frequencySq, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_intCast]
  ring_nf
  simp [Complex.I_sq]

def component (j : Fin 2) : BoxFourierL2 →L[ℂ] BoxFourierL2 :=
  boxMultiplier (symbol j) (symbol_norm_le j)

lemma component_coeff (j : Fin 2) (f : BoxFourierL2) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusL2Equiv (component j f)) k =
      symbol j k * UnitAddTorus.mFourierCoeff (torusL2Equiv f) k :=
  boxMultiplier_coeff _ _ _ _

lemma component_norm_le (j : Fin 2) (f : BoxFourierL2) : ‖component j f‖ ≤ ‖f‖ :=
  boxMultiplier_norm_le _ _ _

def complexify : Lp ℝ 2 μT →L[ℝ] BoxFourierL2 :=
  Complex.ofRealCLM.compLpL 2 μT

lemma coeFn_complexify (f : Lp ℝ 2 μT) :
    complexify f =ᵐ[μT] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

lemma complexify_norm_le (f : Lp ℝ 2 μT) : ‖complexify f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_complexify f] with x hx
  simp [hx]

lemma mFourierCoeff_lift_zero (f : BoxFourierL2) :
    UnitAddTorus.mFourierCoeff (torusL2Equiv f) 0 =
      (2 * π : ℂ)⁻¹ * ∫ x, f x ∂μT := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]
  change (∫ t, torusLiftFn f t) = _
  rw [integral_congr_ae (coeFn_torusLiftFn f), integral_const_mul, integral_torusRep]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp

lemma integral_boxRealCoordInjection (j : Fin 2) (v : BoxFourierL2) :
    (∫ x, boxRealCoordInjection j v x ∂μT) =
      realCoordInjection j (∫ x, v x ∂μT) := by
  calc
    _ = ∫ x, realCoordInjection j (v x) ∂μT := by
      apply integral_congr_ae
      exact coeFn_boxRealCoordInjection j v
    _ = _ := (realCoordInjection j).integral_comp_comm
      ((Lp.memLp v).integrable (by norm_num))

lemma integral_component_zero (j : Fin 2) (f : BoxFourierL2) :
    (∫ x, component j f x ∂μT) = 0 := by
  have h₀ : UnitAddTorus.mFourierCoeff (torusL2Equiv (component j f)) 0 = 0 := by
    rw [component_coeff, symbol_zero, zero_mul]
  rw [mFourierCoeff_lift_zero] at h₀
  exact (mul_eq_zero.mp h₀).resolve_left (by
    apply inv_ne_zero
    exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity))

def pairedPolynomial (N : ℕ) (v : Fin 2 → BoxFourierL2) (x : R2) : R2 :=
  boxScalarFourierPolynomial N (v 0) x • EuclideanSpace.single 0 1 +
    boxScalarFourierPolynomial N (v 1) x • EuclideanSpace.single 1 1

def pairedTrunc (N : ℕ) (v : Fin 2 → BoxFourierL2) : L2T :=
  boxRealCoordInjection 0 (boxScalarFourierTrunc N (v 0)) +
    boxRealCoordInjection 1 (boxScalarFourierTrunc N (v 1))

lemma pairedPolynomial_apply (N : ℕ) (v : Fin 2 → BoxFourierL2) (x : R2) (j : Fin 2) :
    pairedPolynomial N v x j = boxScalarFourierPolynomial N (v j) x := by
  fin_cases j <;> simp [pairedPolynomial, EuclideanSpace.single_apply]

lemma pairedPolynomial_smooth_periodic (N : ℕ) (v : Fin 2 → BoxFourierL2) :
    ContDiff ℝ ∞ (pairedPolynomial N v) ∧ IsTorusPeriodic (pairedPolynomial N v) := by
  have h₀ := isScalarTest_boxScalarFourierPolynomial N (v 0)
  have h₁ := isScalarTest_boxScalarFourierPolynomial N (v 1)
  refine ⟨(h₀.1.smul contDiff_const).add (h₁.1.smul contDiff_const), ?_⟩
  intro x i
  simp only [pairedPolynomial, h₀.2 x i, h₁.2 x i]

lemma pairedTrunc_ae (N : ℕ) (v : Fin 2 → BoxFourierL2) :
    pairedTrunc N v =ᵐ[μT] pairedPolynomial N v := by
  filter_upwards [Lp.coeFn_add (boxRealCoordInjection 0 (boxScalarFourierTrunc N (v 0)))
      (boxRealCoordInjection 1 (boxScalarFourierTrunc N (v 1))),
    coeFn_boxRealCoordInjection 0 (boxScalarFourierTrunc N (v 0)),
    coeFn_boxRealCoordInjection 1 (boxScalarFourierTrunc N (v 1)),
    coeFn_boxScalarFourierTrunc_re N (v 0), coeFn_boxScalarFourierTrunc_re N (v 1)]
    with x hadd h₀ h₁ hp₀ hp₁
  change (boxRealCoordInjection 0 (boxScalarFourierTrunc N (v 0)) +
    boxRealCoordInjection 1 (boxScalarFourierTrunc N (v 1))) x = _
  rw [hadd]
  change boxRealCoordInjection 0 (boxScalarFourierTrunc N (v 0)) x +
    boxRealCoordInjection 1 (boxScalarFourierTrunc N (v 1)) x = _
  rw [h₀, h₁, hp₀, hp₁]
  rfl

lemma pd_pairedPolynomial (N : ℕ) (v : Fin 2 → BoxFourierL2) (x : R2) (i j : Fin 2) :
    pd i (pairedPolynomial N v) x j = realFourierPolynomial N
      (fun k => Complex.I * (k i : ℂ) * boxNormalizedFourierCoeff (v j) k) x := by
  rw [← torus_pd_component _ x
    ((pairedPolynomial_smooth_periodic N v).1.differentiable (by simp) x) i j]
  have he : (fun y => pairedPolynomial N v y j) = boxScalarFourierPolynomial N (v j) :=
    funext fun y => pairedPolynomial_apply N v y j
  rw [he]
  exact pd_realFourierPolynomial N _ i x

lemma tendsto_pairedTrunc (v : Fin 2 → BoxFourierL2) :
    Tendsto (fun N => pairedTrunc N v) atTop
      (𝓝 (boxRealCoordInjection 0 (v 0) + boxRealCoordInjection 1 (v 1))) := by
  have h₀ := (boxRealCoordInjection 0).continuous.tendsto (v 0) |>.comp
    (tendsto_boxScalarFourierTrunc (v 0))
  have h₁ := (boxRealCoordInjection 1).continuous.tendsto (v 1) |>.comp
    (tendsto_boxScalarFourierTrunc (v 1))
  exact h₀.add h₁

lemma normalized_component_coeff (j : Fin 2) (f : BoxFourierL2) (k : Fin 2 → ℤ) :
    boxNormalizedFourierCoeff (component j f) k =
      symbol j k * boxNormalizedFourierCoeff f k := by
  unfold boxNormalizedFourierCoeff
  rw [component_coeff]
  ring

lemma normalized_component_div (f : BoxFourierL2) (k : Fin 2 → ℤ) :
    Complex.I * (k 0 : ℂ) * boxNormalizedFourierCoeff (component 0 f) k +
      Complex.I * (k 1 : ℂ) * boxNormalizedFourierCoeff (component 1 f) k = 0 := by
  rw [normalized_component_coeff, normalized_component_coeff]
  calc
    _ = Complex.I * ((k 0 : ℂ) * symbol 0 k + (k 1 : ℂ) * symbol 1 k) *
        boxNormalizedFourierCoeff f k := by ring
    _ = 0 := by rw [symbol_div, mul_zero, zero_mul]

lemma normalized_complexify_zero (f : Lp ℝ 2 μT) (hf : (∫ x, f x ∂μT) = 0) :
    boxNormalizedFourierCoeff (complexify f) 0 = 0 := by
  rw [boxNormalizedFourierCoeff, mFourierCoeff_torusL2Equiv_real (coeFn_complexify f)
    ((Lp.memLp f).integrable (by norm_num))]
  simp [boxFourierCoeff, boxFourierPhase_apply, hf]
  rfl

lemma normalized_component_curl (f : Lp ℝ 2 μT) (hf : (∫ x, f x ∂μT) = 0)
    (k : Fin 2 → ℤ) :
    Complex.I * (k 0 : ℂ) * boxNormalizedFourierCoeff (component 1 (complexify f)) k -
      Complex.I * (k 1 : ℂ) * boxNormalizedFourierCoeff (component 0 (complexify f)) k =
        boxNormalizedFourierCoeff (complexify f) k := by
  rw [normalized_component_coeff, normalized_component_coeff]
  by_cases hk : k = 0
  · subst k
    simp [normalized_complexify_zero f hf]
  · calc
      _ = (Complex.I * ((k 0 : ℂ) * symbol 1 k - (k 1 : ℂ) * symbol 0 k)) *
          boxNormalizedFourierCoeff (complexify f) k := by ring
      _ = _ := by rw [symbol_curl k hk, one_mul]

lemma realPart_complexify (f : Lp ℝ 2 μT) : boxRealPart (complexify f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_boxRealPart (complexify f), coeFn_complexify f] with x hre hc
  rw [hre, hc, Complex.ofReal_re]

lemma tendsto_realPart_trunc_complexify (f : Lp ℝ 2 μT) :
    Tendsto (fun N => boxRealPart (boxScalarFourierTrunc N (complexify f))) atTop (𝓝 f) := by
  simpa only [Function.comp_def, realPart_complexify] using
    (boxRealPart.continuous.tendsto (complexify f)).comp
      (tendsto_boxScalarFourierTrunc (complexify f))

lemma pairedPolynomial_div (N : ℕ) (f : BoxFourierL2) (x : R2) :
    pd 0 (pairedPolynomial N (fun j => component j f)) x 0 +
      pd 1 (pairedPolynomial N (fun j => component j f)) x 1 = 0 := by
  rw [pd_pairedPolynomial, pd_pairedPolynomial]
  unfold realFourierPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← realFourierMode_add, normalized_component_div, realFourierMode_zero]

lemma pairedPolynomial_curl (N : ℕ) (f : Lp ℝ 2 μT) (hf : (∫ x, f x ∂μT) = 0)
    (x : R2) :
    pd 0 (pairedPolynomial N (fun j => component j (complexify f))) x 1 -
      pd 1 (pairedPolynomial N (fun j => component j (complexify f))) x 0 =
        boxScalarFourierPolynomial N (complexify f) x := by
  rw [pd_pairedPolynomial, pd_pairedPolynomial]
  unfold boxScalarFourierPolynomial realFourierPolynomial
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← realFourierMode_sub, normalized_component_curl f hf]

lemma pairedTrunc_isCurl (N : ℕ) (f : Lp ℝ 2 μT) (hf : (∫ x, f x ∂μT) = 0) :
    IsCurl (pairedTrunc N (fun j => component j (complexify f)))
      (boxRealPart (boxScalarFourierTrunc N (complexify f))) := by
  have hs := pairedPolynomial_smooth_periodic N (fun j => component j (complexify f))
  have hraw := isCurl_of_C1_matching_faces (hs.1.of_le (by exact_mod_cast le_top))
    hs.2.matchesTorusFaces
  apply hraw.congr_ae (pairedTrunc_ae N (fun j => component j (complexify f))).symm
  have hcurl : (fun x => pd 0 (pairedPolynomial N (fun j => component j (complexify f))) x 1 -
      pd 1 (pairedPolynomial N (fun j => component j (complexify f))) x 0) =ᵐ[μT]
      boxScalarFourierPolynomial N (complexify f) :=
    Eventually.of_forall (pairedPolynomial_curl N f hf)
  exact hcurl.trans ((coeFn_boxRealPart _).trans
    (coeFn_boxScalarFourierTrunc_re N (complexify f))).symm

end BiotSavartConstruction

open BiotSavartConstruction

/-- The actual continuous real-linear torus inverse curl. -/
def biotSavartL2 : Lp ℝ 2 μT →L[ℝ] L2T :=
  (boxRealCoordInjection 0).comp (((component 0).restrictScalars ℝ).comp complexify) +
    (boxRealCoordInjection 1).comp (((component 1).restrictScalars ℝ).comp complexify)

lemma norm_biotSavartL2_le (f : Lp ℝ 2 μT) : ‖biotSavartL2 f‖ ≤ 2 * ‖f‖ := by
  change ‖boxRealCoordInjection 0 (component 0 (complexify f)) +
    boxRealCoordInjection 1 (component 1 (complexify f))‖ ≤ _
  calc
    _ ≤ ‖boxRealCoordInjection 0 (component 0 (complexify f))‖ +
      ‖boxRealCoordInjection 1 (component 1 (complexify f))‖ := norm_add_le _ _
    _ ≤ ‖component 0 (complexify f)‖ + ‖component 1 (complexify f)‖ :=
      add_le_add (norm_boxRealCoordInjection_le _ _) (norm_boxRealCoordInjection_le _ _)
    _ ≤ ‖complexify f‖ + ‖complexify f‖ :=
      add_le_add (component_norm_le _ _) (component_norm_le _ _)
    _ ≤ 2 * ‖f‖ := by linarith [complexify_norm_le f]

/-- The inverse construction fixes the actual vector-valued spatial mean to zero. -/
lemma integral_biotSavartL2 (f : Lp ℝ 2 μT) :
    (∫ x in torusBox, biotSavartL2 f x) = 0 := by
  let a := boxRealCoordInjection 0 (component 0 (complexify f))
  let b := boxRealCoordInjection 1 (component 1 (complexify f))
  change (∫ x, (a + b) x ∂μT) = 0
  calc
    _ = ∫ x, a x + b x ∂μT := integral_congr_ae (Lp.coeFn_add a b)
    _ = (∫ x, a x ∂μT) + ∫ x, b x ∂μT :=
      integral_add ((Lp.memLp a).integrable (by norm_num))
        ((Lp.memLp b).integrable (by norm_num))
    _ = 0 := by
      dsimp [a, b]
      rw [integral_boxRealCoordInjection, integral_boxRealCoordInjection,
        integral_component_zero, integral_component_zero]
      simp

/-- The explicitly constructed inverse is distributionally divergence free. -/
theorem divFree_biotSavartL2 (f : Lp ℝ 2 μT) : DivFree (biotSavartL2 f) := by
  have hv : Tendsto (fun N => pairedTrunc N (fun j => component j (complexify f)))
      atTop (𝓝 (biotSavartL2 f)) := tendsto_pairedTrunc _
  apply divFree_of_tendsto hv
  exact Eventually.of_forall fun N => divFree_of_pointwise_divergence_zero
    (pairedTrunc_ae N _) ((pairedPolynomial_smooth_periodic N _).1.of_le
      (by exact_mod_cast le_top)) (pairedPolynomial_smooth_periodic N _).2
    (pairedPolynomial_div N (complexify f))

/-- On zero-mean scalar `L²`, the actual continuous linear construction is
a right inverse to the distributional curl. -/
theorem isCurl_biotSavartL2 (f : Lp ℝ 2 μT) (hf : (∫ x in torusBox, f x) = 0) :
    IsCurl (biotSavartL2 f) f := by
  have hv : Tendsto (fun N => pairedTrunc N (fun j => component j (complexify f)))
      atTop (𝓝 (biotSavartL2 f)) := tendsto_pairedTrunc _
  have hw := tendsto_realPart_trunc_complexify f
  intro ψ hψ
  have hl : Tendsto (fun N => ∫ x in torusBox,
      boxRealPart (boxScalarFourierTrunc N (complexify f)) x * ψ x) atTop
      (𝓝 (∫ x in torusBox, f x * ψ x)) := by
    simp_rw [scalar_test_pairing_eq_inner _ hψ.1.continuous]
    exact hw.inner tendsto_const_nhds
  have hpd (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsplit (v : L2T) :
      (∫ x in torusBox, v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x) =
        (∫ x in torusBox, v x 0 * pd 1 ψ x) - ∫ x in torusBox, v x 1 * pd 0 ψ x := by
    have hint (i j : Fin 2) : Integrable (fun x => v x i * pd j ψ x) μT := by
      obtain ⟨C, hC⟩ := bound_on_box (hpd j)
      exact integrable_lin v i (hpd j).aestronglyMeasurable hC
    exact integral_sub (hint 0 1) (hint 1 0)
  have hr : Tendsto (fun N => ∫ x in torusBox,
      pairedTrunc N (fun j => component j (complexify f)) x 0 * pd 1 ψ x -
        pairedTrunc N (fun j => component j (complexify f)) x 1 * pd 0 ψ x) atTop
      (𝓝 (∫ x in torusBox, biotSavartL2 f x 0 * pd 1 ψ x -
        biotSavartL2 f x 1 * pd 0 ψ x)) := by
    simp_rw [hsplit]
    exact (tendsto_integral_lin hv (hpd 1) 0).sub (tendsto_integral_lin hv (hpd 0) 1)
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun N =>
    (pairedTrunc_isCurl N f hf ψ hψ).symm))

theorem isCurl_biotSavartL2_toLp (w : R2 → ℝ) (hw : MemLp w 2 μT)
    (hmean : (∫ x in torusBox, w x) = 0) :
    IsCurl (biotSavartL2 (hw.toLp w)) w := by
  have hm : (∫ x in torusBox, hw.toLp w x) = 0 :=
    (integral_congr_ae hw.coeFn_toLp).trans hmean
  exact (isCurl_biotSavartL2 _ hm).congr_ae Filter.EventuallyEq.rfl hw.coeFn_toLp

/-- Existence is a conclusion of the explicit Fourier construction, with
the actual mean, divergence, curl, and physical `L²` estimate. -/
theorem exists_velocity_of_L2_zero_mean_curl (w : R2 → ℝ) (hw : MemLp w 2 μT)
    (hmean : (∫ x in torusBox, w x) = 0) :
    ∃ u : L2T, DivFree u ∧ (∫ x in torusBox, u x) = 0 ∧ IsCurl u w ∧
      ‖u‖ ≤ 2 * (eLpNorm w 2 μT).toReal := by
  refine ⟨biotSavartL2 (hw.toLp w), divFree_biotSavartL2 _, integral_biotSavartL2 _,
    isCurl_biotSavartL2_toLp w hw hmean, ?_⟩
  simpa only [Lp.norm_toLp] using norm_biotSavartL2_le (hw.toLp w)

end Euler2D

end
