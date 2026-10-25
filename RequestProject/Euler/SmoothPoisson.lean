module

public import RequestProject.Euler.BiotSavartSobolevL2
public import RequestProject.Euler.LagrangianTransport
public import RequestProject.Euler.ContinuousPeriodicEquality

/-!
# Smooth periodic Poisson inversion by actual Fourier series

The coefficient estimates are derived from repeated periodic integration
by parts.  Summability on the two-dimensional integer lattice is proved
from the ordinary integer p-series, rather than assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal BoundedContinuousFunction

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace SmoothPoissonConstruction

lemma scalarTest_pd {g : R2 → ℝ} (hg : IsScalarTest g) (i : Fin 2) :
    IsScalarTest (pd i g) :=
  ⟨(hg.1.fderiv_right (by simp)).clm_apply contDiff_const,
    isTorusPeriodic_pd hg.2 i⟩

lemma boxFourierCoeff_sub {f g : R2 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (k : Fin 2 → ℤ) : boxFourierCoeff (fun x => f x - g x) k =
      boxFourierCoeff f k - boxFourierCoeff g k := by
  have hc (h : R2 → ℝ) (hh : Continuous h) :
      Integrable (fun x => h x * cos (boxFourierPhase k x)) μT :=
    integrable_torusBox_of_continuous (hh.mul (isScalarTest_boxFourier_cos k).1.continuous)
  have hs (h : R2 → ℝ) (hh : Continuous h) :
      Integrable (fun x => h x * sin (boxFourierPhase k x)) μT :=
    integrable_torusBox_of_continuous (hh.mul (isScalarTest_boxFourier_sin k).1.continuous)
  apply Complex.ext <;> simp [boxFourierCoeff, sub_mul,
    integral_sub (hc f hf) (hc g hg), integral_sub (hs f hf) (hs g hg)]
  ring

/-- Periodic integration by parts gives the physical derivative multiplier. -/
lemma boxFourierCoeff_pd {g : R2 → ℝ} (hg : IsScalarTest g) (i : Fin 2)
    (k : Fin 2 → ℤ) : boxFourierCoeff (pd i g) k =
      Complex.I * (k i : ℂ) * boxFourierCoeff g k := by
  have hg1 : ContDiff ℝ 1 g := hg.1.of_le (by exact_mod_cast le_top)
  have hc := isScalarTest_boxFourier_cos k
  have hs := isScalarTest_boxFourier_sin k
  have hcos : (∫ x, pd i g x * cos (boxFourierPhase k x) ∂μT) =
      (k i : ℝ) * ∫ x, g x * sin (boxFourierPhase k x) ∂μT := by
    have h := integral_mul_pd_periodic g _ hg1 (hc.1.of_le (by exact_mod_cast le_top))
      hg.2 hc.2 i
    have he : (fun x => g x * pd i (fun y => cos (boxFourierPhase k y)) x) =
        (fun x => -(k i : ℝ) * (g x * sin (boxFourierPhase k x))) := by
      funext x
      rw [pd_boxFourier_cos]
      ring
    rw [he, integral_const_mul] at h
    linarith
  have hsin : (∫ x, pd i g x * sin (boxFourierPhase k x) ∂μT) =
      -(k i : ℝ) * ∫ x, g x * cos (boxFourierPhase k x) ∂μT := by
    have h := integral_mul_pd_periodic g _ hg1 (hs.1.of_le (by exact_mod_cast le_top))
      hg.2 hs.2 i
    have he : (fun x => g x * pd i (fun y => sin (boxFourierPhase k y)) x) =
        (fun x => (k i : ℝ) * (g x * cos (boxFourierPhase k x))) := by
      funext x
      rw [pd_boxFourier_sin]
      ring
    rw [he, integral_const_mul] at h
    linarith
  apply Complex.ext <;>
    simp [boxFourierCoeff, Complex.mul_re, Complex.mul_im, hcos, hsin]

/-- A convenient elliptic regularizer whose Fourier multiplier never vanishes. -/
def regularizer (g : R2 → ℝ) (x : R2) : ℝ :=
  g x - pd 0 (pd 0 g) x - pd 1 (pd 1 g) x

lemma scalarTest_regularizer {g : R2 → ℝ} (hg : IsScalarTest g) :
    IsScalarTest (regularizer g) := by
  have h₀ := scalarTest_pd (scalarTest_pd hg 0) 0
  have h₁ := scalarTest_pd (scalarTest_pd hg 1) 1
  refine ⟨(hg.1.sub h₀.1).sub h₁.1, ?_⟩
  intro x i
  simp only [regularizer, hg.2 x i, h₀.2 x i, h₁.2 x i]

lemma boxFourierCoeff_regularizer {g : R2 → ℝ} (hg : IsScalarTest g) (k : Fin 2 → ℤ) :
    boxFourierCoeff (regularizer g) k =
      ((1 + frequencySq k : ℝ) : ℂ) * boxFourierCoeff g k := by
  have h₀ := scalarTest_pd (scalarTest_pd hg 0) 0
  have h₁ := scalarTest_pd (scalarTest_pd hg 1) 1
  rw [show regularizer g = (fun x => (g x - pd 0 (pd 0 g) x) - pd 1 (pd 1 g) x) from rfl,
    boxFourierCoeff_sub (f := fun x => g x - pd 0 (pd 0 g) x)
      (hg.1.continuous.sub h₀.1.continuous) h₁.1.continuous,
    boxFourierCoeff_sub hg.1.continuous h₀.1.continuous,
    boxFourierCoeff_pd (scalarTest_pd hg 0), boxFourierCoeff_pd hg,
    boxFourierCoeff_pd (scalarTest_pd hg 1), boxFourierCoeff_pd hg]
  simp only [frequencySq, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_intCast]
  ring_nf
  simp [Complex.I_sq]
  ring

def regularizerIter : ℕ → (R2 → ℝ) → R2 → ℝ
  | 0, g => g
  | n + 1, g => regularizer (regularizerIter n g)

lemma scalarTest_regularizerIter {g : R2 → ℝ} (hg : IsScalarTest g) (n : ℕ) :
    IsScalarTest (regularizerIter n g) := by
  induction n with
  | zero => exact hg
  | succ n ih => exact scalarTest_regularizer ih

lemma boxFourierCoeff_regularizerIter {g : R2 → ℝ} (hg : IsScalarTest g)
    (n : ℕ) (k : Fin 2 → ℤ) :
    boxFourierCoeff (regularizerIter n g) k =
      (((1 + frequencySq k : ℝ) : ℂ) ^ n) * boxFourierCoeff g k := by
  induction n with
  | zero => simp [regularizerIter]
  | succ n ih =>
    rw [regularizerIter, boxFourierCoeff_regularizer (scalarTest_regularizerIter hg n), ih,
      pow_succ]
    ring

lemma norm_boxFourierCoeff_le {g : R2 → ℝ} (hg : Integrable g μT) (k : Fin 2 → ℤ) :
    ‖boxFourierCoeff g k‖ ≤ ∫ x, |g x| ∂μT := by
  rw [← integral_boxFourier_character hg k]
  have hm : AEStronglyMeasurable
      (fun x => UnitAddTorus.mFourier (-k) (torusProj x)) μT :=
    ((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_torusProj).aestronglyMeasurable
  have hbound (x : R2) : ‖UnitAddTorus.mFourier (-k) (torusProj x)‖ ≤ 1 :=
    ((UnitAddTorus.mFourier (-k)).norm_coe_le_norm _).trans_eq (UnitAddTorus.mFourier_norm (n := -k))
  have hi : Integrable (fun x => UnitAddTorus.mFourier (-k) (torusProj x) * (g x : ℂ)) μT :=
    (hg.ofReal : Integrable (fun x => (g x : ℂ)) μT).bdd_mul hm
      (Eventually.of_forall hbound)
  apply le_trans (norm_integral_le_integral_norm _)
  apply integral_mono_ae hi.norm hg.norm
  exact Eventually.of_forall fun x => by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul] using
      mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg (g x))

/-- Every power of Fourier decay is derived from actual derivatives of `g`. -/
theorem boxFourierCoeff_rapid_decay {g : R2 → ℝ} (hg : IsScalarTest g) (n : ℕ)
    (k : Fin 2 → ℤ) :
    ‖boxFourierCoeff g k‖ ≤
      (∫ x, |regularizerIter n g x| ∂μT) / (1 + frequencySq k) ^ n := by
  have hp : 0 < 1 + frequencySq k := by have := frequencySq_nonneg k; positivity
  have h := norm_boxFourierCoeff_le
    (integrable_torusBox_of_continuous (scalarTest_regularizerIter hg n).1.continuous) k
  rw [boxFourierCoeff_regularizerIter hg n k, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hp] at h
  exact (le_div_iff₀ (pow_pos hp n)).mpr (by simpa only [mul_comm] using h)

lemma summable_integer_resolvent : Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
  apply (summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (1 + (n : ℝ) ^ 2))]
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_ne_zero hn') (by linarith)

lemma summable_product_resolvent :
    Summable (fun p : ℤ × ℤ => (1 / (1 + (p.1 : ℝ) ^ 2)) * (1 / (1 + (p.2 : ℝ) ^ 2))) := by
  let w (n : ℤ) := 1 / (1 + (n : ℝ) ^ 2)
  have hw : Summable w := summable_integer_resolvent
  apply (summable_prod_of_nonneg (f := fun p : ℤ × ℤ => w p.1 * w p.2)
    (fun p => by dsimp [w]; positivity)).mpr
  refine ⟨fun x => hw.mul_left (w x), ?_⟩
  simp_rw [tsum_mul_left]
  exact hw.mul_right _

lemma lattice_resolvent_le_product (k : Fin 2 → ℤ) :
    1 / (1 + frequencySq k) ^ 2 ≤
      (1 / (1 + (k 0 : ℝ) ^ 2)) * (1 / (1 + (k 1 : ℝ) ^ 2)) := by
  have hd : (1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2) ≤
      (1 + frequencySq k) ^ 2 := by
    unfold frequencySq
    nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ),
      sq_nonneg ((k 0 : ℝ) ^ 2), sq_nonneg ((k 1 : ℝ) ^ 2),
      mul_nonneg (sq_nonneg (k 0 : ℝ)) (sq_nonneg (k 1 : ℝ))]
  calc
    _ ≤ 1 / ((1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2)) :=
      (div_le_div_iff₀ (by have := frequencySq_nonneg k; positivity) (by positivity)).mpr
        (by simpa only [one_mul] using hd)
    _ = _ := by field_simp

/-- The actual two-dimensional lattice resolvent is summable. -/
theorem summable_lattice_resolvent :
    Summable (fun k : Fin 2 → ℤ => 1 / (1 + frequencySq k) ^ 2) := by
  have hboth : Summable (fun k : Fin 2 → ℤ =>
      (1 / (1 + (k 0 : ℝ) ^ 2)) * (1 / (1 + (k 1 : ℝ) ^ 2))) := by
    have hh : Summable (fun k : Fin 2 → ℤ =>
        (fun p : ℤ × ℤ => (1 / (1 + (p.1 : ℝ) ^ 2)) * (1 / (1 + (p.2 : ℝ) ^ 2)))
          (finTwoArrowEquiv ℤ k)) :=
      summable_product_resolvent.comp_injective (finTwoArrowEquiv ℤ).injective
    exact hh
  exact Summable.of_nonneg_of_le (fun k => by positivity) lattice_resolvent_le_product hboth

lemma norm_phase_le (k : Fin 2 → ℤ) : ‖boxFourierPhase k‖ ≤ 2 * (1 + frequencySq k) := by
  apply ContinuousLinearMap.opNorm_le_bound (boxFourierPhase k)
    (by have := frequencySq_nonneg k; positivity)
  intro x
  rw [Real.norm_eq_abs, boxFourierPhase_apply, Fin.sum_univ_two]
  have hx₀ : |x 0| ≤ ‖x‖ := PiLp.norm_apply_le x 0
  have hx₁ : |x 1| ≤ ‖x‖ := PiLp.norm_apply_le x 1
  have hk₀ := BiotSavartConstruction.abs_frequency_le k 0
  have hk₁ := BiotSavartConstruction.abs_frequency_le k 1
  calc
    _ ≤ |(k 0 : ℝ) * x 0| + |(k 1 : ℝ) * x 1| := abs_add_le _ _
    _ = |(k 0 : ℝ)| * |x 0| + |(k 1 : ℝ)| * |x 1| := by rw [abs_mul, abs_mul]
    _ ≤ (|(k 0 : ℝ)| + |(k 1 : ℝ)|) * ‖x‖ := by
      nlinarith [mul_nonneg (abs_nonneg (k 0 : ℝ)) (sub_nonneg.mpr hx₀),
        mul_nonneg (abs_nonneg (k 1 : ℝ)) (sub_nonneg.mpr hx₁)]
    _ ≤ (2 * (1 + frequencySq k)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)

lemma norm_iteratedFDeriv_cos_mode_le (k : Fin 2 → ℤ) (n : ℕ) (x : R2) :
    ‖iteratedFDeriv ℝ n (fun y => cos (boxFourierPhase k y)) x‖ ≤ ‖boxFourierPhase k‖ ^ n := by
  change ‖iteratedFDeriv ℝ n (cos ∘ boxFourierPhase k) x‖ ≤ _
  rw [(boxFourierPhase k).iteratedFDeriv_comp_right
    (Real.contDiff_cos : ContDiff ℝ ∞ cos) x (by exact_mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n cos (boxFourierPhase k x)‖ * ‖boxFourierPhase k‖ ^ n := by
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ n cos (boxFourierPhase k x)) (fun _ => boxFourierPhase k)
    _ ≤ 1 * ‖boxFourierPhase k‖ ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact abs_iteratedDeriv_cos_le_one n _
    _ = _ := one_mul _

lemma norm_iteratedFDeriv_sin_mode_le (k : Fin 2 → ℤ) (n : ℕ) (x : R2) :
    ‖iteratedFDeriv ℝ n (fun y => sin (boxFourierPhase k y)) x‖ ≤ ‖boxFourierPhase k‖ ^ n := by
  change ‖iteratedFDeriv ℝ n (sin ∘ boxFourierPhase k) x‖ ≤ _
  rw [(boxFourierPhase k).iteratedFDeriv_comp_right
    (Real.contDiff_sin : ContDiff ℝ ∞ sin) x (by exact_mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n sin (boxFourierPhase k x)‖ * ‖boxFourierPhase k‖ ^ n := by
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ n sin (boxFourierPhase k x)) (fun _ => boxFourierPhase k)
    _ ≤ 1 * ‖boxFourierPhase k‖ ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact abs_iteratedDeriv_sin_le_one n _
    _ = _ := one_mul _

lemma norm_iteratedFDeriv_realFourierMode_le (a : ℂ) (k : Fin 2 → ℤ) (n : ℕ) (x : R2) :
    ‖iteratedFDeriv ℝ n (realFourierMode a k) x‖ ≤ 2 * ‖a‖ * ‖boxFourierPhase k‖ ^ n := by
  have hc : ContDiffAt ℝ n (fun y => cos (boxFourierPhase k y)) x :=
    ((isScalarTest_boxFourier_cos k).1.of_le (by exact_mod_cast le_top)).contDiffAt
  have hs : ContDiffAt ℝ n (fun y => sin (boxFourierPhase k y)) x :=
    ((isScalarTest_boxFourier_sin k).1.of_le (by exact_mod_cast le_top)).contDiffAt
  have he : realFourierMode a k = a.re • (fun y => cos (boxFourierPhase k y)) +
      (-a.im) • (fun y => sin (boxFourierPhase k y)) := by
    funext y
    simp [realFourierMode, sub_eq_add_neg]
  have hca : ContDiffAt ℝ n (a.re • (fun y => cos (boxFourierPhase k y))) x :=
    hc.const_smul a.re
  have hsa : ContDiffAt ℝ n ((-a.im) • (fun y => sin (boxFourierPhase k y))) x :=
    hs.const_smul (-a.im)
  rw [he, iteratedFDeriv_add_apply hca hsa,
    iteratedFDeriv_const_smul_apply hc, iteratedFDeriv_const_smul_apply hs]
  calc
    _ ≤ |a.re| * ‖iteratedFDeriv ℝ n (fun y => cos (boxFourierPhase k y)) x‖ +
        |a.im| * ‖iteratedFDeriv ℝ n (fun y => sin (boxFourierPhase k y)) x‖ := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_neg] using norm_add_le
        (a.re • iteratedFDeriv ℝ n (fun y => cos (boxFourierPhase k y)) x)
        (-a.im • iteratedFDeriv ℝ n (fun y => sin (boxFourierPhase k y)) x)
    _ ≤ ‖a‖ * ‖boxFourierPhase k‖ ^ n + ‖a‖ * ‖boxFourierPhase k‖ ^ n :=
      add_le_add
        (mul_le_mul (Complex.abs_re_le_norm a) (norm_iteratedFDeriv_cos_mode_le k n x)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Complex.abs_im_le_norm a) (norm_iteratedFDeriv_sin_mode_le k n x)
          (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

def RapidCoefficients (a : (Fin 2 → ℤ) → ℂ) : Prop :=
  ∀ n : ℕ, Summable (fun k => ‖a k‖ * (1 + frequencySq k) ^ n)

lemma summable_weighted_boxFourierCoeff {g : R2 → ℝ} (hg : IsScalarTest g) (n : ℕ) :
    Summable (fun k => ‖boxFourierCoeff g k‖ * (1 + frequencySq k) ^ n) := by
  let C := ∫ x, |regularizerIter (n + 2) g x| ∂μT
  have hC : 0 ≤ C := integral_nonneg fun x => abs_nonneg _
  apply Summable.of_nonneg_of_le (fun k => by have := frequencySq_nonneg k; positivity) _
    (summable_lattice_resolvent.mul_left C)
  intro k
  have hp : 0 < 1 + frequencySq k := by have := frequencySq_nonneg k; positivity
  calc
    _ ≤ (C / (1 + frequencySq k) ^ (n + 2)) * (1 + frequencySq k) ^ n :=
      mul_le_mul_of_nonneg_right (boxFourierCoeff_rapid_decay hg (n + 2) k) (by positivity)
    _ = C * (1 / (1 + frequencySq k) ^ 2) := by
      rw [pow_add]
      field_simp

def physicalCoeff (g : R2 → ℝ) (k : Fin 2 → ℤ) : ℂ :=
  ((2 * π : ℂ) ^ 2)⁻¹ * boxFourierCoeff g k

lemma rapid_physicalCoeff {g : R2 → ℝ} (hg : IsScalarTest g) :
    RapidCoefficients (physicalCoeff g) := by
  intro n
  convert (summable_weighted_boxFourierCoeff hg n).mul_left ‖((2 * π : ℂ) ^ 2)⁻¹‖ using 1
  funext k
  simp [physicalCoeff, mul_assoc]

def coeffDerivative (i : Fin 2) (a : (Fin 2 → ℤ) → ℂ) (k : Fin 2 → ℤ) : ℂ :=
  Complex.I * (k i : ℂ) * a k

lemma RapidCoefficients.derivative {a : (Fin 2 → ℤ) → ℂ} (ha : RapidCoefficients a)
    (i : Fin 2) : RapidCoefficients (coeffDerivative i a) := by
  intro n
  apply Summable.of_nonneg_of_le (fun k => by have := frequencySq_nonneg k; positivity) _ (ha (n + 1))
  intro k
  simp only [coeffDerivative, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
  have hi : |(k i : ℝ)| ≤ 1 + frequencySq k :=
    (BiotSavartConstruction.abs_frequency_le k i).trans (by linarith)
  calc
    _ ≤ (1 + frequencySq k) * ‖a k‖ * (1 + frequencySq k) ^ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
        (by have := frequencySq_nonneg k; positivity)
    _ = _ := by rw [pow_succ]; ring

def modeSeries (a : (Fin 2 → ℤ) → ℂ) (x : R2) : ℝ :=
  ∑' k, realFourierMode (a k) k x

lemma modeSeries_periodic (a : (Fin 2 → ℤ) → ℂ) : IsTorusPeriodic (modeSeries a) := by
  intro x i
  exact tsum_congr fun k => (isScalarTest_realFourierMode (a k) k).2 x i

lemma modeSeries_smooth {a : (Fin 2 → ℤ) → ℂ} (ha : RapidCoefficients a) :
    ContDiff ℝ ∞ (modeSeries a) := by
  apply contDiff_tsum (v := fun n k => (2 : ℝ) ^ (n + 1) * ‖a k‖ * (1 + frequencySq k) ^ n)
    (fun k => (isScalarTest_realFourierMode (a k) k).1)
  · intro n hn
    convert (ha n).mul_left ((2 : ℝ) ^ (n + 1)) using 1
    funext k
    ring
  · intro n k x hn
    calc
      _ ≤ 2 * ‖a k‖ * ‖boxFourierPhase k‖ ^ n :=
        norm_iteratedFDeriv_realFourierMode_le (a k) k n x
      _ ≤ 2 * ‖a k‖ * (2 * (1 + frequencySq k)) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_phase_le k) n) (by positivity)
      _ = _ := by rw [mul_pow, pow_succ]; ring

lemma summable_modes {a : (Fin 2 → ℤ) → ℂ} (ha : RapidCoefficients a) (x : R2) :
    Summable (fun k => realFourierMode (a k) k x) := by
  have hu : Summable (fun k => 2 * ‖a k‖) := by simpa using (ha 0).mul_left 2
  apply hu.of_norm_bounded
  intro k
  simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using
    norm_iteratedFDeriv_realFourierMode_le (a k) k 0 x

lemma norm_fderiv_mode_le (a : ℂ) (k : Fin 2 → ℤ) (x : R2) :
    ‖fderiv ℝ (realFourierMode a k) x‖ ≤ 4 * ‖a‖ * (1 + frequencySq k) := by
  have h := norm_iteratedFDeriv_realFourierMode_le a k 1 x
  rw [norm_iteratedFDeriv_one] at h
  calc
    _ ≤ 2 * ‖a‖ * ‖boxFourierPhase k‖ := by simpa only [pow_one] using h
    _ ≤ 2 * ‖a‖ * (2 * (1 + frequencySq k)) :=
      mul_le_mul_of_nonneg_left (norm_phase_le k) (by positivity)
    _ = _ := by ring

lemma pd_modeSeries {a : (Fin 2 → ℤ) → ℂ} (ha : RapidCoefficients a) (i : Fin 2) (x : R2) :
    pd i (modeSeries a) x = modeSeries (coeffDerivative i a) x := by
  have hu : Summable (fun k => 4 * ‖a k‖ * (1 + frequencySq k)) := by
    simpa only [pow_one, mul_assoc] using (ha 1).mul_left 4
  have hd := hasFDerivAt_tsum hu
    (fun k y => ((isScalarTest_realFourierMode (a k) k).1.differentiable (by simp) y).hasFDerivAt)
    (fun k y => norm_fderiv_mode_le (a k) k y) (summable_modes ha (0 : R2)) x
  have hD : Summable (fun k => fderiv ℝ (realFourierMode (a k) k) x) :=
    hu.of_norm_bounded (fun k => norm_fderiv_mode_le (a k) k x)
  unfold pd modeSeries
  rw [hd.fderiv]
  change (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1))
    (∑' k, fderiv ℝ (realFourierMode (a k) k) x) = _
  rw [(ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).map_tsum hD]
  exact tsum_congr fun k => pd_realFourierMode (a k) k i x

lemma norm_mode_le (a : ℂ) (k : Fin 2 → ℤ) (x : R2) :
    ‖realFourierMode a k x‖ ≤ 2 * ‖a‖ := by
  simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using
    norm_iteratedFDeriv_realFourierMode_le a k 0 x

def boundedMode (a : ℂ) (k : Fin 2 → ℤ) : R2 →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (realFourierMode a k)
    (isScalarTest_realFourierMode a k).1.continuous (2 * ‖a‖) (norm_mode_le a k)

lemma norm_boundedMode_le (a : ℂ) (k : Fin 2 → ℤ) : ‖boundedMode a k‖ ≤ 2 * ‖a‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  exact norm_mode_le a k

lemma summable_boundedModes {a : (Fin 2 → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) :
    Summable (fun k => boundedMode (a k) k) :=
  (ha.mul_left 2).of_norm_bounded fun k => norm_boundedMode_le (a k) k

def boundedSeries (a : (Fin 2 → ℤ) → ℂ) : R2 →ᵇ ℝ := ∑' k, boundedMode (a k) k

lemma boundedSeries_apply {a : (Fin 2 → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) (x : R2) :
    boundedSeries a x = modeSeries a x := by
  change (BoundedContinuousFunction.evalCLM ℝ x) (∑' k, boundedMode (a k) k) = _
  rw [(BoundedContinuousFunction.evalCLM ℝ x).map_tsum (summable_boundedModes ha)]
  rfl

def boundedPartial (N : ℕ) (a : (Fin 2 → ℤ) → ℂ) : R2 →ᵇ ℝ :=
  ∑ k ∈ fourierModes N, boundedMode (a k) k

lemma boundedPartial_apply (N : ℕ) (a : (Fin 2 → ℤ) → ℂ) (x : R2) :
    boundedPartial N a x = realFourierPolynomial N a x := by
  change (BoundedContinuousFunction.evalCLM ℝ x) (∑ k ∈ fourierModes N, boundedMode (a k) k) = _
  rw [map_sum]
  rfl

lemma tendsto_boundedPartial {a : (Fin 2 → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) :
    Tendsto (fun N => boundedPartial N a) atTop (𝓝 (boundedSeries a)) := by
  have hsum : Tendsto (fun s : Finset (Fin 2 → ℤ) => ∑ k ∈ s, boundedMode (a k) k)
      atTop (𝓝 (boundedSeries a)) := (summable_boundedModes ha).hasSum
  exact hsum.comp tendsto_fourierModes_atTop

lemma boundedPartial_toLp (N : ℕ) (v : BoxFourierL2) :
    BoundedContinuousFunction.toLp 2 μT ℝ (boundedPartial N (boxNormalizedFourierCoeff v)) =
      boxRealPart (boxScalarFourierTrunc N v) := by
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μT ℝ
      (boundedPartial N (boxNormalizedFourierCoeff v)),
    (coeFn_boxRealPart _).trans (coeFn_boxScalarFourierTrunc_re N v)] with x hleft hright
  rw [hleft, hright, boundedPartial_apply]
  rfl

lemma physicalCoeff_eq_normalized {g : R2 → ℝ} (hg : IsScalarTest g) (k : Fin 2 → ℤ) :
    physicalCoeff g k = boxNormalizedFourierCoeff
      (BiotSavartConstruction.complexify ((continuous_memLp_torus hg.1.continuous 2).toLp g)) k := by
  symm
  apply boxNormalizedFourierCoeff_real
  · filter_upwards [BiotSavartConstruction.coeFn_complexify
      ((continuous_memLp_torus hg.1.continuous 2).toLp g),
      (continuous_memLp_torus hg.1.continuous 2).coeFn_toLp] with x hc hgx
    rw [hc, hgx]
  · exact integrable_torusBox_of_continuous hg.1.continuous

/-- Actual smooth periodic Fourier reconstruction, pointwise on the whole plane. -/
lemma modeSeries_physicalCoeff {g : R2 → ℝ} (hg : IsScalarTest g) :
    modeSeries (physicalCoeff g) = g := by
  let f : Lp ℝ 2 μT := (continuous_memLp_torus hg.1.continuous 2).toLp g
  have hcoeff : physicalCoeff g = boxNormalizedFourierCoeff (BiotSavartConstruction.complexify f) :=
    funext fun k => physicalCoeff_eq_normalized hg k
  have ha : Summable fun k => ‖physicalCoeff g k‖ := by
    simpa only [pow_zero, mul_one] using rapid_physicalCoeff hg 0
  have hfirst := ((BoundedContinuousFunction.toLp 2 μT ℝ).continuous.tendsto
    (boundedSeries (physicalCoeff g))).comp (tendsto_boundedPartial ha)
  have hsecond := BiotSavartConstruction.tendsto_realPart_trunc_complexify f
  have heach (N : ℕ) : BoundedContinuousFunction.toLp 2 μT ℝ (boundedPartial N (physicalCoeff g)) =
      boxRealPart (boxScalarFourierTrunc N (BiotSavartConstruction.complexify f)) := by
    rw [hcoeff]
    exact boundedPartial_toLp N _
  have hLp : BoundedContinuousFunction.toLp 2 μT ℝ (boundedSeries (physicalCoeff g)) = f :=
    tendsto_nhds_unique hfirst (hsecond.congr' (Eventually.of_forall fun N => (heach N).symm))
  have hrep := BoundedContinuousFunction.coeFn_toLp 2 μT ℝ (boundedSeries (physicalCoeff g))
  rw [hLp] at hrep
  have hfg : (boundedSeries (physicalCoeff g) : R2 → ℝ) =ᵐ[μT] g :=
    hrep.symm.trans (continuous_memLp_torus hg.1.continuous 2).coeFn_toLp
  have hfun : (boundedSeries (physicalCoeff g) : R2 → ℝ) = modeSeries (physicalCoeff g) :=
    funext fun x => boundedSeries_apply ha x
  rw [hfun] at hfg
  exact Continuous.eq_of_periodic_ae_eq (modeSeries_smooth (rapid_physicalCoeff hg)).continuous
    hg.1.continuous (modeSeries_periodic _) hg.2 hfg

lemma one_le_frequencySq {k : Fin 2 → ℤ} (hk : k ≠ 0) : 1 ≤ frequencySq k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have hi' : k i ≠ 0 := hi
  have habs : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  exact habs.trans (BiotSavartConstruction.abs_frequency_le k i)

def poissonCoeff (g : R2 → ℝ) (k : Fin 2 → ℤ) : ℂ :=
  -physicalCoeff g k / (frequencySq k : ℂ)

lemma norm_poissonCoeff_le (g : R2 → ℝ) (k : Fin 2 → ℤ) :
    ‖poissonCoeff g k‖ ≤ ‖physicalCoeff g k‖ := by
  by_cases hk : k = 0
  · subst k
    simp [poissonCoeff, frequencySq]
  · have hq := one_le_frequencySq hk
    rw [poissonCoeff, norm_div, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (frequencySq_nonneg k)]
    exact div_le_self (norm_nonneg _) hq

lemma rapid_poissonCoeff {g : R2 → ℝ} (hg : IsScalarTest g) :
    RapidCoefficients (poissonCoeff g) := by
  intro n
  apply Summable.of_nonneg_of_le (fun k => by have := frequencySq_nonneg k; positivity) _
    (rapid_physicalCoeff hg n)
  intro k
  exact mul_le_mul_of_nonneg_right (norm_poissonCoeff_le g k)
    (by have := frequencySq_nonneg k; positivity)

lemma laplace_coeff (a : (Fin 2 → ℤ) → ℂ) (k : Fin 2 → ℤ) :
    coeffDerivative 0 (coeffDerivative 0 a) k + coeffDerivative 1 (coeffDerivative 1 a) k =
      -(frequencySq k : ℂ) * a k := by
  simp only [coeffDerivative, frequencySq, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_intCast]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma physicalCoeff_zero {g : R2 → ℝ} (hg : (∫ x in torusBox, g x) = 0) :
    physicalCoeff g 0 = 0 := by
  simp [physicalCoeff, boxFourierCoeff, boxFourierPhase_apply, hg]
  rfl

lemma laplace_poissonCoeff {g : R2 → ℝ} (hg : (∫ x in torusBox, g x) = 0)
    (k : Fin 2 → ℤ) :
    coeffDerivative 0 (coeffDerivative 0 (poissonCoeff g)) k +
      coeffDerivative 1 (coeffDerivative 1 (poissonCoeff g)) k = physicalCoeff g k := by
  rw [laplace_coeff]
  by_cases hk : k = 0
  · subst k
    simp [frequencySq, physicalCoeff_zero hg]
  · have hz : (frequencySq k : ℂ) ≠ 0 := by
      exact_mod_cast (BiotSavartConstruction.frequencySq_eq_zero_iff k).not.mpr hk
    rw [poissonCoeff]
    field_simp

lemma laplace_modeSeries {a : (Fin 2 → ℤ) → ℂ} (ha : RapidCoefficients a) (x : R2) :
    pd 0 (pd 0 (modeSeries a)) x + pd 1 (pd 1 (modeSeries a)) x =
      modeSeries (fun k => coeffDerivative 0 (coeffDerivative 0 a) k +
        coeffDerivative 1 (coeffDerivative 1 a) k) x := by
  have h₀ : pd 0 (modeSeries a) = modeSeries (coeffDerivative 0 a) :=
    funext fun y => pd_modeSeries ha 0 y
  have h₁ : pd 1 (modeSeries a) = modeSeries (coeffDerivative 1 a) :=
    funext fun y => pd_modeSeries ha 1 y
  rw [h₀, h₁, pd_modeSeries (ha.derivative 0), pd_modeSeries (ha.derivative 1)]
  unfold modeSeries
  rw [← (summable_modes ((ha.derivative 0).derivative 0) x).tsum_add
    (summable_modes ((ha.derivative 1).derivative 1) x)]
  exact tsum_congr fun k => (realFourierMode_add _ _ k x).symm

end SmoothPoissonConstruction

open SmoothPoissonConstruction

/-- An explicit inverse Laplace series, with zero frequency set to zero. -/
def smoothPoisson (g : R2 → ℝ) : R2 → ℝ :=
  modeSeries (poissonCoeff g)

theorem smoothPoisson_smooth {g : R2 → ℝ} (hg : IsScalarTest g) :
    ContDiff ℝ ∞ (smoothPoisson g) :=
  modeSeries_smooth (rapid_poissonCoeff hg)

theorem smoothPoisson_periodic (g : R2 → ℝ) : IsTorusPeriodic (smoothPoisson g) :=
  modeSeries_periodic _

/-- The actual, globally pointwise Poisson equation for smooth periodic
zero-mean forcing in the physical period-`2π` coordinates. -/
theorem laplacian_smoothPoisson {g : R2 → ℝ} (hg : IsScalarTest g)
    (hmean : (∫ x in torusBox, g x) = 0) (x : R2) :
    pd 0 (pd 0 (smoothPoisson g)) x + pd 1 (pd 1 (smoothPoisson g)) x = g x := by
  change pd 0 (pd 0 (modeSeries (poissonCoeff g))) x +
    pd 1 (pd 1 (modeSeries (poissonCoeff g))) x = g x
  rw [laplace_modeSeries (rapid_poissonCoeff hg) x]
  have heq : (fun k => coeffDerivative 0 (coeffDerivative 0 (poissonCoeff g)) k +
      coeffDerivative 1 (coeffDerivative 1 (poissonCoeff g)) k) = physicalCoeff g :=
    funext fun k => laplace_poissonCoeff hmean k
  rw [heq, modeSeries_physicalCoeff hg]

theorem smoothPoisson_spec {g : R2 → ℝ} (hg : IsScalarTest g)
    (hmean : (∫ x in torusBox, g x) = 0) :
    ContDiff ℝ ∞ (smoothPoisson g) ∧ IsTorusPeriodic (smoothPoisson g) ∧
      ∀ x, pd 0 (pd 0 (smoothPoisson g)) x + pd 1 (pd 1 (smoothPoisson g)) x = g x :=
  ⟨smoothPoisson_smooth hg, smoothPoisson_periodic g, laplacian_smoothPoisson hg hmean⟩

theorem exists_smooth_periodic_poisson {g : R2 → ℝ} (hg : IsScalarTest g)
    (hmean : (∫ x in torusBox, g x) = 0) :
    ∃ H : R2 → ℝ, IsScalarTest H ∧
      ∀ x, pd 0 (pd 0 H) x + pd 1 (pd 1 H) x = g x :=
  ⟨smoothPoisson g, ⟨smoothPoisson_smooth hg, smoothPoisson_periodic g⟩,
    laplacian_smoothPoisson hg hmean⟩

end Euler2D

end
