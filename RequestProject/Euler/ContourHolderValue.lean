module

public import RequestProject.Euler.ContourNormalizedChord
public import RequestProject.Euler.ContourSmoothEmbedding
public import RequestProject.Euler.ContourHolderScalar

/-! # Actual value, constant, and real-part maps in contour Hölder spaces -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

def contourValueHolderConstant (γ : ℝ) : ℝ := 1 + Real.pi ^ (1 - γ)

theorem contourValueHolderConstant_pos (γ : ℝ) : 0 < contourValueHolderConstant γ := by
  unfold contourValueHolderConstant
  positivity

theorem contour_dist_le_holder_power {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (x y : ContourCircle) :
    dist x y ≤ Real.pi ^ (1 - (γ : ℝ)) * dist x y ^ (γ : ℝ) := by
  by_cases hd : dist x y = 0
  · rw [hd]
    positivity
  have hdp : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
  calc
    dist x y = dist x y ^ (1 - (γ : ℝ)) * dist x y ^ (γ : ℝ) := by
      rw [← Real.rpow_add hdp, sub_add_cancel, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow dist_nonneg (contour_dist_le_pi x y) (sub_nonneg.mpr hγ1))
      (Real.rpow_nonneg dist_nonneg _)

theorem holderWith_contourC1_value {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) (Z : ContourC1Space γ) :
    HolderWith (⟨Real.pi ^ (1 - (γ : ℝ)) * ‖Z‖, by positivity⟩ : ℝ≥0) γ
      (fun x => ContourC1Space.toBCF γ Z x) := by
  have hl : LipschitzWith ‖Z‖₊ (fun x => ContourC1Space.toBCF γ Z x) :=
    lipschitzWith_contour_of_deriv_bound (ContourC1Space.contDiff_lift Z)
      (ContourC1Space.norm_deriv_lift_le Z)
  apply contour_holderWith_of_norm_bound (by positivity)
  intro x y
  have hb : ‖ContourC1Space.toBCF γ Z x - ContourC1Space.toBCF γ Z y‖ ≤ ‖Z‖ * dist x y := by
    simpa only [dist_eq_norm] using hl.dist_le_mul x y
  exact (hb.trans (mul_le_mul_of_nonneg_left (contour_dist_le_holder_power hγ1 x y)
    (norm_nonneg _))).trans_eq (by ring)

def contourC1ValueHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) (Z : ContourC1Space γ) :
    ContourHolderSpace γ :=
  HolderFunctionSpace.ofMemHolder (ContourC1Space.toBCF γ Z) (holderWith_contourC1_value hγ1 Z).memHolder

@[simp] theorem contourC1ValueHolder_apply {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z : ContourC1Space γ) (x : ContourCircle) :
    contourC1ValueHolder hγ1 Z x = ContourC1Space.toBCF γ Z x := rfl

theorem norm_contourC1ValueHolder_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) (Z : ContourC1Space γ) :
    ‖contourC1ValueHolder hγ1 Z‖ ≤ contourValueHolderConstant (γ : ℝ) * ‖Z‖ := by
  have hD : 1 ≤ contourValueHolderConstant (γ : ℝ) := by
    unfold contourValueHolderConstant
    exact le_add_of_nonneg_right (Real.rpow_nonneg Real.pi_pos.le _)
  have hP : Real.pi ^ (1 - (γ : ℝ)) ≤ contourValueHolderConstant (γ : ℝ) := by
    unfold contourValueHolderConstant
    linarith
  apply norm_contourHolder_le_of_bounds _ (mul_nonneg (zero_le_one.trans hD) (norm_nonneg Z))
  · intro x
    have hn : ‖Z‖ ≤ contourValueHolderConstant (γ : ℝ) * ‖Z‖ := by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hD (norm_nonneg Z))
    exact (ContourC1Space.norm_eval_le Z x).trans hn
  · intro x y
    have hb : ‖ContourC1Space.toBCF γ Z x - ContourC1Space.toBCF γ Z y‖ ≤
        (Real.pi ^ (1 - (γ : ℝ)) * ‖Z‖) * dist x y ^ (γ : ℝ) := by
      simpa only [dist_eq_norm] using (holderWith_contourC1_value hγ1 Z).dist_le x y
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
      (Real.rpow_nonneg dist_nonneg _))

theorem contourC1ValueHolder_sub {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) (Z W : ContourC1Space γ) :
    contourC1ValueHolder hγ1 (Z - W) = contourC1ValueHolder hγ1 Z - contourC1ValueHolder hγ1 W := by
  apply HolderFunctionSpace.ext
  intro x
  rfl

theorem norm_contourC1ValueHolder_sub_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) (Z W : ContourC1Space γ) :
    ‖contourC1ValueHolder hγ1 Z - contourC1ValueHolder hγ1 W‖ ≤
      contourValueHolderConstant (γ : ℝ) * ‖Z - W‖ := by
  rw [← contourC1ValueHolder_sub]
  exact norm_contourC1ValueHolder_le hγ1 (Z - W)

def contourHolderConstantCLM (γ : ℝ≥0) : ℂ →L[ℝ] ContourHolderSpace γ :=
  ({ toFun := HolderFunctionSpace.const γ
     map_add' := fun a b => by apply HolderFunctionSpace.ext; intro x; rfl
     map_smul' := fun a b => by apply HolderFunctionSpace.ext; intro x; rfl } :
      ℂ →ₗ[ℝ] ContourHolderSpace γ).mkContinuous 1
    (fun a => by simpa only [one_mul] using HolderFunctionSpace.norm_const_le (γ := γ) a)

@[simp] theorem contourHolderConstantCLM_apply (γ : ℝ≥0) (a : ℂ) (x : ContourCircle) :
    contourHolderConstantCLM γ a x = a := rfl

theorem norm_complexRealPart_le (a : ℂ) : ‖(a.re : ℂ)‖ ≤ ‖a‖ := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm a

def contourHolderRealPart {γ : ℝ≥0} (f : ContourHolderSpace γ) : ContourHolderSpace γ :=
  HolderFunctionSpace.ofMemHolder
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun x => ((f x).re : ℂ), Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (HolderFunctionSpace.toBCF γ f).continuous)⟩)
    (contour_holderWith_of_norm_bound (norm_nonneg f) (fun x y => by
      have he : ((f x).re : ℂ) - ((f y).re : ℂ) = ((f x - f y).re : ℂ) := by simp
      change ‖((f x).re : ℂ) - ((f y).re : ℂ)‖ ≤ _
      rw [he]
      exact (norm_complexRealPart_le _).trans (HolderFunctionSpace.norm_sub_le_holder f x y))).memHolder

@[simp] theorem contourHolderRealPart_apply {γ : ℝ≥0} (f : ContourHolderSpace γ) (x : ContourCircle) :
    contourHolderRealPart f x = ((f x).re : ℂ) := rfl

theorem norm_contourHolderRealPart_le {γ : ℝ≥0} (f : ContourHolderSpace γ) :
    ‖contourHolderRealPart f‖ ≤ ‖f‖ := by
  apply norm_contourHolder_le_of_bounds _ (norm_nonneg f)
  · intro x
    exact (norm_complexRealPart_le _).trans (HolderFunctionSpace.norm_eval_le f x)
  · intro x y
    have he : ((f x).re : ℂ) - ((f y).re : ℂ) = ((f x - f y).re : ℂ) := by simp
    change ‖((f x).re : ℂ) - ((f y).re : ℂ)‖ ≤ _
    rw [he]
    exact (norm_complexRealPart_le _).trans (HolderFunctionSpace.norm_sub_le_holder f x y)

def contourHolderRealPartCLM (γ : ℝ≥0) : ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ :=
  ({ toFun := contourHolderRealPart
     map_add' := fun f g => by
       apply HolderFunctionSpace.ext
       intro x
       change (((f x + g x).re : ℝ) : ℂ) = ((f x).re : ℂ) + ((g x).re : ℂ)
       simp
     map_smul' := fun a f => by
       apply HolderFunctionSpace.ext
       intro x
       change (((a • f x).re : ℝ) : ℂ) = a • ((f x).re : ℂ)
       simp [Complex.real_smul] } : ContourHolderSpace γ →ₗ[ℝ] ContourHolderSpace γ).mkContinuous 1
    (fun f => by simpa only [one_mul] using norm_contourHolderRealPart_le f)

@[simp] theorem contourHolderRealPartCLM_apply {γ : ℝ≥0} (f : ContourHolderSpace γ) (x : ContourCircle) :
    contourHolderRealPartCLM γ f x = ((f x).re : ℂ) := rfl

end Euler2D

end
