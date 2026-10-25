module

public import RequestProject.Euler.ContourFourierModeCalculus

/-! Polynomial bounds for the actual Fourier embeddings in the
unchanged little C¹ Hölder norm, for infinite smoothing multipliers. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ContDiff ENNReal

namespace Euler2D

local instance (priority := 2000) fourierNormC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) fourierNormC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) fourierNormLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fourierNormLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem norm_contourC1_le_of_uniform_holder_bounds {γ : ℝ≥0} (Z : ContourC1Space γ)
    (A B C : ℝ≥0) (hv : ∀ x, ‖ContourC1Space.toBCF γ Z x‖ ≤ A)
    (hd : ∀ x, ‖ContourC1Space.derivative γ Z x‖ ≤ B)
    (hh : HolderWith C γ (fun x => ContourC1Space.derivative γ Z x)) :
    ‖Z‖ ≤ (A : ℝ) + B + C := by
  have hA : ‖ContourC1Space.toBCF γ Z‖ ≤ A := (BoundedContinuousFunction.norm_le A.coe_nonneg).mpr hv
  have hB : ‖HolderFunctionSpace.toBCF γ (ContourC1Space.derivative γ Z)‖ ≤ B :=
    (BoundedContinuousFunction.norm_le B.coe_nonneg).mpr hd
  have hC : (nnHolderNorm γ (fun x => ContourC1Space.derivative γ Z x) : ℝ) ≤ C := by
    exact_mod_cast hh.nnholderNorm_le
  have hD : ‖ContourC1Space.derivative γ Z‖ ≤ (B : ℝ) + C :=
    (HolderFunctionSpace.norm_le_uniform_add_holder _).trans (add_le_add hB hC)
  change max ‖ContourC1Space.toBCF γ Z‖ ‖ContourC1Space.derivative γ Z‖ ≤ _
  apply max_le <;> linarith [A.coe_nonneg, B.coe_nonneg, C.coe_nonneg]

set_option maxHeartbeats 600000 in
theorem norm_littleContourFourierMode_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ) (a : ℂ) :
    ‖littleContourFourierMode hγ hγ1 n a‖ ≤
      (1 + ‖(n : ℂ)‖ + ‖(n : ℂ)‖ ^ 2 * Real.pi ^ (1 - (γ : ℝ))) * ‖a‖ := by
  let Z : ContourC1Space γ := (littleContourFourierMode hγ hγ1 n a).val
  let A : ℝ≥0 := ‖a‖₊
  let B : ℝ≥0 := ⟨‖a‖ * ‖(n : ℂ)‖, by positivity⟩
  let C : ℝ≥0 := ⟨‖a‖ * ‖(n : ℂ)‖ ^ 2, by positivity⟩
  have he (θ : ℝ) : ContourC1Space.derivative γ Z (θ : ContourCircle) =
      a * ((n : ℂ) * I * contourCircleCharacter n θ) := by
    rw [← ContourC1Space.deriv_lift]
    exact deriv_lift_littleContourFourierMode hγ hγ1 n a θ
  have hv (x : ContourCircle) : ‖ContourC1Space.toBCF γ Z x‖ ≤ A := by
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ‖a * contourCircleCharacter n θ‖ ≤ ‖a‖
    simp only [norm_mul, norm_contourCircleCharacter, mul_one, le_refl]
  have hd (x : ContourCircle) : ‖ContourC1Space.derivative γ Z x‖ ≤ B := by
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [he]
    simp only [norm_mul, norm_I, norm_contourCircleCharacter, mul_one]
    exact le_rfl
  have hl : LipschitzWith C (fun x => ContourC1Space.derivative γ Z x) := by
    apply lipschitzWith_contour_of_deriv_bound
    · have hc : ContDiff ℝ ∞ (fun θ => a * ((n : ℂ) * I * contourCircleCharacter n θ)) :=
        contDiff_const.mul (contDiff_const.mul (contDiff_contourCircleCharacter n))
      simpa only [he] using (hc.of_le (by simp) : ContDiff ℝ 1 _)
    · intro θ
      have hd' := (((hasDerivAt_contourCircleCharacter n θ).const_mul ((n : ℂ) * I)).const_mul a).deriv
      have hf : (fun θ : ℝ => ContourC1Space.derivative γ Z (θ : ContourCircle)) =
          (fun θ => a * ((n : ℂ) * I * contourCircleCharacter n θ)) := funext he
      rw [hf, hd']
      simp only [norm_mul, norm_I, norm_contourCircleCharacter, mul_one]
      change ‖a‖ * (‖(n : ℂ)‖ * ‖(n : ℂ)‖) ≤ ‖a‖ * ‖(n : ℂ)‖ ^ 2
      exact le_of_eq (by ring)
  have hdiam (x y : ContourCircle) : edist x y ≤ (Real.toNNReal Real.pi : ℝ≥0∞) := by
    rw [edist_dist]
    change ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal Real.pi
    exact ENNReal.ofReal_le_ofReal (contour_dist_le_pi x y)
  have hh := hl.holderWith.of_le (D := Real.toNNReal Real.pi) hdiam hγ1
  have hb := norm_contourC1_le_of_uniform_holder_bounds Z A B
    (C * (Real.toNNReal Real.pi) ^ (1 - (γ : ℝ))) hv hd hh
  change ‖Z‖ ≤ _
  convert hb using 1
  simp only [A, B, C, NNReal.coe_mul, NNReal.coe_mk, coe_nnnorm,
    NNReal.coe_rpow, Real.coe_toNNReal _ Real.pi_pos.le]
  ring

set_option maxHeartbeats 600000 in
theorem norm_littleContourFourierModeCLM_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ) :
    ‖littleContourFourierModeCLM hγ hγ1 n‖ ≤
      1 + ‖(n : ℂ)‖ + ‖(n : ℂ)‖ ^ 2 * Real.pi ^ (1 - (γ : ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound (littleContourFourierModeCLM hγ hγ1 n) (by positivity)
  intro a
  rw [littleContourFourierModeCLM_apply]
  exact norm_littleContourFourierMode_le hγ hγ1 n a

end Euler2D

end
