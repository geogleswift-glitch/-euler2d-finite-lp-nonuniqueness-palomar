module

public import RequestProject.Euler.ContourFourierModeNorm
public import RequestProject.Euler.ContourFourierUniqueness

/-! Actual bounded Fourier multipliers constructed by operator-norm
summation in the original little space. Their coefficient formulas,
composition and two-sided inverse identities use genuine Fourier uniqueness. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) smoothingLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) smoothingLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def contourFourierModeWeight (γ : ℝ≥0) (n : ℤ) : ℝ :=
  1 + ‖(n : ℂ)‖ + ‖(n : ℂ)‖ ^ 2 * Real.pi ^ (1 - (γ : ℝ))

theorem contourFourierModeWeight_nonneg (γ : ℝ≥0) (n : ℤ) :
    0 ≤ contourFourierModeWeight γ n := by unfold contourFourierModeWeight; positivity

def littleContourFourierTermCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (n : ℤ) (c : ℂ) : LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  (littleContourFourierModeCLM hγ hγ1 n).comp
    (((ContinuousLinearMap.mul ℝ ℂ) c).comp (littleContourFourierCoefficientCLM γ n))

theorem littleContourFourierTermCLM_apply {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (n : ℤ) (c : ℂ) (H : LittleContourSpace γ) :
    littleContourFourierTermCLM hγ hγ1 n c H =
      littleContourFourierMode hγ hγ1 n (c * littleContourFourierCoefficient γ n H) := by
  simp only [littleContourFourierTermCLM, ContinuousLinearMap.comp_apply,
    littleContourFourierModeCLM_apply, littleContourFourierCoefficientCLM_apply,
    ContinuousLinearMap.mul_apply']

theorem norm_littleContourFourierTermCLM_le {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (n : ℤ) (c : ℂ) :
    ‖littleContourFourierTermCLM hγ hγ1 n c‖ ≤ contourFourierModeWeight γ n * ‖c‖ := by
  apply (littleContourFourierTermCLM hγ hγ1 n c).opNorm_le_bound
    (mul_nonneg (contourFourierModeWeight_nonneg γ n) (norm_nonneg c))
  intro H
  rw [littleContourFourierTermCLM_apply]
  calc
    _ ≤ contourFourierModeWeight γ n * ‖c * littleContourFourierCoefficient γ n H‖ :=
      norm_littleContourFourierMode_le hγ hγ1 n _
    _ ≤ contourFourierModeWeight γ n * (‖c‖ * ‖H‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_littleContourFourierCoefficient_le n H) (norm_nonneg c))
        (contourFourierModeWeight_nonneg γ n)
    _ = _ := by
      change contourFourierModeWeight γ n * (‖c‖ * ‖H‖) =
        (contourFourierModeWeight γ n * ‖c‖) * ‖H‖
      exact (mul_assoc _ _ _).symm

theorem summable_littleContourFourierTermCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {c : ℤ → ℂ} (hc : Summable (fun n => contourFourierModeWeight γ n * ‖c n‖)) :
    Summable (fun n => littleContourFourierTermCLM hγ hγ1 n (c n)) :=
  hc.of_norm_bounded (fun n => norm_littleContourFourierTermCLM_le hγ hγ1 n (c n))

def littleContourFourierMultiplierCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (c : ℤ → ℂ) : LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  ∑' n : ℤ, littleContourFourierTermCLM hγ hγ1 n (c n)

theorem norm_littleContourFourierMultiplierCLM_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {c : ℤ → ℂ}
    (hc : Summable (fun n => contourFourierModeWeight γ n * ‖c n‖)) :
    ‖littleContourFourierMultiplierCLM hγ hγ1 c‖ ≤
      ∑' n : ℤ, contourFourierModeWeight γ n * ‖c n‖ :=
  tsum_of_norm_bounded hc.hasSum (fun n => norm_littleContourFourierTermCLM_le hγ hγ1 n (c n))

theorem littleContourFourierCoefficient_term {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (k n : ℤ) (c : ℂ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficient γ k (littleContourFourierTermCLM hγ hγ1 n c H) =
      if n = k then c * littleContourFourierCoefficient γ n H else 0 := by
  rw [littleContourFourierTermCLM_apply, littleContourFourierCoefficient_fourierMode]

set_option maxHeartbeats 600000 in
theorem littleContourFourierCoefficient_multiplier {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {c : ℤ → ℂ}
    (hc : Summable (fun n => contourFourierModeWeight γ n * ‖c n‖))
    (H : LittleContourSpace γ) (k : ℤ) :
    littleContourFourierCoefficient γ k (littleContourFourierMultiplierCLM hγ hγ1 c H) =
      c k * littleContourFourierCoefficient γ k H := by
  have hs := summable_littleContourFourierTermCLM hγ hγ1 hc
  let ev : (LittleContourSpace γ →L[ℝ] LittleContourSpace γ) →L[ℝ] LittleContourSpace γ :=
    ContinuousLinearMap.apply ℝ (LittleContourSpace γ) H
  have hv : Summable (fun n => littleContourFourierTermCLM hγ hγ1 n (c n) H) :=
    (ev.hasSum hs.hasSum).summable
  change littleContourFourierCoefficientCLM γ k
    (ev (∑' n, littleContourFourierTermCLM hγ hγ1 n (c n))) = _
  rw [ev.map_tsum hs]
  change littleContourFourierCoefficientCLM γ k
    (∑' n, littleContourFourierTermCLM hγ hγ1 n (c n) H) = _
  rw [(littleContourFourierCoefficientCLM γ k).map_tsum hv]
  simp only [littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_term]
  simp

set_option maxHeartbeats 600000 in
theorem littleContourFourierMultiplier_comp {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {c d : ℤ → ℂ}
    (hc : Summable (fun n => contourFourierModeWeight γ n * ‖c n‖))
    (hd : Summable (fun n => contourFourierModeWeight γ n * ‖d n‖))
    (hcd : Summable (fun n => contourFourierModeWeight γ n * ‖c n * d n‖)) :
    (littleContourFourierMultiplierCLM hγ hγ1 c).comp (littleContourFourierMultiplierCLM hγ hγ1 d) =
      littleContourFourierMultiplierCLM hγ hγ1 (fun n => c n * d n) := by
  apply ContinuousLinearMap.ext
  intro H
  apply littleContourFourierCoefficient_ext
  intro k
  change littleContourFourierCoefficient γ k
      (littleContourFourierMultiplierCLM hγ hγ1 c (littleContourFourierMultiplierCLM hγ hγ1 d H)) = _
  rw [littleContourFourierCoefficient_multiplier hγ hγ1 hc,
    littleContourFourierCoefficient_multiplier hγ hγ1 hd,
    littleContourFourierCoefficient_multiplier hγ hγ1 hcd]
  ring

def littleContourAffineFourierMultiplierCLM {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (a : ℝ) (c : ℤ → ℂ) :
    LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  a • ContinuousLinearMap.id ℝ (LittleContourSpace γ) + littleContourFourierMultiplierCLM hγ hγ1 c

theorem littleContourFourierCoefficient_affineMultiplier {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (a : ℝ) {c : ℤ → ℂ}
    (hc : Summable (fun n => contourFourierModeWeight γ n * ‖c n‖))
    (H : LittleContourSpace γ) (k : ℤ) :
    littleContourFourierCoefficient γ k (littleContourAffineFourierMultiplierCLM hγ hγ1 a c H) =
      ((a : ℂ) + c k) * littleContourFourierCoefficient γ k H := by
  change littleContourFourierCoefficientCLM γ k
      (a • H + littleContourFourierMultiplierCLM hγ hγ1 c H) = _
  rw [map_add, map_smul, littleContourFourierCoefficientCLM_apply,
    littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_multiplier hγ hγ1 hc]
  rw [Complex.real_smul]
  ring

set_option maxHeartbeats 600000 in
theorem littleContourAffineFourierMultiplier_comp_eq_id {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (a b : ℝ) {c d : ℤ → ℂ}
    (hc : Summable (fun n => contourFourierModeWeight γ n * ‖c n‖))
    (hd : Summable (fun n => contourFourierModeWeight γ n * ‖d n‖))
    (hinv : ∀ n, ((a : ℂ) + c n) * ((b : ℂ) + d n) = 1) :
    (littleContourAffineFourierMultiplierCLM hγ hγ1 a c).comp
        (littleContourAffineFourierMultiplierCLM hγ hγ1 b d) =
      ContinuousLinearMap.id ℝ (LittleContourSpace γ) := by
  apply ContinuousLinearMap.ext
  intro H
  apply littleContourFourierCoefficient_ext
  intro k
  change littleContourFourierCoefficient γ k
    (littleContourAffineFourierMultiplierCLM hγ hγ1 a c
      (littleContourAffineFourierMultiplierCLM hγ hγ1 b d H)) = littleContourFourierCoefficient γ k H
  rw [littleContourFourierCoefficient_affineMultiplier hγ hγ1 a hc,
    littleContourFourierCoefficient_affineMultiplier hγ hγ1 b hd, ← mul_assoc, hinv k, one_mul]

theorem littleContourAffineFourierMultiplier_two_sided_inverse {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (a b : ℝ) {c d : ℤ → ℂ}
    (hc : Summable (fun n => contourFourierModeWeight γ n * ‖c n‖))
    (hd : Summable (fun n => contourFourierModeWeight γ n * ‖d n‖))
    (hinv : ∀ n, ((a : ℂ) + c n) * ((b : ℂ) + d n) = 1) :
    (littleContourAffineFourierMultiplierCLM hγ hγ1 a c).comp
        (littleContourAffineFourierMultiplierCLM hγ hγ1 b d) = ContinuousLinearMap.id ℝ (LittleContourSpace γ) ∧
    (littleContourAffineFourierMultiplierCLM hγ hγ1 b d).comp
        (littleContourAffineFourierMultiplierCLM hγ hγ1 a c) = ContinuousLinearMap.id ℝ (LittleContourSpace γ) := by
  exact ⟨littleContourAffineFourierMultiplier_comp_eq_id hγ hγ1 a b hc hd hinv,
    littleContourAffineFourierMultiplier_comp_eq_id hγ hγ1 b a hd hc
      (fun n => by rw [mul_comm]; exact hinv n)⟩

end Euler2D

end
