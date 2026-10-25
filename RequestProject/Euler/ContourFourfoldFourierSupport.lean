module

public import RequestProject.Euler.CircularFourierOperatorBounds

/-! The original fourfold constraint forces the actual Fourier
coefficients to vanish away from contour frequencies congruent to one
modulo four. In particular no additional low unstable blocks occur. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) fourfoldSupportLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fourfoldSupportLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem contourCircleCharacter_quarter_eq_one_iff (k : ℤ) :
    contourCircleCharacter k (Real.pi / 2) = 1 ↔ (4 : ℤ) ∣ k := by
  rw [contourCircleCharacter, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨z, hz⟩
    have hi := congrArg Complex.im hz
    norm_num [Complex.mul_im] at hi
    have hk : (k : ℝ) = 4 * (z : ℝ) := by
      apply mul_right_cancel₀ Real.pi_ne_zero
      nlinarith
    refine ⟨z, ?_⟩
    exact_mod_cast hk
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    push_cast
    ring

theorem littleContourFourierCoefficient_fourfold_eq_zero {γ : ℝ≥0}
    {H : LittleContourSpace γ} (hH : H ∈ fourfoldLittleContourSubmodule γ)
    (k : ℤ) (hk : ¬(4 : ℤ) ∣ 1 - k) : littleContourFourierCoefficient γ k H = 0 := by
  have hr : contourRotationLittleCLM γ (Real.pi / 2) H = H := by
    change contourRotationLittleCLM γ (Real.pi / 2) H - H = 0 at hH
    exact sub_eq_zero.mp hH
  have he := congrArg (littleContourFourierCoefficient γ k) hr
  rw [littleContourFourierCoefficient_rotation] at he
  have hn : contourCircleCharacter (1 - k) (Real.pi / 2) - 1 ≠ 0 :=
    sub_ne_zero.mpr (fun h => hk ((contourCircleCharacter_quarter_eq_one_iff (1 - k)).mp h))
  have hz : (contourCircleCharacter (1 - k) (Real.pi / 2) - 1) *
      littleContourFourierCoefficient γ k H = 0 := by
    rw [sub_mul, one_mul, he, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left hn

theorem circularModeAmplitudeCoefficient_fourfold_eq_zero {γ : ℝ≥0}
    (H : Fin 2 → LittleContourSpace γ) (hH : ∀ i, H i ∈ fourfoldLittleContourSubmodule γ)
    (N : ℕ) (hN : ¬(4 : ℤ) ∣ ((N + 2 : ℕ) : ℤ)) :
    circularModeAmplitudeCoefficientCLM γ N H = 0 := by
  have hp (i : Fin 2) : littleContourFourierCoefficient γ ((N + 3 : ℕ) : ℤ) (H i) = 0 := by
    apply littleContourFourierCoefficient_fourfold_eq_zero (hH i)
    rwa [show (1 : ℤ) - ((N + 3 : ℕ) : ℤ) = -((N + 2 : ℕ) : ℤ) by omega, dvd_neg]
  have hn (i : Fin 2) : littleContourFourierCoefficient γ (-((N + 1 : ℕ) : ℤ)) (H i) = 0 := by
    apply littleContourFourierCoefficient_fourfold_eq_zero (hH i)
    rwa [show (1 : ℤ) - -((N + 1 : ℕ) : ℤ) = ((N + 2 : ℕ) : ℤ) by omega]
  apply Prod.ext
  · funext i
    change littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N (H i) = 0
    rw [littleContourModeNormalCoefficientCLM_apply, hp, hn]
    simp
  · funext i
    change littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N (H i) = 0
    rw [littleContourModeTangentCoefficientCLM_apply, hp, hn]
    simp

theorem circularModeAmplitudeCoefficient_low_fourfold_eq_zero {γ : ℝ≥0}
    (H : Fin 2 → LittleContourSpace γ) (hH : ∀ i, H i ∈ fourfoldLittleContourSubmodule γ)
    {N : ℕ} (hN : N < 6) (hN2 : N ≠ 2) : circularModeAmplitudeCoefficientCLM γ N H = 0 :=
  circularModeAmplitudeCoefficient_fourfold_eq_zero H hH N (by omega)

end Euler2D

end
