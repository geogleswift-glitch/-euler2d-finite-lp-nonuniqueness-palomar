module

public import RequestProject.Euler.ContourCircularFieldModes
public import RequestProject.Euler.ContourRotationLittle
public import RequestProject.Euler.ContourBanachAreaChart

/-! Actual Fourier perturbations lie in the original closed fourfold
subspace and in the genuine linear tangent space of the fixed-area chart. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) fourierConstraintLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fourierConstraintLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem contourCircleCharacter_quarter_of_four_dvd {k : ℤ} (hk : 4 ∣ k) :
    contourCircleCharacter k (Real.pi / 2) = 1 := by
  obtain ⟨q, rfl⟩ := hk
  unfold contourCircleCharacter
  have he : ((4 * q : ℤ) : ℂ) * ((Real.pi / 2 : ℝ) : ℂ) * I =
      (q : ℂ) * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [he]
  exact exp_int_mul_two_pi_mul_I q

theorem refCircle_quarter_shift (r θ : ℝ) :
    refCircle r (θ + Real.pi / 2) = I * refCircle r θ := by
  unfold refCircle
  rw [Complex.ofReal_add, add_mul, exp_add]
  have he : exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
    push_cast
    exact exp_pi_div_two_mul_I
  rw [he]
  ring

theorem littleReferenceCircle_mem_fourfold {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) :
    littleReferenceCircle hγ hγ1 r ∈ fourfoldLittleContourSubmodule γ := by
  rw [mem_fourfoldLittleContourSubmodule]
  intro θ
  simp only [lift_littleReferenceCircle]
  exact refCircle_quarter_shift r θ

theorem circularNormalModeLittle_mem_fourfold {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (hN : 4 ∣ N + 2)
    (η τ : Fin 2 → ℂ) (i : Fin 2) :
    circularNormalModeLittle hγ hγ1 N η τ i ∈ fourfoldLittleContourSubmodule γ := by
  rw [mem_fourfoldLittleContourSubmodule]
  intro θ
  have hk : (4 : ℤ) ∣ ((N + 2 : ℕ) : ℤ) := by exact_mod_cast hN
  simp only [lift_circularNormalModeLittle, refCircle_quarter_shift,
    contourCircleCharacter_add_arg, contourCircleCharacter_quarter_of_four_dvd hk, mul_one]
  ring

theorem littleContourEllCLM_fourierMode_eq_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) (n : ℤ) (hn : n ≠ 1) (a : ℂ) :
    littleContourEllCLM γ r (littleContourFourierMode hγ hγ1 n a) = 0 := by
  rw [littleContourEllCLM_eq_ellFun]
  change r * (∫ θ in (0 : ℝ)..2 * Real.pi,
    (exp (-((θ : ℂ) * I)) * (a * contourCircleCharacter n θ)).re) = 0
  have he (θ : ℝ) : exp (-((θ : ℂ) * I)) * (a * contourCircleCharacter n θ) =
      a * contourCircleCharacter (n - 1) θ := by
    have hm : exp (-((θ : ℂ) * I)) = contourCircleCharacter (-1) θ := by
      simp only [contourCircleCharacter, Int.cast_neg, Int.cast_one, neg_one_mul]
      congr 1
      ring
    rw [hm]
    calc
      contourCircleCharacter (-1) θ * (a * contourCircleCharacter n θ) =
          a * (contourCircleCharacter (-1) θ * contourCircleCharacter n θ) := by ring
      _ = _ := by rw [contourCircleCharacter_mul]; congr 2; ring
  simp_rw [he]
  have hi : IntervalIntegrable (fun θ : ℝ => a * contourCircleCharacter (n - 1) θ)
      volume 0 (2 * Real.pi) :=
    (continuous_const.mul (continuous_contourCircleCharacter (n - 1))).intervalIntegrable _ _
  have hre := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ θ in (0 : ℝ)..2 * Real.pi, (a * contourCircleCharacter (n - 1) θ).re) =
    (∫ θ in (0 : ℝ)..2 * Real.pi, a * contourCircleCharacter (n - 1) θ).re at hre
  rw [hre, intervalIntegral.integral_const_mul, integral_contourCircleCharacter,
    if_neg (sub_ne_zero.mpr hn), mul_zero, Complex.zero_re, mul_zero]

theorem littleContourEllCLM_circularNormalModeLittle {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2)
    (r : ℝ) :
    littleContourEllCLM γ r (circularNormalModeLittle hγ hγ1 N η τ i) = 0 := by
  unfold circularNormalModeLittle
  rw [map_add,
    littleContourEllCLM_fourierMode_eq_zero hγ hγ1 r ((N + 3 : ℕ) : ℤ) (by omega),
    littleContourEllCLM_fourierMode_eq_zero hγ hγ1 r (-((N + 1 : ℕ) : ℤ)) (by omega),
    add_zero]

theorem circularNormalModeLittle_mem_areaConstraint {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    circularNormalModeLittle hγ hγ1 N η τ i ∈
      LittleContourAreaConstraint γ (circularContourRadii i) :=
  littleContourEllCLM_circularNormalModeLittle hγ hγ1 N η τ i (circularContourRadii i)

theorem circularNormalModeLittle_mem_fourfold_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (hN : 4 ∣ N + 2)
    (η τ : Fin 2 → ℂ) (i : Fin 2) :
    circularNormalModeLittle hγ hγ1 N η τ i ∈
      fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i) :=
  ⟨circularNormalModeLittle_mem_fourfold hγ hγ1 N hN η τ i,
    circularNormalModeLittle_mem_areaConstraint hγ hγ1 N η τ i⟩

theorem circularFourthModeLittle_mem_fourfold_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    circularNormalModeLittle hγ hγ1 2 η τ i ∈
      fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i) :=
  circularNormalModeLittle_mem_fourfold_area hγ hγ1 2 (by decide) η τ i

theorem littleAreaChart_mem_fourfold {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (r : ℝ) (v : LittleContourSpace γ) (hv : v ∈ fourfoldLittleContourSubmodule γ) :
    littleAreaChart hγ hγ1 r v ∈ fourfoldLittleContourSubmodule γ :=
  (fourfoldLittleContourSubmodule γ).add_mem
    ((fourfoldLittleContourSubmodule γ).smul_mem _ (littleReferenceCircle_mem_fourfold hγ hγ1 r)) hv

end Euler2D

end
