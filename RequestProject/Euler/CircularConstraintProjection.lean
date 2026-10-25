module

public import RequestProject.Euler.CircularAreaChartInverse

/-! Genuine bounded projections onto the simultaneous original
fourfold and linear area constraints, for nonlinear return coordinates. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) constraintProjectLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) constraintProjectLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem contourRotationLittleCLM_two_pi {γ : ℝ≥0} (Z : LittleContourSpace γ) :
    contourRotationLittleCLM γ (2 * Real.pi) Z = Z := by
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (contourRotationLittleCLM γ (2 * Real.pi) Z) θ =
    LittleContourSpace.lift γ Z θ
  rw [lift_contourRotationLittleCLM]
  change exp (((2 * Real.pi : ℝ) : ℂ) * I) * LittleContourSpace.lift γ Z (θ - 2 * Real.pi) = _
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I, one_mul]
  simpa only [sub_add_cancel] using (LittleContourSpace.periodic_lift Z (θ - 2 * Real.pi)).symm

theorem contourQuarterRotation_pow_four (γ : ℝ≥0) :
    (contourRotationLittleCLM γ (Real.pi / 2)) ^ 4 = 1 := by
  apply ContinuousLinearMap.ext
  intro Z
  change contourRotationLittleCLM γ (Real.pi / 2)
    (contourRotationLittleCLM γ (Real.pi / 2)
      (contourRotationLittleCLM γ (Real.pi / 2) (contourRotationLittleCLM γ (Real.pi / 2) Z))) = Z
  rw [contourRotationLittleCLM_add, contourRotationLittleCLM_add, contourRotationLittleCLM_add]
  have he : Real.pi / 2 + Real.pi / 2 + Real.pi / 2 + Real.pi / 2 = 2 * Real.pi := by ring
  rw [he]
  exact contourRotationLittleCLM_two_pi Z

def littleFourfoldProjectionCLM (γ : ℝ≥0) : LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  (1 / 4 : ℝ) • (1 + contourRotationLittleCLM γ (Real.pi / 2) +
    (contourRotationLittleCLM γ (Real.pi / 2)) ^ 2 +
      (contourRotationLittleCLM γ (Real.pi / 2)) ^ 3)

theorem littleFourfoldProjectionCLM_mem {γ : ℝ≥0} (Z : LittleContourSpace γ) :
    littleFourfoldProjectionCLM γ Z ∈ fourfoldLittleContourSubmodule γ := by
  let R := contourRotationLittleCLM γ (Real.pi / 2)
  let S := (1 : LittleContourSpace γ →L[ℝ] LittleContourSpace γ) + R + R ^ 2 + R ^ 3
  have hR : R ^ 4 = 1 := contourQuarterRotation_pow_four γ
  have he : R * S = S := by
    dsimp only [S]
    calc
      _ = R + R ^ 2 + R ^ 3 + R ^ 4 := by noncomm_ring
      _ = _ := by rw [hR]; noncomm_ring
  have heZ : R (S Z) = S Z := congrArg (fun A : LittleContourSpace γ →L[ℝ] LittleContourSpace γ => A Z) he
  change R ((1 / 4 : ℝ) • S Z) - (1 / 4 : ℝ) • S Z = 0
  have hs : R ((1 / 4 : ℝ) • S Z) = (1 / 4 : ℝ) • R (S Z) :=
    R.toLinearMap.map_smul' (1 / 4 : ℝ) (S Z)
  rw [hs, heZ, sub_self]

theorem littleFourfoldProjectionCLM_of_mem {γ : ℝ≥0} (Z : LittleContourSpace γ)
    (hZ : Z ∈ fourfoldLittleContourSubmodule γ) : littleFourfoldProjectionCLM γ Z = Z := by
  let R := contourRotationLittleCLM γ (Real.pi / 2)
  have hz : R Z = Z := by change _ - Z = 0 at hZ; exact sub_eq_zero.mp hZ
  have h2 : (R ^ 2) Z = Z := by
    change R (R Z) = Z
    rw [hz, hz]
  have h3 : (R ^ 3) Z = Z := by
    change R (R (R Z)) = Z
    rw [hz, hz, hz]
  change (1 / 4 : ℝ) • (((1 : LittleContourSpace γ →L[ℝ] LittleContourSpace γ) + R + R ^ 2 + R ^ 3) Z) = Z
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, hz, h2, h3]
  module

def littleFourfoldAreaProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) :
    LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  (littleAreaTangentProjection hγ hγ1 r).comp (littleFourfoldProjectionCLM γ)

theorem littleFourfoldAreaProjectionCLM_mem {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {r : ℝ} (hr : r ≠ 0) (Z : LittleContourSpace γ) :
    littleFourfoldAreaProjectionCLM hγ hγ1 r Z ∈
      fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ r :=
  ⟨littleAreaTangentProjection_fourfold hγ hγ1 r _ (littleFourfoldProjectionCLM_mem Z),
    littleAreaTangentProjection_ell_zero hγ hγ1 hr _⟩

theorem littleFourfoldAreaProjectionCLM_of_mem {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (r : ℝ) (Z : LittleContourSpace γ)
    (hZ : Z ∈ fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ r) :
    littleFourfoldAreaProjectionCLM hγ hγ1 r Z = Z := by
  change littleAreaTangentProjection hγ hγ1 r (littleFourfoldProjectionCLM γ Z) = Z
  rw [littleFourfoldProjectionCLM_of_mem Z hZ.1]
  exact littleAreaTangentProjection_of_ell_zero hγ hγ1 r Z hZ.2

def circularConstraintProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  ContinuousLinearMap.pi fun i => (littleFourfoldAreaProjectionCLM hγ hγ1 (circularContourRadii i)).comp
    (ContinuousLinearMap.proj i)

theorem circularConstraintProjectionCLM_mem {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (Z : Fin 2 → LittleContourSpace γ) (i : Fin 2) :
    circularConstraintProjectionCLM hγ hγ1 Z i ∈ fourfoldLittleContourSubmodule γ ⊓
      LittleContourAreaConstraint γ (circularContourRadii i) := by
  apply littleFourfoldAreaProjectionCLM_mem hγ hγ1 _ (Z i)
  fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']

theorem circularConstraintProjectionCLM_of_mem {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (Z : Fin 2 → LittleContourSpace γ)
    (hZ : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ ⊓
      LittleContourAreaConstraint γ (circularContourRadii i)) :
    circularConstraintProjectionCLM hγ hγ1 Z = Z := by
  funext i
  exact littleFourfoldAreaProjectionCLM_of_mem hγ hγ1 (circularContourRadii i) (Z i) (hZ i)

end Euler2D

end
