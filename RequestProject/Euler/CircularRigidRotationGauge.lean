module

public import RequestProject.Euler.LittleContourComplexScalar
public import RequestProject.Euler.CircularReferencePhases
public import RequestProject.Euler.ComplexBanachRotatingFrame

/-! The genuine isolated circular Banach field is equivariant under
pure spatial value rotation. Thus a real constant core angular velocity
is removed by an actual Little-valued gauge, with no change of time or
of the original isolated field. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) rigidGaugeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) rigidGaugeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

local instance (priority := 2000) rigidGaugeFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℂ (Fin 2 → LittleContourSpace γ) where
  smul_assoc c a Z := by
    funext i
    change (c • a) • Z i = c • (a • Z i)
    exact smul_assoc _ _ _

theorem complexValueRotationFamily_eq_shift_rotation {γ : ℝ≥0}
    (b : ℝ) (Z : Fin 2 → LittleContourSpace γ) :
    exp ((b : ℂ) * I) • Z = contourParameterShiftFamilyCLM γ (fun _ => b)
      (contourRotationFamilyLittleCLM γ b Z) := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change exp ((b : ℂ) * I) * LittleContourSpace.lift γ (Z i) θ =
    LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ b (contourRotationLittleCLM γ b (Z i))) θ
  simp only [lift_contourParameterShiftLittleCLM, lift_contourRotationLittleCLM, rotShift,
    add_sub_cancel_right]

theorem circularBanachDomain_complexValueRotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (b : ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    exp ((b : ℂ) * I) • Z ∈ circularBanachDomain hγ hγ1 := by
  rw [complexValueRotationFamily_eq_shift_rotation]
  exact circularBanachDomain_parameterShift hγ hγ1 _ (circularBanachDomain_rotation hγ hγ1 b hZ)

theorem circularBanachField_complexValueRotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (b : ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    circularBanachField hγ hγ1 (exp ((b : ℂ) * I) • Z) =
      exp ((b : ℂ) * I) • circularBanachField hγ hγ1 Z := by
  rw [complexValueRotationFamily_eq_shift_rotation]
  rw [circularBanachField_parameterShift hγ hγ1 _ (circularBanachDomain_rotation hγ hγ1 b hZ)]
  rw [circularBanachField_rotation hγ hγ1 b hZ]
  exact (complexValueRotationFamily_eq_shift_rotation b (circularBanachField hγ hγ1 Z)).symm

theorem hasDerivAt_circularRigidRotatedCurve {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Z : ℝ → Fin 2 → LittleContourSpace γ}
    {q : ℝ → (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ}
    (ω e t : ℝ) (hZ : Z t ∈ circularBanachDomain hγ hγ1)
    (hd : HasDerivAt Z (circularBanachField hγ hγ1 (Z t) +
      ((ω : ℂ) * I) • Z t + q t (Z t)) t) :
    HasDerivAt (fun s => rigidRotationGauge ω e s • Z s)
      (circularBanachField hγ hγ1 (rigidRotationGauge ω e t • Z t) +
        rigidRotatedForcing ω e q t (rigidRotationGauge ω e t • Z t)) t := by
  exact hasDerivAt_rigidRotatedCurve (F := circularBanachField hγ hγ1) (q := q) (z := Z) ω e t hd
    (circularBanachField_complexValueRotation hγ hγ1 ((t - e) * (-ω)) hZ)

theorem circularRigidRotatedCurve_mem {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (ω e t : ℝ) {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    rigidRotationGauge ω e t • Z ∈ circularBanachDomain hγ hγ1 :=
  circularBanachDomain_complexValueRotation hγ hγ1 ((t - e) * (-ω)) hZ

theorem circularRigidRotatedCurve_initial {γ : ℝ≥0}
    (ω e : ℝ) (Z : ℝ → Fin 2 → LittleContourSpace γ) :
    rigidRotationGauge ω e e • Z e = Z e := by rw [rigidRotationGauge_entrance, one_smul]

end Euler2D

end
