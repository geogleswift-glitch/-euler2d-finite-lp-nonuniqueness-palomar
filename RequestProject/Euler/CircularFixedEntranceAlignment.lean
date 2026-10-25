module

public import RequestProject.Euler.CircularRetardedTubeAlignment
public import RequestProject.Euler.CircularMaterialPhaseForcing

/-! One constant material alignment removes the entrance's absolute
rigid and material phases. It is fixed for the entire stage and
preserves both the true slow equation and its forcing norm. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 4500

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

local instance fixedEntranceReal_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := (smul_smul a b Z).symm

theorem circularFixedEntranceShift_reference_advance {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (α u v : ℝ) :
    contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift α u)
      (exp ((α : ℂ) * I) • littleCircularMaterialContours hγ hγ1 (u + v)) =
      littleCircularMaterialContours hγ hγ1 v := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change exp ((α : ℂ) * I) * LittleContourSpace.lift γ
    (littleCircularMaterialContours hγ hγ1 (u + v) i)
      (θ + circularRetardedMaterialShift α u i) =
      LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 v i) θ
  rw [lift_littleCircularMaterialContours, lift_littleCircularMaterialContours]
  unfold circularRetardedMaterialShift
  change exp ((α : ℂ) * I) * refCircle (circularContourRadii i)
      (θ + (-α - circularContourAngularVelocities i * u) + circularContourAngularVelocities i * (u + v)) =
      refCircle (circularContourRadii i) (θ + circularContourAngularVelocities i * v)
  rw [show θ + (-α - circularContourAngularVelocities i * u) +
      circularContourAngularVelocities i * (u + v) =
      (θ + circularContourAngularVelocities i * v) - α by ring]
  unfold refCircle
  calc
    _ = (circularContourRadii i : ℂ) *
        (exp ((α : ℂ) * I) * exp (((θ + circularContourAngularVelocities i * v - α : ℝ) : ℂ) * I)) := by ring
    _ = (circularContourRadii i : ℂ) * exp ((α : ℂ) * I +
        (((θ + circularContourAngularVelocities i * v - α : ℝ) : ℂ) * I)) := by rw [exp_add]
    _ = _ := by congr 2; push_cast; ring

theorem norm_circularFixedEntranceShift_sub_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (α u v : ℝ)
    (Y : Fin 2 → LittleContourSpace γ) :
    ‖contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift α u) Y -
        littleCircularMaterialContours hγ hγ1 v‖ =
      ‖Y - exp ((α : ℂ) * I) • littleCircularMaterialContours hγ hγ1 (u + v)‖ := by
  let S := contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift α u)
  have hh : S (Y - exp ((α : ℂ) * I) • littleCircularMaterialContours hγ hγ1 (u + v)) =
      S Y - littleCircularMaterialContours hγ hγ1 v := by
    rw [S.map_sub, circularFixedEntranceShift_reference_advance hγ hγ1]
  rw [← hh, norm_contourParameterShiftFamilyCLM]

theorem hasDerivAt_fixedEntranceAligned_slowForcedCircularCurve {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (α u a t : ℝ)
    {y : ℝ → Fin 2 → LittleContourSpace γ} {p : Fin 2 → LittleContourSpace γ}
    (hm : y t ∈ circularBanachDomain hγ hγ1)
    (hd : HasDerivAt y (a • circularBanachField hγ hγ1 (y t) + p) t) :
    HasDerivAt (fun s => contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift α u) (y s))
      (a • circularBanachField hγ hγ1
          (contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift α u) (y t)) +
        contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift α u) p) t ∧
      ‖contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift α u) p‖ = ‖p‖ := by
  let S := contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift α u)
  constructor
  · have hh := S.hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun s => S (y s)) (S (a • circularBanachField hγ hγ1 (y t) + p)) t at hh
    rw [S.map_add, S.map_smul, ← circularBanachField_parameterShift hγ hγ1 _ hm] at hh
    exact hh
  · exact norm_contourParameterShiftFamilyCLM _ _

theorem littleCircularMaterialContours_slow_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (a t : ℝ) :
    HasDerivAt (fun s => littleCircularMaterialContours hγ hγ1 (a * s))
      (a • circularBanachField hγ hγ1 (littleCircularMaterialContours hγ hγ1 (a * t))) t := by
  have hh := (littleCircularMaterialContours_hasDerivAt hγ hγ1 (a * t)).scomp t
    ((hasDerivAt_id t).const_mul a)
  simpa only [Function.comp_def, circularBanachField, mul_one] using hh

end Euler2D

end
