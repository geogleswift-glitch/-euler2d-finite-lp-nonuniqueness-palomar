module

public import RequestProject.Euler.CircularRigidRotationGauge

/-! The actual norm deviation from the circular material orbit is
exactly a physical relative-tube deviation after a geometric material
shift. The shift is used only to describe domains; the dynamical stage
gauge and clock are not reset. -/

@[expose] public section

set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

noncomputable section

open Complex
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def circularRetardedMaterialShift (φ t : ℝ) (i : Fin 2) : ℝ :=
  -φ - circularContourAngularVelocities i * t

theorem circularRetardedMaterialShift_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (φ t : ℝ) :
    contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift φ t)
      (exp ((φ : ℂ) * I) • littleCircularMaterialContours hγ hγ1 t) =
      littleCircularReference hγ hγ1 := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change exp ((φ : ℂ) * I) * LittleContourSpace.lift γ
    (littleCircularMaterialContours hγ hγ1 t i)
      (θ + circularRetardedMaterialShift φ t i) = refCircle (circularContourRadii i) θ
  rw [lift_littleCircularMaterialContours]
  change exp ((φ : ℂ) * I) * refCircle (circularContourRadii i)
    (θ + (-φ - circularContourAngularVelocities i * t) + circularContourAngularVelocities i * t) = _
  rw [show θ + (-φ - circularContourAngularVelocities i * t) +
      circularContourAngularVelocities i * t = θ - φ by ring]
  unfold refCircle
  calc
    _ = (circularContourRadii i : ℂ) *
        (exp ((φ : ℂ) * I) * exp (((θ - φ : ℝ) : ℂ) * I)) := by ring
    _ = (circularContourRadii i : ℂ) * exp ((φ : ℂ) * I + (((θ - φ : ℝ) : ℂ) * I)) :=
      by rw [exp_add]
    _ = _ := by congr 2; push_cast; ring

theorem norm_circularRetardedAligned_sub_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (φ t : ℝ)
    (Y : Fin 2 → LittleContourSpace γ) :
    ‖contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift φ t)
        (exp ((φ : ℂ) * I) • Y) - littleCircularReference hγ hγ1‖ =
      ‖Y - littleCircularMaterialContours hγ hγ1 t‖ := by
  let S := contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift φ t)
  have he := circularRetardedMaterialShift_reference hγ hγ1 φ t
  have hh : S (exp ((φ : ℂ) * I) • (Y - littleCircularMaterialContours hγ hγ1 t)) =
      S (exp ((φ : ℂ) * I) • Y) - littleCircularReference hγ hγ1 := by
    rw [smul_sub, S.map_sub, he]
  rw [← hh, norm_contourParameterShiftFamilyCLM, norm_smul,
    norm_exp_ofReal_mul_I, one_mul]

theorem norm_circularRetardedPhysicalAligned_sub_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {r : ℝ} (hr : 0 ≤ r) (φ t : ℝ)
    (Y : Fin 2 → LittleContourSpace γ) :
    ‖contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift φ t)
        (r • (exp ((φ : ℂ) * I) • Y)) - r • littleCircularReference hγ hγ1‖ =
      r * ‖Y - littleCircularMaterialContours hγ hγ1 t‖ := by
  rw [map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    norm_circularRetardedAligned_sub_reference hγ hγ1 φ t]

end Euler2D

end
