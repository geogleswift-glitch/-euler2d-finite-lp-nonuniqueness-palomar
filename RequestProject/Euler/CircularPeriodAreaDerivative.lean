module

public import RequestProject.Euler.CircularConstrainedPeriodMap

/-! The original linear area functional is the actual derivative of
the signed patch area at the reference circle, and the genuine return
derivative preserves it on every original perturbation. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) periodAreaDerivLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) periodAreaDerivLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem littleContourArea_reference_add {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (r : ℝ) (v : LittleContourSpace γ) :
    littleContourArea γ (littleReferenceCircle hγ hγ1 r + v) =
      Real.pi * r ^ 2 + littleContourEllCLM γ r v + littleContourArea γ v := by
  rw [littleContourEllCLM_eq_ellFun]
  change loopArea (LittleContourSpace.lift γ (littleReferenceCircle hγ hγ1 r + v)) = _
  rw [LittleContourSpace.lift_add, lift_littleReferenceCircle]
  simpa only [Complex.ofReal_one, one_mul, one_pow] using
    loopArea_affine r 1 (LittleContourSpace.contDiff_lift v) (LittleContourSpace.periodic_lift v)

theorem hasFDerivAt_littleContourArea_reference {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) :
    HasFDerivAt (littleContourArea γ) (littleContourEllCLM γ r) (littleReferenceCircle hγ hγ1 r) := by
  let C := littleReferenceCircle hγ hγ1 r
  have hsum := ((hasFDerivAt_const (Real.pi * r ^ 2) (0 : LittleContourSpace γ)).add
    (littleContourEllCLM γ r).hasFDerivAt).add (hasFDerivAt_littleContourArea_zero γ)
  have hd : HasFDerivAt (fun v => littleContourArea γ (C + v)) (littleContourEllCLM γ r) 0 := by
    have he : (fun v => littleContourArea γ (C + v)) =
        (fun v => Real.pi * r ^ 2 + littleContourEllCLM γ r v + littleContourArea γ v) :=
      funext (littleContourArea_reference_add hγ hγ1 r)
    rw [he]
    simpa only [zero_add, add_zero] using hsum
  have ht : HasFDerivAt (fun Z : LittleContourSpace γ => Z - C)
      (ContinuousLinearMap.id ℝ (LittleContourSpace γ)) C := (hasFDerivAt_id C).sub_const C
  have hd' : HasFDerivAt (fun v => littleContourArea γ (C + v)) (littleContourEllCLM γ r) (C - C) := by
    rw [sub_self]
    exact hd
  have h := hd'.comp (f := fun Z : LittleContourSpace γ => Z - C) C ht
  have he : (fun Z : LittleContourSpace γ => littleContourArea γ (C + (Z - C))) = littleContourArea γ := by
    funext Z
    congr 1
    abel
  change HasFDerivAt (fun Z => littleContourArea γ (C + (Z - C)))
    ((littleContourEllCLM γ r).comp (ContinuousLinearMap.id ℝ (LittleContourSpace γ))) C at h
  rw [he, ContinuousLinearMap.comp_id] at h
  exact h

theorem circularPeriod_derivative_preserves_ell {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ}
    (hd : DifferentiableAt ℝ P (littleCircularReference hγ hγ1))
    (hfix : P (littleCircularReference hγ hγ1) = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ i,
      littleContourArea γ (P W i) = littleContourArea γ (W i))
    (H : Fin 2 → LittleContourSpace γ) (i : Fin 2) :
    littleContourEllCLM γ (circularContourRadii i)
        (fderiv ℝ P (littleCircularReference hγ hγ1) H i) =
      littleContourEllCLM γ (circularContourRadii i) (H i) := by
  let c := littleCircularReference hγ hγ1
  let A := fun W : Fin 2 → LittleContourSpace γ => littleContourArea γ (W i)
  let L := (littleContourEllCLM γ (circularContourRadii i)).comp
    (ContinuousLinearMap.proj i : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ)
  have hA : HasFDerivAt A L c :=
    (hasFDerivAt_littleContourArea_reference hγ hγ1.le (circularContourRadii i)).comp
      (f := fun W : Fin 2 → LittleContourSpace γ => W i) c
      (ContinuousLinearMap.proj i : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ).hasFDerivAt
  have hA' : HasFDerivAt A L (P c) := by rw [hfix]; exact hA
  have hAP := hA'.comp c hd.hasFDerivAt
  have he : (fun W => A (P W)) =ᶠ[𝓝 c] A := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with W hW
    exact harea W hW i
  have hEq := hAP.unique (hA.congr_of_eventuallyEq he)
  exact congrArg (fun M : (Fin 2 → LittleContourSpace γ) →L[ℝ] ℝ => M H) hEq

end Euler2D

end
