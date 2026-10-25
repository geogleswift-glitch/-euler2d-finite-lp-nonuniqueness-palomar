module

public import RequestProject.Euler.CircularPeriodConstraints

/-! Rotation covariance of every actual circular Banach flow on a
reference ball, and commutation of its genuine full-period derivative
with all weighted rotations on the original little space. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) periodRotationC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) periodRotationLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) periodRotationLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem norm_contourRotationFamilyLittleCLM {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (b : ℝ) (W : ι → LittleContourSpace γ) :
    ‖contourRotationFamilyLittleCLM γ b W‖ = ‖W‖ := by
  have hle (c : ℝ) (Z : ι → LittleContourSpace γ) :
      ‖contourRotationFamilyLittleCLM γ c Z‖ ≤ ‖Z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg Z)).mpr
    intro i
    rw [contourRotationFamilyLittleCLM_apply]
    exact (norm_contourRotationLittleCLM c (Z i)).trans_le (norm_le_pi_norm Z i)
  apply le_antisymm (hle b W)
  have h := hle (-b) (contourRotationFamilyLittleCLM γ b W)
  have he : contourRotationFamilyLittleCLM γ (-b) (contourRotationFamilyLittleCLM γ b W) = W := by
    funext i
    change contourRotationLittleCLM γ (-b) (contourRotationLittleCLM γ b (W i)) = W i
    rw [contourRotationLittleCLM_add, neg_add_cancel, contourRotationLittleCLM_zero]
  rwa [he] at h

theorem contourRotationFamilyLittleCLM_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (b : ℝ) :
    contourRotationFamilyLittleCLM γ b (littleCircularReference hγ hγ1) =
      littleCircularReference hγ hγ1 := by
  funext i
  apply Subtype.ext
  exact contourRotationC1_refCircle b _ (lift_littleReferenceCircle hγ hγ1.le _)

theorem circularReferenceBall_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (b ρ : ℝ)
    {W : Fin 2 → LittleContourSpace γ}
    (hW : W ∈ ball (littleCircularReference hγ hγ1) ρ) :
    contourRotationFamilyLittleCLM γ b W ∈ ball (littleCircularReference hγ hγ1) ρ := by
  rw [mem_ball, dist_eq_norm] at hW ⊢
  rw [← contourRotationFamilyLittleCLM_reference hγ hγ1 b, ← map_sub,
    norm_contourRotationFamilyLittleCLM]
  exact hW

set_option maxHeartbeats 800000 in
theorem circularBanachFlow_rotation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {ρ T : ℝ}
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) T X)
    (b : ℝ) {W : Fin 2 → LittleContourSpace γ}
    (hW : W ∈ ball (littleCircularReference hγ hγ1) ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    X (contourRotationFamilyLittleCLM γ b W) t =
      contourRotationFamilyLittleCLM γ b (X W t) := by
  let R := contourRotationFamilyLittleCLM (ι := Fin 2) γ b
  have hRW := circularReferenceBall_rotation hγ hγ1 b ρ hW
  have hd (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivAt (fun u => R (X W u)) (circularBanachField hγ hγ1 (R (X W s))) s := by
    have h := R.hasFDerivAt.comp_hasDerivAt s (hX.hasDerivAt W hW s hs)
    change HasDerivAt (fun u => R (X W u)) (R (circularBanachField hγ hγ1 (X W s))) s at h
    rw [← circularBanachField_rotation hγ hγ1 b (hX.mem W hW s hs)] at h
    exact h
  have he : EqOn (fun u => R (X W u)) (X (R W)) (Icc 0 T) := by
    apply eqOn_of_banachODE_open
      (isOpen_phaseAdmissibleLittleContourFamilies _ _)
      (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1)
      (R.continuous.comp_continuousOn (hX.continuous W hW)) (hX.continuous (R W) hRW)
      (fun s hs => circularBanachDomain_rotation hγ hγ1 b (hX.mem W hW s hs))
      (hX.mem (R W) hRW)
      (fun s hs => hd s ⟨hs.1, hs.2.le⟩)
      (fun s hs => hX.hasDerivAt (R W) hRW s ⟨hs.1, hs.2.le⟩)
    change R (X W 0) = X (R W) 0
    rw [hX.initial W hW, hX.initial (R W) hRW]
  exact (he ht).symm

set_option maxHeartbeats 800000 in
theorem circularPeriod_derivative_rotation_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (b : ℝ) :
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)).comp
        (contourRotationFamilyLittleCLM γ b) =
      (contourRotationFamilyLittleCLM γ b).comp
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) := by
  let c := littleCircularReference hγ hγ1
  let R := contourRotationFamilyLittleCLM (ι := Fin 2) γ b
  have hfix : R c = c := contourRotationFamilyLittleCLM_reference hγ hγ1 b
  have hleft := (show HasFDerivAt (fun W => X W period)
      (fderiv ℝ (fun W => X W period) c) (R c) by rw [hfix]; exact hd.hasFDerivAt).comp c
    R.hasFDerivAt
  have hright := R.hasFDerivAt.comp c hd.hasFDerivAt
  have he : (fun W => X (R W) period) =ᶠ[𝓝 c] (fun W => R (X W period)) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with W hW
    exact circularBanachFlow_rotation hγ hγ1 hX b hW ⟨by unfold period; positivity, le_rfl⟩
  exact hleft.unique (hright.congr_of_eventuallyEq he)

end Euler2D

end
