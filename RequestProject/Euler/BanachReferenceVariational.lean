module

public import RequestProject.Euler.BanachCompactLipschitzNeighborhood
public import RequestProject.Euler.BanachReferenceContinuation
public import RequestProject.Euler.BanachFlowGlobalVariational

/-! Actual directional variational curves identify the derivative of
any genuine flow near a compact reference orbit in an open smooth field.
The original field domain need not admit a global Lipschitz constant. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

set_option maxHeartbeats 600000 in
theorem fderiv_banachFlow_eq_directional_variational_of_compact_reference
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {c : ℝ → E} (hc : Continuous c) (hcK : IsCompact (range c))
    (hcU : ∀ t, c t ∈ U) (hcd : ∀ t, HasDerivAt c (f (c t)) t)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U (ball (c 0) ρ) T X)
    {Y : ℝ → E} (hYc : ContinuousOn Y (Icc (0 : ℝ) T))
    (hYd : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt Y ((fderiv ℝ f (c t)) (Y t)) t) :
    fderiv ℝ (fun b => X b T) (c 0) (Y 0) = Y T := by
  have hf1 : ContDiffOn ℝ 1 f U := hf.of_le (by simp)
  obtain ⟨W, hW, hcW, hWU, K, hLip⟩ :=
    exists_lipschitz_open_neighborhood_of_compact hU hf1 hcK
      (by rintro _ ⟨t, rfl⟩; exact hcU t)
  have hcW' (t : ℝ) : c t ∈ W := hcW (mem_range_self t)
  have hfW : ContDiffOn ℝ ∞ f W := hf.mono hWU
  obtain ⟨r, hr, Z, hZ, _, heZ⟩ :=
    exists_smooth_banachFlow_along_reference 1 hW hfW hc hcW' hcd hT
  let x : ℝ → E := fun t => c (projIcc (0 : ℝ) T hT.le t)
  have hxc : Continuous x :=
    hc.comp (continuous_subtype_val.comp (continuous_projIcc (h := hT.le)))
  have hxW (t : ℝ) : x t ∈ W := hcW' _
  have hx (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : x t = c t := by
    dsimp only [x]
    rw [projIcc_of_mem _ ht]
  let B : ℝ → E →L[ℝ] E := fun t => fderiv ℝ f (x t)
  have hD : ContinuousOn (fderiv ℝ f) W :=
    ((hfW.of_le (by simp) : ContDiffOn ℝ 1 f W).fderiv_of_isOpen hW
      (m := 0) (by norm_num)).continuousOn
  have hBc : Continuous B := hD.comp_continuous hxc hxW
  have hB (t : ℝ) : ‖B t‖ ≤ K :=
    norm_fderiv_le_of_lipschitzOn ℝ (hW.mem_nhds (hxW t)) hLip
  obtain ⟨A, hAc, hA0, hAd, _⟩ :=
    exists_banachFlow_global_variational_curve hBc hB hT.le
  have hAdZ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt A ((fderiv ℝ f (Z (c 0) t)).comp (A t)) t := by
    simpa only [B, hx t ht, heZ ht] using hAd t ht
  have hdZ := hasFDerivAt_banachFlow_of_variational hW
    (hfW.of_le (by simp)) hLip hr hT.le hZ hAc.continuousOn hA0 hAdZ
    (show T ∈ Icc (0 : ℝ) T from ⟨hT.le, le_rfl⟩)
  have hXZ (b : E) (hb : b ∈ ball (c 0) (min ρ r)) :
      EqOn (X b) (Z b) (Icc (0 : ℝ) T) := by
    have hbX : b ∈ ball (c 0) ρ := (ball_subset_ball (min_le_left _ _)) hb
    have hbZ : b ∈ ball (c 0) r := (ball_subset_ball (min_le_right _ _)) hb
    exact eqOn_of_banachODE_open hU hf1
      (hX.continuous b hbX) (hZ.continuous b hbZ)
      (hX.mem b hbX) (fun t ht => hWU (hZ.mem b hbZ t ht))
      (fun t ht => hX.hasDerivAt b hbX t ⟨ht.1, ht.2.le⟩)
      (fun t ht => hZ.hasDerivAt b hbZ t ⟨ht.1, ht.2.le⟩)
      (by rw [hX.initial b hbX, hZ.initial b hbZ])
  have he : (fun b => X b T) =ᶠ[𝓝 (c 0)] (fun b => Z b T) := by
    filter_upwards [ball_mem_nhds (c 0) (lt_min hρ hr)] with b hb
    exact hXZ b hb ⟨hT.le, le_rfl⟩
  have hdX : HasFDerivAt (fun b => X b T) (A T) (c 0) :=
    hdZ.congr_of_eventuallyEq he
  rw [hdX.fderiv]
  have hAL (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
      HasDerivAt (fun s => A s (Y 0)) (B t (A t (Y 0))) t := by
    have hd := (hAd t ⟨ht.1, ht.2.le⟩).clm_apply (hasDerivAt_const t (Y 0))
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using hd
  have hBL (t : ℝ) : LipschitzWith K (B t) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact ((B t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _))
  have heAY : EqOn (fun t => A t (Y 0)) Y (Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun t z => B t z) (s := fun _ => (univ : Set E))
      (fun t _ => (hBL t).lipschitzOnWith)
      (hAc.clm_apply continuous_const).continuousOn
      (fun t ht => (hAL t ht).hasDerivWithinAt) (fun _ _ => mem_univ _)
      hYc (fun t ht => by
        have hd := hYd t ht
        simpa only [B, hx t ⟨ht.1, ht.2.le⟩] using hd.hasDerivWithinAt)
      (fun _ _ => mem_univ _) (by rw [hA0, ContinuousLinearMap.id_apply])
  exact heAY ⟨hT.le, le_rfl⟩

end Euler2D

end
