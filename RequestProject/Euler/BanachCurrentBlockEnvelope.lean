module

public import RequestProject.Euler.GronwallForcingBound

/-! The periodic self forcing is absorbed on each existing finite
capture block. No new trajectory or extension beyond its actual
provisional interval is used. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Set Metric
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem current_existing_block_envelope
    {f : E → E} {U : Set E} {K : ℝ≥0} (hLip : LipschitzOnWith K f U)
    {D B κ : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (y c p : ℝ → E)
    (hyd : ∀ t ∈ Icc (0 : ℝ) D, HasDerivAt y (f (y t) + p t) t)
    (hcd : ∀ t ∈ Icc (0 : ℝ) D, HasDerivAt c (f (c t)) t)
    (hym : ∀ t ∈ Icc (0 : ℝ) D, y t ∈ U)
    (hcm : ∀ t ∈ Icc (0 : ℝ) D, c t ∈ U)
    (hp : ∀ t ∈ Icc (0 : ℝ) D, ‖p t‖ ≤ B + κ * ‖y t - c t‖)
    (hsmall : 2 * (D * Real.exp ((K : ℝ) * D)) * κ ≤ 1) :
    ∀ t ∈ Icc (0 : ℝ) D, ‖y t - c t‖ ≤
      2 * Real.exp ((K : ℝ) * D) * (‖y 0 - c 0‖ + D * B) := by
  have hyc : ContinuousOn y (Icc (0 : ℝ) D) :=
    fun t ht => (hyd t ht).continuousAt.continuousWithinAt
  have hcc : ContinuousOn c (Icc (0 : ℝ) D) :=
    fun t ht => (hcd t ht).continuousAt.continuousWithinAt
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) D).Nonempty from ⟨0, le_rfl, hD⟩) (hyc.sub hcc).norm
  let Q := ‖y t₀ - c t₀‖
  let δ := ‖y 0 - c 0‖
  have hQ : 0 ≤ Q := norm_nonneg _
  have hδ : 0 ≤ δ := norm_nonneg _
  have hbase : 0 ≤ B + κ * Q := by positivity
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) : ‖y t - c t‖ ≤ Q := hmax ht
  have hpc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) : ‖p t‖ ≤ B + κ * Q :=
    (hp t ht).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hbound t ht) hκ))
  have hone (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
      ‖y t - c t‖ ≤ (δ + (B + κ * Q) * D) * Real.exp ((K : ℝ) * D) := by
    have hh := dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun _ x => f x) (s := fun _ => U) (K := K)
      (fun _ _ => hLip) hyc
      (fun s hs => (hyd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (εf := B + κ * Q) (fun s hs => by
        simpa only [dist_eq_norm, add_sub_cancel_left] using hpc s ⟨hs.1, hs.2.le⟩)
      (fun s hs => hym s ⟨hs.1, hs.2.le⟩) hcc
      (fun s hs => (hcd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (εg := 0) (fun _ _ => by simp)
      (fun s hs => hcm s ⟨hs.1, hs.2.le⟩)
      (δ := δ) (by simp only [δ, dist_eq_norm, le_refl]) t ht
    have hg := gronwallBound_le_add_mul_exp (δ := δ) K.coe_nonneg hbase ht.1
    have hh' : ‖y t - c t‖ ≤ gronwallBound δ (K : ℝ) (B + κ * Q) t := by
      simpa only [dist_eq_norm, add_zero, sub_zero] using hh
    exact (hh'.trans hg).trans (mul_le_mul
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht.2 hbase))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg))
      (Real.exp_pos _).le (by positivity))
  have hineq := hone t₀ ht₀
  have hsmallQ := mul_le_mul_of_nonneg_right hsmall hQ
  have hclosed : Q ≤ 2 * Real.exp ((K : ℝ) * D) * (δ + D * B) := by
    nlinarith only [hineq, hsmallQ]
  intro t ht
  exact (hbound t ht).trans hclosed

end Euler2D

end
