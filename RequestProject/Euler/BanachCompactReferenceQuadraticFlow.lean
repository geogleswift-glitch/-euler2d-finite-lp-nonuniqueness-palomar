module

public import RequestProject.Euler.BanachFlowQuadraticLinearization
public import RequestProject.Euler.BanachReferenceContinuation
public import RequestProject.Euler.BanachOpenODEUniqueness

/-! Uniform quadratic material-flow linearization near a compact
reference orbit in the original open field domain. A genuine Lipschitz
neighborhood is constructed and its flow is identified by ODE uniqueness. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem banachFlow_uniform_quadratic_of_compact_reference
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {c : ℝ → E} (hc : Continuous c) (hcK : IsCompact (range c))
    (hcU : ∀ t, c t ∈ U) (hcd : ∀ t, HasDerivAt c (f (c t)) t)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U (ball (c 0) ρ) T X)
    {A : ℝ → E →L[ℝ] E} (hAc : ContinuousOn A (Icc (0 : ℝ) T))
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hAd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A ((fderiv ℝ f (c t)).comp (A t)) t) :
    ∃ δ > 0, ∃ C > 0, ∀ h : E, ‖h‖ ≤ δ → ∀ t ∈ Icc (0 : ℝ) T,
      ‖X (c 0 + h) t - c t - A t h‖ ≤ C * ‖h‖ ^ 2 := by
  have horder (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
    change ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  have hf1 : ContDiffOn ℝ 1 f U := hf.of_le (horder 1)
  obtain ⟨W, hW, hCW, hWU, K, hLip⟩ :=
    exists_lipschitz_open_neighborhood_of_compact hU hf1 hcK
      (by rintro _ ⟨t, rfl⟩; exact hcU t)
  have hcW (t : ℝ) : c t ∈ W := hCW (mem_range_self t)
  have hfW : ContDiffOn ℝ ∞ f W := hf.mono hWU
  obtain ⟨r, hr, Z, hZ, hs, heZ⟩ := exists_smooth_banachFlow_along_reference 2 hW hfW hc hcW hcd hT
  let r₀ := min r ρ
  have hr₀ : 0 < r₀ := lt_min hr hρ
  have hsubZ : ball (c 0) r₀ ⊆ ball (c 0) r := ball_subset_ball (min_le_left _ _)
  have hsubX : ball (c 0) r₀ ⊆ ball (c 0) ρ := ball_subset_ball (min_le_right _ _)
  have hZr := hZ.mono_initial hsubZ
  have hXZ (b : E) (hb : b ∈ ball (c 0) r₀) : EqOn (X b) (Z b) (Icc (0 : ℝ) T) := by
    apply eqOn_of_banachODE_open hU hf1 (hX.continuous b (hsubX hb))
      (hZ.continuous b (hsubZ hb)) (hX.mem b (hsubX hb))
      (fun t ht => hWU (hZ.mem b (hsubZ hb) t ht))
      (fun t ht => hX.hasDerivAt b (hsubX hb) t ⟨ht.1, ht.2.le⟩)
      (fun t ht => hZ.hasDerivAt b (hsubZ hb) t ⟨ht.1, ht.2.le⟩)
    exact (hX.initial b (hsubX hb)).trans (hZ.initial b (hsubZ hb)).symm
  have hAZ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt A ((fderiv ℝ f (Z (c 0) t)).comp (A t)) t := by
    rw [heZ ht]
    exact hAd t ht
  obtain ⟨δ, hδ, C, hC, hquad⟩ := banachFlow_uniform_quadratic_linearization hW
    (hfW.of_le (horder 2)) hLip hr₀ hT.le hZr hAc hA0 hAZ
  refine ⟨min δ (r₀ / 2), lt_min hδ (half_pos hr₀), C, hC, ?_⟩
  intro h hh t ht
  have hbh : c 0 + h ∈ ball (c 0) r₀ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hh.trans (min_le_right _ _)).trans_lt (half_lt_self hr₀)
  have he : banachFlowLinearizationError Z (c 0) h A t = X (c 0 + h) t - c t - A t h := by
    unfold banachFlowLinearizationError
    rw [← hXZ (c 0 + h) hbh ht, heZ ht]
  have hbound := hquad h (hh.trans (min_le_left _ _)) t ht
  rwa [he] at hbound

end Euler2D

end
