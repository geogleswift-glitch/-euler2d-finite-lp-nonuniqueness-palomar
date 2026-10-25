module

public import RequestProject.Euler.BanachOpenODEUniqueness

/-! A compact reference orbit supplies a uniform positive local time
for genuine smooth flows at every reference point in a finite interval. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_uniform_local_banachFlow_along_reference (n : ℕ)
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {c : ℝ → E} (hc : Continuous c) (hcU : ∀ t, c t ∈ U)
    (hcd : ∀ t, HasDerivAt c (f (c t)) t) {T : ℝ} (hT : 0 ≤ T) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) T, ∃ ρ > 0, ∃ X : E → ℝ → E,
      IsBanachFlowOn f U (ball (c t) ρ) δ X ∧
      (∀ s ∈ Icc (0 : ℝ) δ, ContDiffOn ℝ n (fun b => X b s) (ball (c t) ρ)) ∧
      EqOn (X (c t)) (fun s => c (t + s)) (Icc (0 : ℝ) δ) := by
  classical
  let K : Set E := c '' Icc (0 : ℝ) T
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hc.continuousOn
  have hKU : ∀ x : K, x.val ∈ U := by
    rintro ⟨x, t, ht, rfl⟩
    exact hcU t
  choose ρ hρ τ hτ X hX hs using
    (fun x : K => exists_local_smooth_banachFlow n hU hf (hKU x))
  have hcover : K ⊆ ⋃ x : K, ball x.val (ρ x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hρ ⟨x, hx⟩)⟩
  obtain ⟨s, hsub⟩ := hK.elim_finite_subcover (fun x : K => ball x.val (ρ x))
    (fun _ => isOpen_ball) hcover
  have h0K : c 0 ∈ K := mem_image_of_mem c ⟨le_rfl, hT⟩
  obtain ⟨x₀, hx₀, _⟩ := mem_iUnion₂.mp (hsub h0K)
  have hsne : s.Nonempty := ⟨x₀, hx₀⟩
  let δ : ℝ := s.inf' hsne τ
  have hδ : 0 < δ := (Finset.lt_inf'_iff hsne).mpr (fun x _ => hτ x)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  obtain ⟨x, hxs, htx⟩ := mem_iUnion₂.mp (hsub (mem_image_of_mem c ht))
  have hδτ : δ ≤ τ x := Finset.inf'_le τ hxs
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds htx)
  have hflow := ((hX x).mono_initial hrsub).mono_time hδτ
  refine ⟨r, hr, X x, hflow, ?_, ?_⟩
  · intro u hu
    exact (hs x u ⟨hu.1, hu.2.trans hδτ⟩).mono hrsub
  · apply eqOn_of_banachODE_open hU (hf.of_le (by simp))
      (hflow.continuous (c t) (mem_ball_self hr))
      (hc.comp (continuous_const.add continuous_id)).continuousOn
      (hflow.mem (c t) (mem_ball_self hr)) (fun u _ => hcU (t + u))
      (fun u hu => hflow.hasDerivAt (c t) (mem_ball_self hr) u ⟨hu.1, hu.2.le⟩)
    · intro u _
      simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_smul] using
        (hcd (t + u)).scomp u ((hasDerivAt_const u t).add (hasDerivAt_id u))
    · simpa only [Function.comp_def, Pi.add_apply, id_eq, add_zero] using
        hflow.initial (c t) (mem_ball_self hr)

end Euler2D

end
