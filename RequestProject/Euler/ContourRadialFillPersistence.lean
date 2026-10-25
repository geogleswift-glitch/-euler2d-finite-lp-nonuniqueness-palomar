module

public import RequestProject.Euler.ContourPhaseEnclosedDomain

/-! Interior membership of the genuine radial-fill domain persists
under uniform contour perturbations. Compact radial paths and the
actual frontier identity suffice; no angle-inverse continuity is assumed. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem contourRadialFill_star_segment {w : ℝ → ℂ} {x : ℂ}
    (hx : x ∈ contourRadialFill w) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    u • x ∈ contourRadialFill w := by
  obtain ⟨θ, t, ht0, ht1, hxt⟩ := hx
  refine ⟨θ, u * t, mul_nonneg hu.1 ht0,
    (mul_le_mul_of_nonneg_right hu.2 ht0).trans_lt (by simpa only [one_mul] using ht1), ?_⟩
  rw [hxt, smul_smul]

theorem exists_radialFill_interior_persistence {w : ℝ → ℂ}
    (hwOpen : IsOpen (contourRadialFill w))
    (hwFrontier : frontier (contourRadialFill w) = Set.range w)
    {x : ℂ} (hx : x ∈ contourRadialFill w) :
    ∃ δ > 0, ∀ z : ℝ → ℂ,
      IsOpen (contourRadialFill z) → frontier (contourRadialFill z) = Set.range z →
      (∀ θ, ‖z θ - w θ‖ < δ) → x ∈ contourRadialFill z := by
  let K : Set ℂ := (fun u : ℝ => u • x) '' Icc (0 : ℝ) 1
  have hcurve : Continuous (fun u : ℝ => u • x) := continuous_id.smul continuous_const
  have hK : IsCompact K := isCompact_Icc.image hcurve
  have hKpre : IsPreconnected K := isPreconnected_Icc.image _ hcurve.continuousOn
  have hKsubset : K ⊆ contourRadialFill w := by
    rintro y ⟨u, hu, rfl⟩
    exact contourRadialFill_star_segment hx hu
  have hzero : (0 : ℂ) ∈ K := ⟨0, by norm_num, by simp⟩
  have hxK : x ∈ K := ⟨1, by norm_num, by simp⟩
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hwOpen hKsubset
  refine ⟨δ, hδ, ?_⟩
  intro z hzOpen hzFrontier hclose
  have hdis : Disjoint K (frontier (contourRadialFill z)) := by
    apply Set.disjoint_left.mpr
    intro y hyK hyFrontier
    obtain ⟨θ, hθ⟩ := hzFrontier ▸ hyFrontier
    have hwnear : w θ ∈ thickening δ K := by
      apply mem_thickening_iff.mpr
      refine ⟨y, hyK, ?_⟩
      rw [← hθ]
      simpa only [dist_eq_norm, norm_sub_rev] using hclose θ
    have hwIn := hthick hwnear
    have hwFr : w θ ∈ frontier (contourRadialFill w) := hwFrontier.symm ▸ Set.mem_range_self θ
    rw [frontier, hwOpen.interior_eq] at hwFr
    exact hwFr.2 hwIn
  have hcover : K ⊆ contourRadialFill z ∪ (closure (contourRadialFill z))ᶜ := by
    intro y hyK
    by_cases hy : y ∈ contourRadialFill z
    · exact Or.inl hy
    · apply Or.inr
      intro hycl
      have hyFr : y ∈ frontier (contourRadialFill z) := by
        rw [frontier, hzOpen.interior_eq]
        exact ⟨hycl, hy⟩
      exact Set.disjoint_left.mp hdis hyK hyFr
  have hDC : Disjoint (contourRadialFill z) (closure (contourRadialFill z))ᶜ :=
    Set.disjoint_left.mpr (fun _ hy hn => hn (subset_closure hy))
  rcases IsPreconnected.subset_or_subset hzOpen isClosed_closure.isOpen_compl hDC hcover hKpre with hsub | hsub
  · exact hsub hxK
  · have hz0 : (0 : ℂ) ∈ contourRadialFill z := ⟨0, 0, le_rfl, zero_lt_one, by simp⟩
    exact False.elim ((hsub hzero) (subset_closure hz0))

theorem eventually_mem_contourRadialFill_of_tendsto {ι : Type*} {l : Filter ι} {γ : ℝ≥0}
    (Z : ι → ContourC1Space γ) (W Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hW : ‖W - Z₀‖ ≤ r / 4) (hZ : ∀ i, ‖Z i - Z₀‖ ≤ r / 4)
    (hlim : Tendsto Z l (𝓝 W)) {x : ℂ} (hx : x ∈ contourRadialFill (ContourC1Space.lift γ W)) :
    ∀ᶠ i in l, x ∈ contourRadialFill (ContourC1Space.lift γ (Z i)) := by
  have hOpen : IsOpen (contourRadialFill (ContourC1Space.lift γ W)) := by
    rw [← contourC1EnclosedDomain_eq_radialFill W Z₀ hr href hW]
    exact isOpen_contourC1EnclosedDomain W Z₀ hr href hW
  have hFrontier : frontier (contourRadialFill (ContourC1Space.lift γ W)) =
      Set.range (ContourC1Space.lift γ W) := by
    rw [← contourC1EnclosedDomain_eq_radialFill W Z₀ hr href hW]
    exact frontier_contourC1EnclosedDomain W Z₀ hr href hW
  obtain ⟨δ, hδ, hpersist⟩ := exists_radialFill_interior_persistence hOpen hFrontier hx
  filter_upwards [hlim.eventually (Metric.ball_mem_nhds W hδ)] with i hi
  apply hpersist (ContourC1Space.lift γ (Z i))
  · rw [← contourC1EnclosedDomain_eq_radialFill (Z i) Z₀ hr href (hZ i)]
    exact isOpen_contourC1EnclosedDomain (Z i) Z₀ hr href (hZ i)
  · rw [← contourC1EnclosedDomain_eq_radialFill (Z i) Z₀ hr href (hZ i)]
    exact frontier_contourC1EnclosedDomain (Z i) Z₀ hr href (hZ i)
  · intro θ
    have hh : ‖ContourC1Space.lift γ (Z i - W) θ‖ ≤ ‖Z i - W‖ := by
      exact ContourC1Space.norm_eval_le (Z i - W) (θ : ContourCircle)
    have heq : ContourC1Space.lift γ (Z i - W) θ =
        ContourC1Space.lift γ (Z i) θ - ContourC1Space.lift γ W θ := rfl
    rw [heq] at hh
    exact hh.trans_lt (by simpa only [mem_ball, dist_eq_norm] using hi)

end Euler2D

end
