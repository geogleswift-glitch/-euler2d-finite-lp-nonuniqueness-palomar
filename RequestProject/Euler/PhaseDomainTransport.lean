module

public import RequestProject.Euler.ContourPhaseVorticity

/-! Genuine transport of the intrinsic physical domains through
arbitrary phase-chart changes. The inverse isotopy selects the actual
interior component; equality of boundaries alone is insufficient. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) phaseTransportC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseTransportC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem image_contourRadialFill_of_phase_boundary_isotopy
    {γ : ℝ≥0} (Z : ℝ → ContourC1Space γ) (Z₀ : ContourC1Space γ)
    {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hphase : ∀ s ∈ Icc (0 : ℝ) T, ∃ b : ℝ, ‖contourParameterShiftC1 b (Z s) - Z₀‖ ≤ r / 4)
    (F : ℝ → ℂ ≃ₜ ℂ)
    (hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) T))
    (hF0 : (F 0).symm 0 = 0)
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ∀ θ,
      F s (ContourC1Space.lift γ (Z 0) θ) = ContourC1Space.lift γ (Z s) θ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    F t '' contourRadialFill (ContourC1Space.lift γ (Z 0)) =
      contourRadialFill (ContourC1Space.lift γ (Z t)) := by
  have hopen (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      IsOpen (contourRadialFill (ContourC1Space.lift γ (Z s))) := by
    obtain ⟨b, hb⟩ := hphase s hs
    exact isOpen_contourRadialFill_of_shift (Z s) Z₀ hr href b hb
  have hfront (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      frontier (contourRadialFill (ContourC1Space.lift γ (Z s))) =
        range (ContourC1Space.lift γ (Z s)) := by
    obtain ⟨b, hb⟩ := hphase s hs
    exact frontier_contourRadialFill_of_shift (Z s) Z₀ hr href b hb
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hpath : MapsTo (fun s => (F s).symm 0) (Icc (0 : ℝ) T)
      (contourRadialFill (ContourC1Space.lift γ (Z 0))) := by
    apply mapsTo_of_isPreconnected_avoids_frontier isPreconnected_Icc (hopen 0 h0) hFinv
    · intro s hs hbad
      rw [hfront 0 h0] at hbad
      obtain ⟨θ, hθ⟩ := hbad
      have he : ContourC1Space.lift γ (Z s) θ = 0 := by
        rw [← hb s hs θ, hθ, (F s).apply_symm_apply]
      have hf : (0 : ℂ) ∈ frontier (contourRadialFill (ContourC1Space.lift γ (Z s))) := by
        rw [hfront s hs]
        exact ⟨θ, he⟩
      exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr (hopen s hs)) hf
        (zero_mem_contourRadialFill _)
    · refine ⟨0, h0, ?_⟩
      rw [hF0]
      exact zero_mem_contourRadialFill _
  apply eq_of_isOpen_isPreconnected_frontier_eq_inter
    ((F t).isOpenMap _ (hopen 0 h0)) (hopen t ht)
    ((isConnected_contourRadialFill _).isPreconnected.image (F t) (F t).continuous.continuousOn)
    (isConnected_contourRadialFill _).isPreconnected
  · rw [← (F t).image_frontier, hfront 0 h0, hfront t ht, ← Set.range_comp]
    congr 1
    exact funext (hb t ht)
  · exact ⟨0, ⟨(F t).symm 0, hpath ht, (F t).apply_symm_apply 0⟩, zero_mem_contourRadialFill _⟩

theorem phaseFiniteContourPatchVorticity_eq_initial_comp_inverse
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {T : ℝ} (hT : 0 ≤ T)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (hphase : ∀ s ∈ Icc (0 : ℝ) T, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z s i) - Z₀ i‖ ≤ r i / 4)
    (F : ℝ → ℂ ≃ₜ ℂ)
    (hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) T))
    (hF0 : (F 0).symm 0 = 0)
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ∀ i θ,
      F s (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z s i) θ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : ℂ) :
    phaseFiniteContourPatchVorticity g (Z t) x =
      phaseFiniteContourPatchVorticity g (Z 0) ((F t).symm x) := by
  unfold phaseFiniteContourPatchVorticity
  apply Finset.sum_congr rfl
  intro i _
  have he := image_contourRadialFill_of_phase_boundary_isotopy (fun s => Z s i) (Z₀ i)
    (hr i) hT (href i)
    (fun s hs => by obtain ⟨b, hb⟩ := hphase s hs; exact ⟨b i, hb i⟩)
    F hFinv hF0 (fun s hs θ => hb s hs i θ) ht
  unfold phaseContourPatchVorticity
  rw [← he, (F t).image_eq_preimage_symm]
  by_cases hx : (F t).symm x ∈ contourRadialFill (ContourC1Space.lift γ (Z 0 i)) <;> simp [hx]

end Euler2D

end
