module

public import RequestProject.Euler.ContourC1EnclosedDomain
public import RequestProject.Euler.ContourDomainFill
public import Mathlib.Analysis.Convex.PathConnected

/-! Identification of genuine enclosed domains under a homeomorphism.
The interior component is selected by an actual common interior point.
Boundary equality alone is never used as a substitute for this step. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

theorem starConvex_contourRadialFill (z : ℝ → ℂ) :
    StarConvex ℝ 0 (contourRadialFill z) := by
  rw [starConvex_zero_iff]
  rintro x ⟨θ, t, ht0, ht1, rfl⟩ a ha0 ha1
  refine ⟨θ, a * t, mul_nonneg ha0 ht0, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right ha1 ht0).trans_lt (by simpa using ht1)
  · rw [smul_smul]

theorem zero_mem_contourRadialFill (z : ℝ → ℂ) :
    (0 : ℂ) ∈ contourRadialFill z :=
  ⟨0, 0, le_rfl, zero_lt_one, by simp⟩

theorem isConnected_contourRadialFill (z : ℝ → ℂ) :
    IsConnected (contourRadialFill z) :=
  ((starConvex_contourRadialFill z).isPathConnected (zero_mem_contourRadialFill z)).isConnected

theorem contourC1EnclosedDomain_eq_radialFill {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) :
    contourC1EnclosedDomain Z Z₀ hr href hsmall =
      contourRadialFill (ContourC1Space.lift γ Z) :=
  nearCircleEnclosedDomain_eq_contourRadialFill hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)
    (ContourC1Space.periodic_lift Z)

theorem isConnected_contourC1EnclosedDomain {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) :
    IsConnected (contourC1EnclosedDomain Z Z₀ hr href hsmall) := by
  rw [contourC1EnclosedDomain_eq_radialFill]
  exact isConnected_contourRadialFill _

theorem zero_mem_contourC1EnclosedDomain {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) :
    (0 : ℂ) ∈ contourC1EnclosedDomain Z Z₀ hr href hsmall := by
  rw [contourC1EnclosedDomain_eq_radialFill]
  exact zero_mem_contourRadialFill _

theorem eq_of_isOpen_isPreconnected_frontier_eq_inter
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hcU : IsPreconnected U) (hcV : IsPreconnected V)
    (hfr : frontier U = frontier V) (hi : (U ∩ V).Nonempty) : U = V := by
  have hsub {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
      (hcA : IsPreconnected A) (hf : frontier A = frontier B)
      (hab : (A ∩ B).Nonempty) : A ⊆ B := by
    apply hcA.subset_of_closure_inter_subset hB hab
    rintro x ⟨hxc, hxa⟩
    by_contra hxb
    have hxfb : x ∈ frontier B := by
      rw [frontier, hB.interior_eq]
      exact ⟨hxc, hxb⟩
    have hxfa : x ∈ frontier A := hf.symm ▸ hxfb
    exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hA) hxfa hxa
  exact Set.Subset.antisymm (hsub hU hV hcU hfr hi)
    (hsub hV hU hcV hfr.symm (by simpa only [Set.inter_comm] using hi))

theorem homeomorph_image_enclosedDomain_of_boundary
    {γ : ℝ≥0} (Z W Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hZ : ‖Z - Z₀‖ ≤ r / 4) (hW : ‖W - Z₀‖ ≤ r / 4)
    (F : ℂ ≃ₜ ℂ)
    (hb : ∀ θ, F (ContourC1Space.lift γ Z θ) = ContourC1Space.lift γ W θ)
    (hinside : F 0 ∈ contourC1EnclosedDomain W Z₀ hr href hW) :
    F '' contourC1EnclosedDomain Z Z₀ hr href hZ =
      contourC1EnclosedDomain W Z₀ hr href hW := by
  apply eq_of_isOpen_isPreconnected_frontier_eq_inter
    (F.isOpenMap _ (isOpen_contourC1EnclosedDomain Z Z₀ hr href hZ))
    (isOpen_contourC1EnclosedDomain W Z₀ hr href hW)
    ((isConnected_contourC1EnclosedDomain Z Z₀ hr href hZ).isPreconnected.image
      F F.continuous.continuousOn)
    (isConnected_contourC1EnclosedDomain W Z₀ hr href hW).isPreconnected
  · rw [← F.image_frontier, frontier_contourC1EnclosedDomain,
      frontier_contourC1EnclosedDomain, ← Set.range_comp]
    congr 1
    exact funext hb
  · exact ⟨F 0, ⟨0, zero_mem_contourC1EnclosedDomain Z Z₀ hr href hZ, rfl⟩, hinside⟩

theorem homeomorph_image_enclosedDomain_of_boundary_zero
    {γ : ℝ≥0} (Z W Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hZ : ‖Z - Z₀‖ ≤ r / 4) (hW : ‖W - Z₀‖ ≤ r / 4)
    (F : ℂ ≃ₜ ℂ)
    (hb : ∀ θ, F (ContourC1Space.lift γ Z θ) = ContourC1Space.lift γ W θ)
    (hzero : F 0 = 0) :
    F '' contourC1EnclosedDomain Z Z₀ hr href hZ =
      contourC1EnclosedDomain W Z₀ hr href hW := by
  apply homeomorph_image_enclosedDomain_of_boundary Z W Z₀ hr href hZ hW F hb
  rw [hzero]
  exact zero_mem_contourC1EnclosedDomain W Z₀ hr href hW

theorem mapsTo_of_isPreconnected_avoids_frontier
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {U : Set Y} {p : X → Y}
    (hA : IsPreconnected A) (hU : IsOpen U) (hp : ContinuousOn p A)
    (havoid : ∀ s ∈ A, p s ∉ frontier U)
    (hinit : ∃ s ∈ A, p s ∈ U) : MapsTo p A U := by
  have hi : (p '' A ∩ U).Nonempty := by
    obtain ⟨s, hs, hsu⟩ := hinit
    exact ⟨p s, ⟨s, hs, rfl⟩, hsu⟩
  have hsub : p '' A ⊆ U := by
    apply (hA.image p hp).subset_of_closure_inter_subset hU hi
    rintro y ⟨hyc, s, hs, rfl⟩
    by_contra hsu
    apply havoid s hs
    rw [frontier, hU.interior_eq]
    exact ⟨hyc, hsu⟩
  intro s hs
  exact hsub ⟨s, hs, rfl⟩

/-- A true continuous inverse isotopy selects the interior component.
In particular, no fixed-center assumption is needed. -/
theorem image_contourC1EnclosedDomain_of_boundary_isotopy
    {γ : ℝ≥0} (Z : ℝ → ContourC1Space γ) (Z₀ : ContourC1Space γ)
    {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ∀ s ∈ Icc (0 : ℝ) T, ‖Z s - Z₀‖ ≤ r / 4)
    (F : ℝ → ℂ ≃ₜ ℂ)
    (hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) T))
    (hF0 : (F 0).symm 0 = 0)
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ∀ θ,
      F s (ContourC1Space.lift γ (Z 0) θ) = ContourC1Space.lift γ (Z s) θ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    F t '' contourC1EnclosedDomain (Z 0) Z₀ hr href (hsmall 0 ⟨le_rfl, hT⟩) =
      contourC1EnclosedDomain (Z t) Z₀ hr href (hsmall t ht) := by
  let D₀ := contourC1EnclosedDomain (Z 0) Z₀ hr href (hsmall 0 ⟨le_rfl, hT⟩)
  have hopen : IsOpen D₀ := isOpen_contourC1EnclosedDomain _ _ _ _ _
  have hzero : (0 : ℂ) ∈ D₀ := zero_mem_contourC1EnclosedDomain _ _ _ _ _
  have hpath : MapsTo (fun s => (F s).symm 0) (Icc (0 : ℝ) T) D₀ := by
    apply mapsTo_of_isPreconnected_avoids_frontier isPreconnected_Icc hopen hFinv
    · intro s hs hbad
      change (F s).symm 0 ∈ frontier (contourC1EnclosedDomain _ _ _ _ _) at hbad
      rw [frontier_contourC1EnclosedDomain] at hbad
      obtain ⟨θ, hθ⟩ := hbad
      have he : ContourC1Space.lift γ (Z s) θ = 0 := by
        rw [← hb s hs θ, hθ, (F s).apply_symm_apply]
      have hf : (0 : ℂ) ∈ frontier (contourC1EnclosedDomain (Z s) Z₀ hr href (hsmall s hs)) := by
        rw [frontier_contourC1EnclosedDomain]
        exact ⟨θ, he⟩
      exact Set.disjoint_left.mp
        (disjoint_frontier_iff_isOpen.mpr (isOpen_contourC1EnclosedDomain _ _ _ _ _)) hf
        (zero_mem_contourC1EnclosedDomain _ _ _ _ _)
    · refine ⟨0, ⟨le_rfl, hT⟩, ?_⟩
      rw [hF0]
      exact hzero
  apply eq_of_isOpen_isPreconnected_frontier_eq_inter
    ((F t).isOpenMap D₀ hopen) (isOpen_contourC1EnclosedDomain _ _ _ _ _)
    ((isConnected_contourC1EnclosedDomain _ _ _ _ _).isPreconnected.image
      (F t) (F t).continuous.continuousOn)
    (isConnected_contourC1EnclosedDomain _ _ _ _ _).isPreconnected
  · rw [← (F t).image_frontier, frontier_contourC1EnclosedDomain,
      frontier_contourC1EnclosedDomain, ← Set.range_comp]
    congr 1
    exact funext (hb t ht)
  · refine ⟨0, ⟨(F t).symm 0, hpath ht, (F t).apply_symm_apply 0⟩,
      zero_mem_contourC1EnclosedDomain _ _ _ _ _⟩

end Euler2D
