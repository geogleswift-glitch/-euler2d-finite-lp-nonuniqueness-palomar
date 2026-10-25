module

public import RequestProject.Euler.FiniteContourActualCorrectionParticleFlow
public import RequestProject.Euler.ContourMaterialVorticity

/-! The finite forced contour equation is transported by the genuine
plane area-preserving particles constructed from the same actual torus
correction. Boundary, enclosed domains and indicator density all agree. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_finiteContour_actualCorrection_continuous_velocity
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hD : 0 ≤ D)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) D, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (hZc : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D)) :
    ∃ v : ℝ → ℂ → ℂ, Continuous (Function.uncurry v) ∧
      ∀ t ∈ Icc (0 : ℝ) D, ∀ z, v t z =
        velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) z +
          planeComplexEquiv (S.correctionLabelField t (complexTorusPoint z)) := by
  let Zi : Icc (0 : ℝ) D → ι → ContourC1Space γ := fun t => Z t
  let hsmalli : ∀ t : Icc (0 : ℝ) D, ∀ i, ‖Zi t i - Z₀ i‖ ≤ r i / 4 :=
    fun t i => hsmall t t.property i
  let vp := finiteContourPlanarVelocity hD g Zi Z₀ r hr href hsmalli
  have hvp : Continuous (Function.uncurry vp) :=
    continuous_finiteContourPlanarVelocity hD g Zi Z₀ r hr href hsmalli (fun i => (hZc i).restrict)
  let v : ℝ → ℂ → ℂ := fun t z => complexPhysicalPlane.symm
    (vp t (complexPhysicalPlane z) + S.correctionLabelField t (complexTorusPoint z))
  have hpc : Continuous (fun p : ℝ × ℂ => vp p.1 (complexPhysicalPlane p.2)) := Continuous.comp
    (f := fun p : ℝ × ℂ => (p.1, complexPhysicalPlane p.2))
    (g := fun p : ℝ × R2 => vp p.1 p.2) hvp
    (continuous_fst.prodMk (complexPhysicalPlane.continuous.comp continuous_snd))
  have hj : Continuous (fun p : ℝ × ℂ => (p.1, complexTorusPoint p.2)) :=
    continuous_fst.prodMk (complexTorusPoint_smooth.continuous.comp continuous_snd)
  have hcc : Continuous (fun p : ℝ × ℂ => S.correctionLabelField p.1 (complexTorusPoint p.2)) :=
    Continuous.comp (f := fun p : ℝ × ℂ => (p.1, complexTorusPoint p.2))
      (g := fun p : ℝ × R2 => S.correctionLabelField p.1 p.2) S.continuous_correctionLabelField hj
  have hc : Continuous (Function.uncurry v) := Continuous.comp
    (f := fun p : ℝ × ℂ => vp p.1 (complexPhysicalPlane p.2) + S.correctionLabelField p.1 (complexTorusPoint p.2))
    (g := fun x : R2 => complexPhysicalPlane.symm x) complexPhysicalPlane.symm.continuous (hpc.add hcc)
  refine ⟨v, hc, ?_⟩
  intro t ht z
  have hp := finiteContourPlanarVelocity_apply hD g Zi Z₀ r hr href hsmalli
    (⟨t, ht⟩ : Icc (0 : ℝ) D) z
  change vp t (complexPhysicalPlane z) = _ at hp
  dsimp only [v]
  rw [hp, map_add, LinearIsometryEquiv.symm_apply_apply]
  simp only [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ht,
    complexPhysicalPlane_symm_eq_planeComplexEquiv, Zi]

theorem exists_finiteContour_actualCorrection_material_area_transport
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hD : 0 ≤ D)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) D, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (hZc : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D))
    (hmat : ∀ t ∈ Icc (0 : ℝ) D, ∀ i θ,
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (contourC1BoundaryField g (Z t) i θ +
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (ContourC1Space.lift γ (Z t i) θ)))) t) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) D, ∀ a,
        HasDerivAt (fun s => F s a)
          (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) (F t a) +
            planeComplexEquiv (S.correctionLabelField t (complexTorusPoint (F t a)))) t) ∧
      (∀ t ∈ Icc (0 : ℝ) D, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume) ∧
      ∀ t (ht : t ∈ Icc (0 : ℝ) D),
        (∀ i θ, F t (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z t i) θ) ∧
        (∀ i, F t '' contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i)
            (hsmall 0 ⟨le_rfl, hD⟩ i) =
          contourC1EnclosedDomain (Z t i) (Z₀ i) (hr i) (href i) (hsmall t ht i)) ∧
        ∀ x, finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t x =
          finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0 ((F t).symm x) := by
  obtain ⟨F, hFc, hFic, hF0, hFd, hFarea⟩ :=
    S.exists_finiteContour_actualCorrection_particleFlow_area g Z Z₀ r hr href hD hsmall hZc
  obtain ⟨C, hC, hlog⟩ := S.exists_finiteContour_actualCorrection_logBound g Z Z₀ r hr href hsmall
  let v : ℝ → ℂ → ℂ := fun t x =>
    velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) x +
      planeComplexEquiv (S.correctionLabelField t (complexTorusPoint x))
  have hZd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (i : ι) (θ : ℝ) :
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (v t (ContourC1Space.lift γ (Z t i) θ)) t := by
    have hd := hmat t ht i θ
    rw [contourC1BoundaryField_eq_actual_velocity g (Z t) Z₀ r hr href (hsmall t ht)] at hd
    simpa only [v, finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ht] using hd
  have hboundary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (i : ι) (θ : ℝ) :
      F t (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z t i) θ := by
    exact logFlow_uniqueOn hC
      (fun s hs => (hFd s hs _).continuousAt.continuousWithinAt)
      (fun s hs => (hZd s hs i θ).continuousAt.continuousWithinAt)
      (fun s hs => hFd s hs _) (fun s hs => hZd s hs i θ) (hF0 _) hlog t ht
  have hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) D) :=
    (hFic.comp (continuous_id.prodMk continuous_const)).continuousOn
  have himage (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (i : ι) :
      F t '' contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i)
        (hsmall 0 ⟨le_rfl, hD⟩ i) =
      contourC1EnclosedDomain (Z t i) (Z₀ i) (hr i) (href i) (hsmall t ht i) := by
    apply image_contourC1EnclosedDomain_of_boundary_isotopy (fun s => Z s i) (Z₀ i)
      (hr i) hD (href i) (fun s hs => hsmall s hs i) F hFinv
    · rw [← hF0 ((F 0).symm 0), (F 0).apply_symm_apply]
    · intro s hs θ
      exact hboundary s hs i θ
    · exact ht
  refine ⟨F, hFc, hFic, hF0, hFd, hFarea, ?_⟩
  intro t ht
  refine ⟨hboundary t ht, himage t ht, ?_⟩
  intro x
  classical
  rw [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ht,
    finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ⟨le_rfl, hD⟩]
  unfold finiteContourC1PatchVorticity
  apply Finset.sum_congr rfl
  intro i _
  unfold contourC1PatchVorticity
  rw [← himage t ht i, (F t).image_eq_preimage_symm]
  by_cases hx : (F t).symm x ∈ contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i)
      (hsmall 0 ⟨le_rfl, hD⟩ i) <;> simp [hx]

end BoundedEulerParticleSystem
end Euler2D

end
