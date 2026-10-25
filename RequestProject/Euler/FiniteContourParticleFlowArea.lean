module

public import RequestProject.Euler.FiniteContourParticleFlow
public import RequestProject.Euler.FiniteContourPlanarIncompressibility

/-! The genuine complex-plane particle homeomorphisms of the
original finite patch velocity preserve actual planar area. Osgood
uniqueness identifies the existing true material flow with the actual
measure-preserving Euclidean flow constructed from its smoothings. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem exists_finiteContour_particleFlow_area
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (hZ : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) T)) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a,
        HasDerivAt (fun s => F s a)
          (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) (F t a)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        MeasurePreserving (F t) volume volume ∧ MeasurePreserving (F t).symm volume volume := by
  obtain ⟨F, hFc, hFic, hF0, hFd⟩ := exists_finiteContour_particleFlow g Z Z₀ r hr href hT hsmall hZ
  let Zi : Icc (0 : ℝ) T → ι → ContourC1Space γ := fun t => Z t
  let hsmalli : ∀ t : Icc (0 : ℝ) T, ∀ i, ‖Zi t i - Z₀ i‖ ≤ r i / 4 :=
    fun t i => hsmall t t.property i
  have hZi (i : ι) : Continuous (fun t : Icc (0 : ℝ) T => Zi t i) := (hZ i).restrict
  let v := finiteContourPlanarVelocity hT g Zi Z₀ r hr href hsmalli
  obtain ⟨S, hSarea⟩ := exists_finiteContour_measurePreserving_planarLogParticleFlow hT g Zi Z₀ r hr href hsmalli hZi
  let G : ℝ → R2 → R2 := fun t x => complexPhysicalPlane (F t (complexPhysicalPlane.symm x))
  have hGc : Continuous (Function.uncurry G) := complexPhysicalPlane.continuous.comp
    (hFc.comp (continuous_fst.prodMk (complexPhysicalPlane.symm.continuous.comp continuous_snd)))
  have hG0 (a : R2) : G 0 a = a := by
    dsimp only [G]
    rw [hF0, LinearIsometryEquiv.apply_symm_apply]
  have hGd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
      HasDerivAt (fun s => G s a) (v t (G t a)) t := by
    have hd := complexPhysicalPlane.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hFd t ht (complexPhysicalPlane.symm a))
    change HasDerivAt (fun s => G s a)
      (complexPhysicalPlane (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t)
        (F t (complexPhysicalPlane.symm a)))) t at hd
    rw [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ht] at hd
    have he : v t (G t a) = complexPhysicalPlane
        (velocityC (finiteContourC1PatchVorticity g (Z t) Z₀ r hr href (hsmall t ht))
          (F t (complexPhysicalPlane.symm a))) :=
      finiteContourPlanarVelocity_apply hT g Zi Z₀ r hr href hsmalli
        (⟨t, ht⟩ : Icc (0 : ℝ) T) (F t (complexPhysicalPlane.symm a))
    rw [← he] at hd
    exact hd
  let C := 8 * (finiteContourPatchSupBound g + finiteContourPatchMassBound g r)
  have hC : 0 ≤ C := by
    dsimp only [C]
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  have heq (a : R2) : ∀ t ∈ Icc (0 : ℝ) T, G t a = S.forward t a := by
    exact logFlow_unique hC (hGc.comp (continuous_id.prodMk continuous_const))
      (S.continuous_forward.comp (continuous_id.prodMk continuous_const))
      (fun t ht => hGd t ht a) (fun t ht => S.derivative t ht a)
      ((hG0 a).trans (S.initial a).symm)
      (fun t _ x y hxy => finiteContourPlanarVelocity_logFlowModulus_le hT g Zi Z₀ r hr href hsmalli t hxy)
  refine ⟨F, hFc, hFic, hF0, hFd, ?_⟩
  intro t ht
  have hGarea : MeasurePreserving (G t) volume volume := by
    have he : G t = S.forward t := funext (fun a => heq a t ht)
    rw [he]
    exact (hSarea t ht).1
  have hFarea : MeasurePreserving (F t) volume volume := by
    have hm := complexPhysicalPlane.symm.measurePreserving.comp
      (hGarea.comp complexPhysicalPlane.measurePreserving)
    have he : (complexPhysicalPlane.symm ∘ G t ∘ complexPhysicalPlane) = F t := by
      funext z
      simp only [Function.comp_def, G, LinearIsometryEquiv.symm_apply_apply]
    change MeasurePreserving (complexPhysicalPlane.symm ∘ G t ∘ complexPhysicalPlane) volume volume at hm
    rw [he] at hm
    exact hm
  exact ⟨hFarea, MeasurePreserving.symm (F t).toMeasurableEquiv hFarea⟩

end Euler2D

end
