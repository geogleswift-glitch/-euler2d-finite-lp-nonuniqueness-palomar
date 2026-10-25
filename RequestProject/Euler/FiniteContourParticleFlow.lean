module

public import RequestProject.Euler.FiniteContourPlanarVelocity
public import RequestProject.Euler.PlanarLogHomeomorphFlow
public import RequestProject.Euler.ContourMaterialVorticity

/-! Actual planar particle homeomorphisms driven by the genuine finite
patch density. Their existence is proved from compact smoothings; no
particle flow or torus periodicity is an input assumption. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

set_option maxHeartbeats 600000 in
theorem exists_finiteContour_particleFlow
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
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
        HasDerivAt (fun s => F s a)
          (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) (F t a)) t := by
  let Zi : Icc (0 : ℝ) T → ι → ContourC1Space γ := fun t => Z t
  let hsmalli : ∀ t : Icc (0 : ℝ) T, ∀ i, ‖Zi t i - Z₀ i‖ ≤ r i / 4 :=
    fun t i => hsmall t t.property i
  have hZi (i : ι) : Continuous (fun t : Icc (0 : ℝ) T => Zi t i) := (hZ i).restrict
  let v := finiteContourPlanarVelocity hT g Zi Z₀ r hr href hsmalli
  have hv : Continuous (Function.uncurry v) :=
    continuous_finiteContourPlanarVelocity hT g Zi Z₀ r hr href hsmalli hZi
  obtain ⟨M, C, K, hvn, _, hmod, hconv⟩ :=
    exists_smoothApproximation_finiteContourPlanarVelocity hT g Zi Z₀ r hr href hsmalli hZi
  obtain ⟨G, hGc, hGic, hG0, hGd⟩ :=
    exists_planarLogHomeomorphFlow_of_uniform_approximation hv
      (smoothBoundedLogVelocityApproximation v) K M C hvn hmod hconv hT
  let e := complexPhysicalPlane.toHomeomorph
  let F : ℝ → ℂ ≃ₜ ℂ := fun t => e.trans (G t) |>.trans e.symm
  have hFc : Continuous (fun p : ℝ × ℂ => F p.1 p.2) := by
    have h := complexPhysicalPlane.symm.continuous.comp
      (hGc.comp (continuous_fst.prodMk (complexPhysicalPlane.continuous.comp continuous_snd)))
    exact h.congr (fun _ => rfl)
  have hFic : Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) := by
    have h := complexPhysicalPlane.symm.continuous.comp
      (hGic.comp (continuous_fst.prodMk (complexPhysicalPlane.continuous.comp continuous_snd)))
    exact h.congr (fun _ => rfl)
  refine ⟨F, hFc, hFic, ?_, ?_⟩
  · intro a
    change complexPhysicalPlane.symm (G 0 (complexPhysicalPlane a)) = a
    rw [hG0, LinearIsometryEquiv.symm_apply_apply]
  · intro t ht a
    have hd := complexPhysicalPlane.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hGd t ht (complexPhysicalPlane a))
    change HasDerivAt (fun s => F s a)
      (complexPhysicalPlane.symm (v t (G t (complexPhysicalPlane a)))) t at hd
    have he : v t (G t (complexPhysicalPlane a)) =
        complexPhysicalPlane (velocityC
          (finiteContourC1PatchVorticity g (Z t) Z₀ r hr href (hsmall t ht)) (F t a)) := by
      have h := finiteContourPlanarVelocity_apply hT g Zi Z₀ r hr href hsmalli
        (⟨t, ht⟩ : Icc (0 : ℝ) T) (complexPhysicalPlane.symm (G t (complexPhysicalPlane a)))
      change finiteContourPlanarVelocity hT g Zi Z₀ r hr href hsmalli t
          (G t (complexPhysicalPlane a)) =
        complexPhysicalPlane (velocityC
          (finiteContourC1PatchVorticity g (Zi ⟨t, ht⟩) Z₀ r hr href (hsmalli ⟨t, ht⟩))
          (complexPhysicalPlane.symm (G t (complexPhysicalPlane a))))
      simpa only [LinearIsometryEquiv.apply_symm_apply] using h
    rw [he, LinearIsometryEquiv.symm_apply_apply] at hd
    rw [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ht]
    exact hd

end Euler2D

end
