module

public import RequestProject.Euler.FiniteContourActualCorrectionTransport
public import RequestProject.Euler.CenteredComplexMaterialFlow
public import RequestProject.Euler.BoundedEulerTimeRestriction

/-! Identification with the original torus Euler particles. The genuine
forced plane particles, their density transport, and the proved mixed
nonlinear uniqueness supply the comparison; no particle agreement is an
input assumption. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem finiteContour_actualCorrection_agreement
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hD : 0 ≤ D) (hDT : D ≤ T)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) D, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (hZc : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D))
    (hmat : ∀ t ∈ Icc (0 : ℝ) D, ∀ i θ,
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (contourC1BoundaryField g (Z t) i θ +
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (ContourC1Space.lift γ (Z t i) θ)))) t)
    (w : R2 → ℝ)
    (hinitial : ∀ b, w b = finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0
      (centeredComplexHomeomorph.symm b))
    (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    {A : Set R2} (hAbox : A ⊆ torusBox)
    (hdomains : ∀ i z, z ∈ contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i)
      (hsmall 0 ⟨le_rfl, hD⟩ i) → complexTorusPoint z ∈ A)
    (hboundary : ∀ i θ, complexTorusPoint (ContourC1Space.lift γ (Z 0 i) θ) ∈ A)
    (hSsmall : ∀ t ∈ Icc (0 : ℝ) D, ∀ a ∈ A,
      ∀ᵐ b ∂μT, w b ≠ 0 → ‖S.forward t a - S.forward t b‖ ≤ 1 / 2) :
    ∀ t (ht : t ∈ Icc (0 : ℝ) D),
      (∀ i θ, S.forward t (complexTorusPoint (ContourC1Space.lift γ (Z 0 i) θ)) =
        complexTorusPoint (ContourC1Space.lift γ (Z t i) θ)) ∧
      ∀ i, S.forward t '' (complexTorusPoint ''
          contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i) (hsmall 0 ⟨le_rfl, hD⟩ i)) =
        complexTorusPoint '' contourC1EnclosedDomain (Z t i) (Z₀ i) (hr i) (href i) (hsmall t ht i) := by
  obtain ⟨F, hFc, _hFic, hF0, hFd, hFarea, hFtransport⟩ :=
    S.exists_finiteContour_actualCorrection_material_area_transport g Z Z₀ r hr href hD hsmall hZc hmat
  obtain ⟨vc, hvc, hvcEq⟩ :=
    S.exists_finiteContour_actualCorrection_continuous_velocity g Z Z₀ r hr href hD hsmall hZc
  let ω₀ := finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0
  have hω₀ : Integrable ω₀ := by
    dsimp only [ω₀]
    rw [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ⟨le_rfl, hD⟩]
    exact integrable_finiteContourC1PatchVorticity g (Z 0) Z₀ r hr href (hsmall 0 ⟨le_rfl, hD⟩)
  have hcInv : MeasurePreserving centeredComplexHomeomorph.symm volume volume :=
    MeasurePreserving.symm centeredComplexHomeomorph.toMeasurableEquiv measurePreserving_centeredComplexHomeomorph
  have hw : Integrable w := by
    apply (hcInv.integrable_comp_of_integrable hω₀).congr
    exact ae_of_all _ fun b => (hinitial b).symm
  have hB (b : R2) : ‖w b‖ ≤ finiteContourPatchSupBound g := by
    rw [hinitial b, finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ⟨le_rfl, hD⟩]
    simpa only [Real.norm_eq_abs] using
      abs_finiteContourC1PatchVorticity_le g (Z 0) Z₀ r hr href (hsmall 0 ⟨le_rfl, hD⟩)
        (centeredComplexHomeomorph.symm b)
  have hactive (b : R2) (hb : w b ≠ 0) : b ∈ A := by
    by_contra hn
    apply hb
    rw [hinitial b, finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ⟨le_rfl, hD⟩]
    unfold finiteContourC1PatchVorticity
    apply Finset.sum_eq_zero
    intro i _
    have hni : centeredComplexHomeomorph.symm b ∉
        contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i) (hsmall 0 ⟨le_rfl, hD⟩ i) := by
      intro hi
      apply hn
      have hh := hdomains i (centeredComplexHomeomorph.symm b) hi
      simpa only [← centeredComplexHomeomorph_apply, Homeomorph.apply_symm_apply] using hh
    simp only [contourC1PatchVorticity, Set.indicator_of_notMem hni, mul_zero]
  have hwzero (b : R2) (hb : b ∉ torusBox) : w b = 0 := by
    by_contra hne
    exact hb (hAbox (hactive b hne))
  let Q : ℝ → R2 ≃ₜ R2 := fun t => physicalComplexHomeomorph (F t)
  let vy : ℝ → R2 → R2 := fun t a =>
    complexPhysicalPlane (vc t (F t (centeredComplexHomeomorph.symm a)))
  have hyc (a : R2) (_ha : a ∈ A) : Continuous (fun t => vy t a) := by
    have htraj : Continuous (fun t => F t (centeredComplexHomeomorph.symm a)) :=
      hFc.comp (continuous_id.prodMk continuous_const)
    have hh : Continuous (fun t => vc t (F t (centeredComplexHomeomorph.symm a))) := Continuous.comp
      (f := fun t => (t, F t (centeredComplexHomeomorph.symm a)))
      (g := fun p : ℝ × ℂ => vc p.1 p.2) hvc (continuous_id.prodMk htraj)
    exact complexPhysicalPlane.continuous.comp hh
  have hQd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (a : R2) (_ha : a ∈ A) :
      HasDerivAt (fun s => Q s a) (vy t a) t := by
    have hd := hasDerivAt_complexTorusPoint_comp (hFd t ht (centeredComplexHomeomorph.symm a))
    rw [← hvcEq t ht (F t (centeredComplexHomeomorph.symm a))] at hd
    exact hd
  have heqY (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (a : R2) (ha : a ∈ A) :
      vy t a = planarMaterialLabelVelocity kernelK w (Q t) (Q t a) +
        S.correctionLabelField t (Q t a) := by
    have hm := hasDerivAt_physicalComplexHomeomorph_material (hFarea t ht).1
      (hFtransport t ht).2.2 (hFd t ht) a
    have he : (fun b => ω₀ (centeredComplexHomeomorph.symm b)) = w :=
      funext fun b => (hinitial b).symm
    change HasDerivAt (fun s => Q s a)
      (planarMaterialLabelVelocity kernelK (fun b => ω₀ (centeredComplexHomeomorph.symm b))
        (Q t) (Q t a) + S.correctionLabelField t (Q t a)) t at hm
    rw [he] at hm
    exact (hQd t ht a ha).unique hm
  have hvf := torusExtension_ae (f : R2 → ℝ)
  have hagree : ∀ t ∈ Icc (0 : ℝ) D, ∀ a ∈ A, S.forward t a = Q t a :=
    (S.restrictTime hDT).forward_eq_plane_material_active_of_velocity_bounds
      hw hB hwzero (hwf.trans hvf.symm) hvf (isTorusPeriodic_torusExtension _) hD
      (ae_of_all _ fun b hb => hactive b hb)
      (fun t a => Q t a) vy (fun t => Q t)
      (fun _ => rfl) (fun t => measurePreserving_physicalComplexHomeomorph (F t) (hFarea t t.property).1)
      hSsmall hyc hQd
      (fun a _ => by simp only [Q, physicalComplexHomeomorph_apply, hF0, Homeomorph.apply_symm_apply]) heqY
  have hcomm (t : ℝ) (z : ℂ) : Q t (complexTorusPoint z) = complexTorusPoint (F t z) := by
    simp only [Q, physicalComplexHomeomorph_apply, ← centeredComplexHomeomorph_apply,
      Homeomorph.symm_apply_apply]
  intro t ht
  refine ⟨?_, ?_⟩
  · intro i θ
    exact (hagree t ht _ (hboundary i θ)).trans
      ((hcomm t _).trans (congrArg complexTorusPoint ((hFtransport t ht).1 i θ)))
  · intro i
    calc
      _ = (fun z => S.forward t (complexTorusPoint z)) ''
          contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i) (hsmall 0 ⟨le_rfl, hD⟩ i) := by
        rw [Set.image_image]
      _ = (fun z => complexTorusPoint (F t z)) ''
          contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i) (hsmall 0 ⟨le_rfl, hD⟩ i) := by
        apply Set.image_congr
        intro z hz
        exact (hagree t ht _ (hdomains i z hz)).trans (hcomm t z)
      _ = complexTorusPoint '' (F t ''
          contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i) (hsmall 0 ⟨le_rfl, hD⟩ i)) := by
        rw [Set.image_image]
      _ = _ := by rw [(hFtransport t ht).2.1 i]

end BoundedEulerParticleSystem
end Euler2D

end
