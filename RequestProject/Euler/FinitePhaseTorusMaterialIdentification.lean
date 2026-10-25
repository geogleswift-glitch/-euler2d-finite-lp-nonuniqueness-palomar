module

public import RequestProject.Euler.FinitePhaseActualCorrectionTransport
public import RequestProject.Euler.CenteredComplexMaterialFlow
public import RequestProject.Euler.BoundedEulerTimeRestriction

/-! The same original torus Euler particles agree with genuine forced
material contours across phase charts. Plane measure preservation and
the intrinsic density transport are constructed before using uniqueness. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem finitePhase_actualCorrection_agreement
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hD : 0 ≤ D) (hDT : D ≤ T)
    (hZc : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D))
    (hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z t i) - Z₀ i‖ < r i / 4)
    (hmat : ∀ t ∈ Icc (0 : ℝ) D, ∀ i θ,
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (contourC1BoundaryField g (Z t) i θ +
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (ContourC1Space.lift γ (Z t i) θ)))) t)
    (w : R2 → ℝ)
    (hinitial : ∀ b, w b = phaseFiniteContourPatchVorticity g (Z 0)
      (centeredComplexHomeomorph.symm b))
    (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    {A : Set R2} (hAbox : A ⊆ torusBox)
    (hdomains : ∀ i z, z ∈ contourRadialFill (ContourC1Space.lift γ (Z 0 i)) → complexTorusPoint z ∈ A)
    (hboundary : ∀ i θ, complexTorusPoint (ContourC1Space.lift γ (Z 0 i) θ) ∈ A)
    (hSsmall : ∀ t ∈ Icc (0 : ℝ) D, ∀ a ∈ A,
      ∀ᵐ b ∂μT, w b ≠ 0 → ‖S.forward t a - S.forward t b‖ ≤ 1 / 2) :
    ∀ t ∈ Icc (0 : ℝ) D,
      (∀ i θ, S.forward t (complexTorusPoint (ContourC1Space.lift γ (Z 0 i) θ)) =
        complexTorusPoint (ContourC1Space.lift γ (Z t i) θ)) ∧
      ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z 0 i))) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z t i)) := by
  obtain ⟨F, hFc, _hFic, hF0, hFd, hFarea, hFtransport⟩ :=
    S.exists_finitePhase_actualCorrection_material_area_transport g Z Z₀ r hr href hD hZc hphase hmat
  obtain ⟨_M, _C, vc, hvc, hvcEq, _hM, _hlog, _hdiv⟩ :=
    S.exists_finitePhase_actualCorrection_velocity g Z Z₀ r hr href hD hZc hphase
  let ω₀ := phaseFiniteContourPatchVorticity g (Z 0)
  obtain ⟨b₀, hb₀⟩ := hphase 0 ⟨le_rfl, hD⟩
  have hω₀ : Integrable ω₀ :=
    integrable_phaseFiniteContourPatchVorticity g (Z 0) Z₀ r hr href b₀ (fun i => (hb₀ i).le)
  have hcInv : MeasurePreserving centeredComplexHomeomorph.symm volume volume :=
    MeasurePreserving.symm centeredComplexHomeomorph.toMeasurableEquiv measurePreserving_centeredComplexHomeomorph
  have hw : Integrable w := by
    apply (hcInv.integrable_comp_of_integrable hω₀).congr
    exact ae_of_all _ fun b => (hinitial b).symm
  have hB (b : R2) : ‖w b‖ ≤ finiteContourPatchSupBound g := by
    rw [hinitial b]
    simpa only [Real.norm_eq_abs] using
      abs_phaseFiniteContourPatchVorticity_le g (Z 0) Z₀ r hr href b₀ (fun i => (hb₀ i).le)
        (centeredComplexHomeomorph.symm b)
  have hactive (b : R2) (hb : w b ≠ 0) : b ∈ A := by
    by_contra hn
    apply hb
    rw [hinitial b]
    unfold phaseFiniteContourPatchVorticity
    apply Finset.sum_eq_zero
    intro i _
    have hni : centeredComplexHomeomorph.symm b ∉ contourRadialFill (ContourC1Space.lift γ (Z 0 i)) := by
      intro hi
      apply hn
      have hh := hdomains i (centeredComplexHomeomorph.symm b) hi
      simpa only [← centeredComplexHomeomorph_apply, Homeomorph.apply_symm_apply] using hh
    simp only [phaseContourPatchVorticity, Set.indicator_of_notMem hni, mul_zero]
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
          contourRadialFill (ContourC1Space.lift γ (Z 0 i)) := by rw [Set.image_image]
      _ = (fun z => complexTorusPoint (F t z)) ''
          contourRadialFill (ContourC1Space.lift γ (Z 0 i)) := by
        apply Set.image_congr
        intro z hz
        exact (hagree t ht _ (hdomains i z hz)).trans (hcomm t z)
      _ = complexTorusPoint '' (F t ''
          contourRadialFill (ContourC1Space.lift γ (Z 0 i))) := by rw [Set.image_image]
      _ = _ := by rw [(hFtransport t ht).2.1 i]

end BoundedEulerParticleSystem
end Euler2D

end
