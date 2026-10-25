module

public import RequestProject.Euler.CircularPhaseMaterialTransport

/-! The same genuine particle isotopy transports each individual
enclosed interface domain, not only the sum of the patch indicators. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_circularPhase_material_domain_transport
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z : ℝ → Fin 2 → LittleContourSpace γ) {T : ℝ} (hT : 0 ≤ T)
    (hZc : ContinuousOn Z (Icc (0 : ℝ) T))
    (hZm : ∀ t ∈ Icc (0 : ℝ) T, Z t ∈ circularQuarterPhaseDomain hγ hγ1)
    (hZd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Z (circularBanachField hγ hγ1 (Z t)) t) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => F s a)
        (velocityC (circularPhasePatchVorticity (Z t)) (F t a)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 2,
        F t '' contourRadialFill (LittleContourSpace.lift γ (Z 0 i)) =
          contourRadialFill (LittleContourSpace.lift γ (Z t i)) := by
  let Zi : Icc (0 : ℝ) T → Fin 2 → LittleContourSpace γ := fun t => Z t
  have hZi : Continuous Zi := hZc.restrict
  obtain ⟨F, hFc, hFic, hF0, hFd, hFarea⟩ := exists_circularPhase_particleFlow_area hγ hγ1 hT Zi hZi
    (fun t => hZm t t.property)
  have hFd' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : ℂ) :
      HasDerivAt (fun s => F s a) (velocityC (circularPhasePatchVorticity (Z t)) (F t a)) t := by
    simpa only [circularPhaseVelocityOnInterval, projIcc_of_mem hT ht, Zi] using hFd t ht a
  have hdloop (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 2) (θ : ℝ) :
      HasDerivAt (fun s => LittleContourSpace.lift γ (Z s i) θ)
        (velocityC (circularPhasePatchVorticity (Z t)) (LittleContourSpace.lift γ (Z t i) θ)) t := by
    have hd := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
      (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t (hZd t ht)
    change HasDerivAt (fun s => LittleContourSpace.lift γ (Z s i) θ)
      (LittleContourSpace.lift γ (circularBanachField hγ hγ1 (Z t) i) θ) t at hd
    rwa [circularBanachField_eq_actual_phase_velocity hγ hγ1 (hZm t ht) i θ] at hd
  let C := 8 * (finiteContourPatchSupBound circularContourStrengths +
    finiteContourPatchMassBound circularContourStrengths circularContourRadii)
  have hC : 0 ≤ C := by
    dsimp only [C]
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  have hlip (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x y : ℂ) (hxy : ‖x - y‖ ≤ 1 / 2) :
      ‖velocityC (circularPhasePatchVorticity (Z t)) x - velocityC (circularPhasePatchVorticity (Z t)) y‖ ≤
        C * logFlowModulus ‖x - y‖ :=
    velocityC_logFlowModulus_le (integrable_circularPhasePatchVorticity hγ hγ1 (hZm t ht))
      (abs_circularPhasePatchVorticity_le hγ hγ1 (hZm t ht))
      (integral_abs_circularPhasePatchVorticity_le hγ hγ1 (hZm t ht)) hxy
  have hboundary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 2) (θ : ℝ) :
      F t (LittleContourSpace.lift γ (Z 0 i) θ) = LittleContourSpace.lift γ (Z t i) θ :=
    logFlow_uniqueOn hC
      (fun s hs => (hFd' s hs _).continuousAt.continuousWithinAt)
      (fun s hs => (hdloop s hs i θ).continuousAt.continuousWithinAt)
      (fun s hs => hFd' s hs _) (fun s hs => hdloop s hs i θ) (hF0 _) hlip t ht
  have hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) T) :=
    (hFic.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hF0inv : (F 0).symm 0 = 0 := by rw [← hF0 ((F 0).symm 0), (F 0).apply_symm_apply]
  refine ⟨F, hFc, hFic, hF0, hFd', hFarea, ?_⟩
  intro t ht i
  exact image_contourRadialFill_of_phase_boundary_isotopy (fun s => (Z s i).val)
    (circularReferenceC1 hγ hγ1 i) (growingMoment_radius_pos i) hT
    (lift_circularReferenceC1 hγ hγ1 i)
    (fun s hs => by
      obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 (hZm s hs)
      exact ⟨b i, hb i⟩)
    F hFinv hF0inv (fun s hs θ => hboundary s hs i θ) ht

end Euler2D

end
