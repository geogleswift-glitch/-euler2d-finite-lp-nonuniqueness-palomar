module

public import RequestProject.Euler.CircularPhaseVelocityFlow
public import RequestProject.Euler.PhaseDomainTransport
public import RequestProject.Euler.LogFlowIntervalUniqueness

/-! The original circular material equation on the whole quarter-phase
domain gives actual area-preserving particle transport of its true
physical density and preserves every planar Lp norm. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_circularPhase_material_area_transport
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
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x,
        circularPhasePatchVorticity (Z t) x = circularPhasePatchVorticity (Z 0) ((F t).symm x)) ∧
      ∀ (p : ℝ≥0∞) t, t ∈ Icc (0 : ℝ) T →
        eLpNorm (circularPhasePatchVorticity (Z t)) p volume =
          eLpNorm (circularPhasePatchVorticity (Z 0)) p volume := by
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
  have htransport (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : ℂ) :
      circularPhasePatchVorticity (Z t) x = circularPhasePatchVorticity (Z 0) ((F t).symm x) := by
    exact phaseFiniteContourPatchVorticity_eq_initial_comp_inverse circularContourStrengths
      (fun s i => (Z s i).val) (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos hT
      (lift_circularReferenceC1 hγ hγ1)
      (fun s hs => exists_circularQuarterPhase_shift hγ hγ1 (hZm s hs))
      F hFinv hF0inv hboundary ht x
  refine ⟨F, hFc, hFic, hF0, hFd', hFarea, htransport, ?_⟩
  intro p t ht
  have he : circularPhasePatchVorticity (Z t) = circularPhasePatchVorticity (Z 0) ∘ (F t).symm :=
    funext (htransport t ht)
  rw [he]
  exact eLpNorm_comp_measurePreserving
    (integrable_circularPhasePatchVorticity hγ hγ1 (hZm 0 ⟨le_rfl, hT⟩)).aestronglyMeasurable (hFarea t ht).2

end Euler2D

end
