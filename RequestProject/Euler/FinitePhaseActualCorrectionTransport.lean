module

public import RequestProject.Euler.FinitePhaseActualCorrectionParticleFlow

/-! Genuine domain and density transport for the actual forced material
contours through phase chart changes. No continuous phase choice and no
time-dependent change of material labels is used. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_finitePhase_actualCorrection_material_area_transport
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hD : 0 ≤ D)
    (hZ : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D))
    (hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z t i) - Z₀ i‖ < r i / 4)
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
          (velocityC (phaseFiniteContourPatchVorticity g (Z t)) (F t a) +
            planeComplexEquiv (S.correctionLabelField t (complexTorusPoint (F t a)))) t) ∧
      (∀ t ∈ Icc (0 : ℝ) D, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume) ∧
      ∀ t ∈ Icc (0 : ℝ) D,
        (∀ i θ, F t (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z t i) θ) ∧
        (∀ i, F t '' contourRadialFill (ContourC1Space.lift γ (Z 0 i)) =
          contourRadialFill (ContourC1Space.lift γ (Z t i))) ∧
        ∀ x, phaseFiniteContourPatchVorticity g (Z t) x =
          phaseFiniteContourPatchVorticity g (Z 0) ((F t).symm x) := by
  obtain ⟨M, C, v, hv, heq, hM, hlog, hdiv⟩ :=
    S.exists_finitePhase_actualCorrection_velocity g Z Z₀ r hr href hD hZ hphase
  obtain ⟨F, hFc, hFic, hF0, hFd, hFa⟩ :=
    exists_complex_measurePreserving_logHomeomorphFlow hv hM hlog hdiv hD
  have hZd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (i : ι) (θ : ℝ) :
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (v t (ContourC1Space.lift γ (Z t i) θ)) t := by
    obtain ⟨b, hb⟩ := hphase t ht
    have hd := hmat t ht i θ
    change HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
      (contourBoundaryField g (fun j => ContourC1Space.lift γ (Z t j)) i θ + _) t at hd
    rw [contourBoundaryField_eq_phase_actual_velocity g (Z t) Z₀ r hr href b (fun j => (hb j).le),
      ← heq t ht (ContourC1Space.lift γ (Z t i) θ)] at hd
    exact hd
  have hboundary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (i : ι) (θ : ℝ) :
      F t (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z t i) θ :=
    logFlow_uniqueOn C.2
      (fun s hs => (hFd s hs _).continuousAt.continuousWithinAt)
      (fun s hs => (hZd s hs i θ).continuousAt.continuousWithinAt)
      (fun s hs => hFd s hs _) (fun s hs => hZd s hs i θ) (hF0 _)
      (fun s _ z w hzw => hlog s z w hzw) t ht
  have hp : ∀ s ∈ Icc (0 : ℝ) D, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z s i) - Z₀ i‖ ≤ r i / 4 := by
    intro s hs
    obtain ⟨b, hb⟩ := hphase s hs
    exact ⟨b, fun i => (hb i).le⟩
  have hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) D) :=
    (hFic.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hFzero : (F 0).symm 0 = 0 := by
    rw [← hF0 ((F 0).symm 0), (F 0).apply_symm_apply]
  refine ⟨F, hFc, hFic, hF0, ?_, hFa, ?_⟩
  · intro t ht a
    simpa only [heq t ht] using hFd t ht a
  · intro t ht
    refine ⟨hboundary t ht, ?_, ?_⟩
    · intro i
      exact image_contourRadialFill_of_phase_boundary_isotopy (fun s => Z s i) (Z₀ i)
        (hr i) hD (href i)
        (fun s hs => by obtain ⟨b, hb⟩ := hp s hs; exact ⟨b i, hb i⟩)
        F hFinv hFzero (fun s hs θ => hboundary s hs i θ) ht
    · intro x
      exact phaseFiniteContourPatchVorticity_eq_initial_comp_inverse g Z Z₀ r hr hD href hp
        F hFinv hFzero hboundary ht x

end BoundedEulerParticleSystem
end Euler2D

end
