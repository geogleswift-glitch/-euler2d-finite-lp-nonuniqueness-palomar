module

public import RequestProject.Euler.TorusPartialCircularForcing

/-! Actual fixed partial forcing on a circular active prefix. Quarter
phase geometry supplies its target separation, and actual contour norm
budgets supply the finite closed-tube bound used in continuation. -/

@[expose] public section

set_option maxHeartbeats 4500000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_finiteCircular_partial_continuation_field
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (hmean : (∫ x in torusBox, f x) = 0)
    {q : R2 → ℝ} {M : ℝ} (hq : MemLp q 2 μT) (hqper : IsTorusPeriodic q)
    (hqrot : ∀ x, q (torusQuarterTurn x) = q x)
    (hqmean : (∫ x in torusBox, q x) = 0) (hM : ∀ x, ‖q x‖ ≤ M)
    {ε a ai : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0)
    (hai : 0 ≤ ai) (hai1 : ai < 1)
    (hinner : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      ai < ‖x - torusCenter‖ → S.transportedScalar q t x = 0)
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {R ρ η : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16)
    (hsize : R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4)
    (hρa : ρ ≤ cellA / 4) (hηgap : η ≤ (1 - cellA) / 16)
    {N : ℕ} (hsep : ∀ p : FiniteCircularIndex N, 32 * ai ≤ finiteCircularInterfaceRadius R ρ p) :
    ∃ E : ℝ → (FiniteCircularIndex N → LittleContourSpace γ) →
        FiniteCircularIndex N → LittleContourSpace γ,
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ W, ‖W‖ < a / 4 →
        IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) W → ∀ i θ,
        LittleContourSpace.lift γ (E t W i) θ =
          S.physicalLabelComplexField q t (LittleContourSpace.lift γ (W i) θ)) ∧
      (∀ W, ‖W‖ < a / 4 →
        IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) W →
        ∃ K : ℝ≥0, ∃ V : Set (FiniteCircularIndex N → LittleContourSpace γ), V ∈ 𝓝 W ∧
          (∀ t, LipschitzOnWith K (E t) V) ∧ ∀ Z ∈ V, Continuous (fun t => E t Z)) ∧
      ∀ {D H : ℝ}, 0 < D → D < ε → 0 < H →
      ∀ (g : FiniteCircularIndex N → ℝ)
        (Z : ℝ → FiniteCircularIndex N → LittleContourSpace γ),
      (∀ t ∈ Ico (0 : ℝ) D, HasDerivAt Z
        (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g (Z t) + E t (Z t)) t) →
      (∀ t ∈ Ico (0 : ℝ) D,
        IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Z t) ∧ ‖Z t‖ < a / 4 ∧
        IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Z t)) →
      (∀ t ∈ Ioo (0 : ℝ) D, ∃ b : FiniteCircularIndex N → ℝ, ∀ p,
        ‖contourParameterShiftC1 (b p) (Z t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1) →
      ∃ δ > 0, δ ≤ H ∧ D + δ ≤ ε ∧
        ∃ Y : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        (∀ t ∈ Ico (0 : ℝ) D, Y t = Z t) ∧
        ContinuousOn Y (Icc (0 : ℝ) (D + δ)) ∧
        (∀ t ∈ Icc (0 : ℝ) (D + δ), HasDerivAt Y
          (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
            (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
            (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g (Y t) + E t (Y t)) t) ∧
        (∀ t ∈ Icc (0 : ℝ) (D + δ),
          IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
            (finiteCircularInterfaceRadius R ρ) (Y t) ∧ ‖Y t‖ < a / 4 ∧
          IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
            (finiteCircularInterfaceRadius R ρ) (Y t)) ∧
        ∀ t ∈ Icc (0 : ℝ) (D + δ), ∀ i θ,
          HasDerivAt (fun s => LittleContourSpace.lift γ (Y s i) θ)
            (contourBoundaryField g (fun j => LittleContourSpace.lift γ (Y t j)) i θ +
              S.physicalLabelComplexField q t (LittleContourSpace.lift γ (Y t i) θ)) t := by
  obtain ⟨E, hE, hlocal, B, hB, hbound⟩ := S.exists_finiteCircular_fixed_partial_forcing
    hS hwf hwper hwrot hmean hq hqper hqrot hqmean hM hε hεT ha ha16 hsupp
      hai hai1 hinner hγ hγ1 hR hρ hρ1 hη hηa hsize hsep
  refine ⟨E, hE, hlocal, ?_⟩
  intro D H hD hDε hH g Z hd hmem htube
  let J := min H (ε - D)
  have hJ : 0 < J := lt_min hH (sub_pos.mpr hDε)
  have hEbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :=
    hbound t ⟨ht.1, ht.2.trans hDε.le⟩
  obtain ⟨δ, hδ, hδJ, Y, hYZ, hYc, hYd, hYmem, hYb⟩ :=
    exists_finiteCircular_phase_tube_continuation_local_forcing
      hγ hγ1 hR hρ hρa hη hηa hηgap ha hsize hD hJ hB g E
      (fun W hWq hWa => hlocal W hWa hWq) hEbound Z hd hmem htube
  have hδε : D + δ ≤ ε := by
    have hh := hδJ.trans (min_le_right H (ε - D))
    linarith
  refine ⟨δ, hδ, hδJ.trans (min_le_left _ _), hδε, Y, hYZ, hYc, hYd, hYmem, ?_⟩
  intro t ht i θ
  have hh := hYb t ht i θ
  rw [hE t ⟨ht.1, ht.2.trans hδε⟩ (Y t) (hYmem t ht).2.1 (hYmem t ht).2.2 i θ] at hh
  exact hh

end BoundedEulerParticleSystem
end Euler2D

end
