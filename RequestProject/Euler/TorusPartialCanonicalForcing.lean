module

public import RequestProject.Euler.TorusPartialCircularContinuation

/-! One actual partial forcing, independent of the auxiliary support
window used to prove its regularity. Whenever a Little representation
of the literal physical velocity exists, it is unique. Thus the
different clamped fields used at local restarts agree with this single
field on their actual physical domains. No regularity is asserted
outside those domains. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def actualPartialContourForcing (q : R2 → ℝ) {γ : ℝ≥0} {ι : Type*}
    (t : ℝ) (W : ι → LittleContourSpace γ) : ι → LittleContourSpace γ := by
  classical
  exact if h : ∃ Q : ι → LittleContourSpace γ, ∀ i θ,
      LittleContourSpace.lift γ (Q i) θ =
        S.physicalLabelComplexField q t (LittleContourSpace.lift γ (W i) θ)
    then h.choose else 0

theorem actualPartialContourForcing_eq_of_lift {q : R2 → ℝ} {γ : ℝ≥0} {ι : Type*}
    {t : ℝ} {W Q : ι → LittleContourSpace γ}
    (hQ : ∀ i θ, LittleContourSpace.lift γ (Q i) θ =
      S.physicalLabelComplexField q t (LittleContourSpace.lift γ (W i) θ)) :
    S.actualPartialContourForcing q t W = Q := by
  classical
  have h : ∃ Q : ι → LittleContourSpace γ, ∀ i θ,
      LittleContourSpace.lift γ (Q i) θ =
        S.physicalLabelComplexField q t (LittleContourSpace.lift γ (W i) θ) := ⟨Q, hQ⟩
  unfold actualPartialContourForcing
  rw [dif_pos h]
  funext i
  exact littleContour_eq_of_lift_eq fun θ => (h.choose_spec i θ).trans (hQ i θ).symm

theorem exists_finiteCircular_actual_partial_continuation
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
    {N : ℕ} (hsep : ∀ p : FiniteCircularIndex N, 32 * ai ≤ finiteCircularInterfaceRadius R ρ p)
    {D H : ℝ} (hD : 0 < D) (hDε : D < ε) (hH : 0 < H)
    (g : FiniteCircularIndex N → ℝ)
    (Z : ℝ → FiniteCircularIndex N → LittleContourSpace γ)
    (hd : ∀ t ∈ Ico (0 : ℝ) D, HasDerivAt Z
      (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g (Z t) +
          S.actualPartialContourForcing q t (Z t)) t)
    (hmem : ∀ t ∈ Ico (0 : ℝ) D,
      IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (Z t) ∧ ‖Z t‖ < a / 4 ∧
      IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (Z t))
    (htube : ∀ t ∈ Ioo (0 : ℝ) D, ∃ β : FiniteCircularIndex N → ℝ, ∀ p,
      ‖contourParameterShiftC1 (β p) (Z t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
        η * radScale R ρ p.1) :
    ∃ δ > 0, δ ≤ H ∧ D + δ ≤ ε ∧
      ∃ Y : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
      (∀ t ∈ Ico (0 : ℝ) D, Y t = Z t) ∧
      ContinuousOn Y (Icc (0 : ℝ) (D + δ)) ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ), HasDerivAt Y
        (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g (Y t) +
            S.actualPartialContourForcing q t (Y t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ),
        IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Y t) ∧ ‖Y t‖ < a / 4 ∧
        IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Y t)) ∧
      ∀ t ∈ Icc (0 : ℝ) (D + δ), ∀ i θ,
        HasDerivAt (fun s => LittleContourSpace.lift γ (Y s i) θ)
          (contourBoundaryField g (fun j => LittleContourSpace.lift γ (Y t j)) i θ +
            S.physicalLabelComplexField q t (LittleContourSpace.lift γ (Y t i) θ)) t := by
  obtain ⟨E, hE, _hlocal, hcontinue⟩ := S.exists_finiteCircular_partial_continuation_field
    hS hwf hwper hwrot hmean hq hqper hqrot hqmean hM hε hεT ha ha16 hsupp
      hai hai1 hinner hγ hγ1 hR hρ hρ1 hη hηa hsize hρa hηgap hsep
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ε) (W : FiniteCircularIndex N → LittleContourSpace γ)
      (hWa : ‖W‖ < a / 4)
      (hWq : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) W) : S.actualPartialContourForcing q t W = E t W :=
    S.actualPartialContourForcing_eq_of_lift (hE t ht W hWa hWq)
  have hdE : ∀ t ∈ Ico (0 : ℝ) D, HasDerivAt Z
      (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g (Z t) + E t (Z t)) t := by
    intro t ht
    have hh := hd t ht
    rw [heq t ⟨ht.1, ht.2.le.trans hDε.le⟩ (Z t) (hmem t ht).2.1 (hmem t ht).2.2] at hh
    exact hh
  obtain ⟨δ, hδ, hδH, hδε, Y, hYZ, hYc, hYd, hYmem, hYmat⟩ :=
    hcontinue hD hDε hH g Z hdE hmem htube
  refine ⟨δ, hδ, hδH, hδε, Y, hYZ, hYc, ?_, hYmem, hYmat⟩
  intro t ht
  rw [heq t ⟨ht.1, ht.2.trans hδε⟩ (Y t) (hYmem t ht).2.1 (hYmem t ht).2.2]
  exact hYd t ht

end BoundedEulerParticleSystem
end Euler2D

end
