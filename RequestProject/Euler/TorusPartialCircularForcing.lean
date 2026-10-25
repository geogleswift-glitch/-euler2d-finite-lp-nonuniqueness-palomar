module

public import RequestProject.Euler.TorusPartialFixedForcing
public import RequestProject.Euler.FiniteQuarterTargetSeparation
public import RequestProject.Euler.CircularFiniteLocalForcingTubeContinuation

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

theorem exists_finiteCircular_fixed_partial_forcing
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
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) ε,
        ∀ W : FiniteCircularIndex N → LittleContourSpace γ,
        (∃ b : FiniteCircularIndex N → ℝ, ∀ p,
          ‖contourParameterShiftC1 (b p) (W p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
            η * radScale R ρ p.1) → ‖E t W‖ ≤ B := by
  let Ref := finiteCircularReferenceC1 hγ hγ1 R ρ (N := N)
  let r := finiteCircularInterfaceRadius R ρ (N := N)
  have hr (p : FiniteCircularIndex N) : 0 < r p := finiteCircularInterfaceRadius_pos hR hρ p
  have href (p : FiniteCircularIndex N) : ContourC1Space.lift γ (Ref p) = refCircle (r p) :=
    lift_finiteCircularReferenceC1 hγ hγ1 R ρ p
  let d : FiniteCircularIndex N → ℝ := fun p => r p / 2
  have hd (p : FiniteCircularIndex N) : 0 < d p := half_pos (hr p)
  have hsep' (p : FiniteCircularIndex N) : 16 * ai ≤ d p := by
    dsimp only [d]
    have hh := hsep p
    change 32 * ai ≤ r p at hh
    linarith
  let L := R * (‖littleCircularReference hγ hγ1‖ + η)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  obtain ⟨E, hE, _htime, hlocal, B, hB, hbound⟩ := S.exists_finitePhase_fixed_partial_forcing
    hS hwf hwper hwrot hmean hq hqper hqrot hqmean hM hε hεT ha ha16 hsupp
      hai hai1 hinner hL hsize hγ1.le d hd hsep'
  have htarget (W : FiniteCircularIndex N → LittleContourSpace γ)
      (hW : IsQuarterPhaseLittleContourFamily Ref r W) :
      ∀ p x, d p ≤ ‖ContourC1Space.toBCF γ (W p).val x‖ :=
    quarterPhase_target_radius_lower Ref r hr href hW
  have htargetHalf (W : FiniteCircularIndex N → LittleContourSpace γ)
      (hW : IsQuarterPhaseLittleContourFamily Ref r W) (p : FiniteCircularIndex N) (x : ContourCircle) :
      d p / 2 ≤ ‖ContourC1Space.toBCF γ (W p).val x‖ := by
    have hh := htarget W hW p x
    have hp := hd p
    linarith
  have hquarter {W : FiniteCircularIndex N → LittleContourSpace γ}
      (hW : ∃ b : FiniteCircularIndex N → ℝ, ∀ p,
        ‖contourParameterShiftC1 (b p) (W p).val - Ref p‖ ≤ η * radScale R ρ p.1) :
      IsQuarterPhaseLittleContourFamily Ref r W := by
    obtain ⟨b, hb⟩ := hW
    refine ⟨b, ?_⟩
    intro p
    have hrad := (circularContourRadii_bounds p.2).2.1
    have hsmall : η < circularContourRadii p.2 / 4 := by linarith [cellA_pos]
    have hm := mul_lt_mul_of_pos_right hsmall (radScale_pos hR hρ p.1)
    exact (hb p).trans_lt (by dsimp only [r, finiteCircularInterfaceRadius]; nlinarith only [hm])
  refine ⟨E, ?_, ?_, B, hB, ?_⟩
  · intro t ht W hWa hW i θ
    exact hE t ht W hWa (htargetHalf W hW) i θ
  · intro W hWa hW
    exact hlocal W hWa (htarget W hW)
  · intro t ht W hW
    have hnorm : ‖W‖ ≤ L :=
      norm_finiteCircular_closedPhaseTube_le hγ hγ1 hR hρ hρ1 hη hW
    exact hbound t ht W hnorm (htargetHalf W (hquarter hW))

end BoundedEulerParticleSystem
end Euler2D

end
