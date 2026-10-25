module

public import RequestProject.Euler.TorusInnerLabelLittleForcing
public import RequestProject.Euler.TorusFinitePhaseFixedForcing

/-! Actual local material evolution of the active interfaces. The same
Euler inner label is kept as a rough source, and only target neighborhoods
separated from that source enter the Banach existence argument. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_local_finitePhase_with_actual_inner
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (hmean : (∫ x in torusBox, f x) = 0)
    {q : R2 → ℝ} {M : ℝ} (hq : MemLp q 2 μT) (hqper : IsTorusPeriodic q)
    (hqrot : ∀ x, q (torusQuarterTurn x) = q x)
    (hqmean : (∫ x in torusBox, q x) = 0) (hM : ∀ x, ‖q x‖ ≤ M)
    {ε a ainner : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0)
    (hai : 0 ≤ ainner) (hai1 : ainner < 1)
    (hinner : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      ainner < ‖x - torusCenter‖ → S.transportedScalar q t x = 0)
    {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z)
    (hZq : IsQuarterPhaseLittleContourFamily Z₀ r Z) (hZa : ‖Z‖ < a / 4)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (hsep : ∀ i, 16 * ainner ≤ d i)
    (hZd : ∀ i x, d i ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖) :
    ∃ δ > 0, δ ≤ ε ∧
      ∃ X : (ι → LittleContourSpace γ) → ℝ → ι → LittleContourSpace γ,
        ∃ ρ > 0,
          (∀ W ∈ ball Z ρ, X W 0 = W) ∧
          (∀ W ∈ ball Z ρ, ContinuousOn (X W) (Icc (0 : ℝ) δ)) ∧
          (∀ W ∈ ball Z ρ, ∀ t ∈ Icc (0 : ℝ) δ,
            IsPhaseAdmissibleLittleContourFamily Z₀ r (X W t) ∧
            ‖X W t‖ < a / 4 ∧ IsQuarterPhaseLittleContourFamily Z₀ r (X W t)) ∧
          ∀ W ∈ ball Z ρ, ∀ t ∈ Icc (0 : ℝ) δ, ∀ i θ,
            HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
              (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ +
                S.physicalLabelComplexField q t (LittleContourSpace.lift γ (X W t i) θ)) t := by
  obtain ⟨Kc, Ec, hEcLip, hEcc, _hEcraw, hEc⟩ := S.exists_finitePhase_fixed_actual_forcing (ι := ι)
    hS hwf hwper hwrot hmean hε hεT ha ha16 hsupp hγ1.le
  obtain ⟨Ei, Ki, Ui, hUi, hEiLip, hEic, hEi⟩ := S.exists_finitePhase_actualInner_forcing
    hS hq hqper hqrot hqmean hM hε hεT hai hai1 hinner hγ1.le d hd hsep Z hZd
  let U : Set (ι → LittleContourSpace γ) := Ui ∩
    (ball 0 (a / 4) ∩ {W | IsQuarterPhaseLittleContourFamily Z₀ r W})
  have hU : U ∈ 𝓝 Z := inter_mem hUi
    (inter_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hZa))
      ((isOpen_quarterPhaseLittleContourFamilies Z₀ r).mem_nhds hZq))
  let E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ := fun t W => Ei t W + Ec t W
  have hELip (t : ℝ) (_ht : t ∈ Icc (-ε) ε) : LipschitzOnWith (Ki + Kc) (E t) U :=
    ((hEiLip t).mono inter_subset_left).add ((hEcLip t).mono (fun _ h => h.2.1))
  have hEt (W : ι → LittleContourSpace γ) (hW : W ∈ U) :
      ContinuousOn (fun t => E t W) (Icc (-ε) ε) :=
    ((hEic W hW.1).add (hEcc W hW.2.1)).continuousOn
  obtain ⟨ρ, hρ, δ, hδ, hδε, X, hX, hderiv⟩ :=
    exists_finitePhase_forced_local_flow hγ hγ1 Z₀ r hr href g Z hZ E hε hU hELip hEt
  refine ⟨δ, hδ, hδε, X, ρ, hρ, hX.initial, hX.continuous, ?_, ?_⟩
  · intro W hW t ht
    exact ⟨(hX.mem W hW t ht).1,
      mem_ball_zero_iff.mp (hX.mem W hW t ht).2.2.1, (hX.mem W hW t ht).2.2.2⟩
  · intro W hW t ht i θ
    have htε : t ∈ Icc (0 : ℝ) ε := ⟨ht.1, ht.2.trans hδε⟩
    have hmem := (hX.mem W hW t ht).2
    have hd0 := hderiv W hW t ht i θ
    change HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
      (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ +
        (LittleContourSpace.lift γ (Ei t (X W t) i) θ +
          LittleContourSpace.lift γ (Ec t (X W t) i) θ)) t at hd0
    rw [hEi t htε (X W t) hmem.1 i θ,
      hEc t htε (X W t) (mem_ball_zero_iff.mp hmem.2.1) i θ] at hd0
    simpa only [S.physicalLabelComplexField_eq] using hd0

end BoundedEulerParticleSystem
end Euler2D

end
