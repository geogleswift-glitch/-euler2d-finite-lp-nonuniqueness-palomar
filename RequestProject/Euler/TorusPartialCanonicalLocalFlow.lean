module

public import RequestProject.Euler.TorusPartialCanonicalForcing

/-! A local trajectory of the one actual partial contour equation.
Only a neighborhood of the initial separated target is used for the
nonautonomous Banach existence theorem. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_local_finiteCircular_actual_partial
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
    {N : ℕ} (hsep : ∀ p : FiniteCircularIndex N, 32 * ai ≤ finiteCircularInterfaceRadius R ρ p)
    (g : FiniteCircularIndex N → ℝ) (Zinit : FiniteCircularIndex N → LittleContourSpace γ)
    (hinit : IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) Zinit ∧ ‖Zinit‖ < a / 4 ∧
      IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) Zinit) :
    ∃ δ > 0, δ ≤ ε ∧ ∃ Z : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
      Z 0 = Zinit ∧ ContinuousOn Z (Icc (0 : ℝ) δ) ∧
      (∀ t ∈ Icc (0 : ℝ) δ, HasDerivAt Z
        (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g (Z t) +
            S.actualPartialContourForcing q t (Z t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) δ,
        IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Z t) ∧ ‖Z t‖ < a / 4 ∧
        IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Z t)) ∧
      ∀ t ∈ Icc (0 : ℝ) δ, ∀ i θ,
        HasDerivAt (fun u => LittleContourSpace.lift γ (Z u i) θ)
          (contourBoundaryField g (fun j => LittleContourSpace.lift γ (Z t j)) i θ +
            S.physicalLabelComplexField q t (LittleContourSpace.lift γ (Z t i) θ)) t := by
  obtain ⟨E, hE, hlocal, _B, _hB, _hbound⟩ := S.exists_finiteCircular_fixed_partial_forcing
    hS hwf hwper hwrot hmean hq hqper hqrot hqmean hM hε hεT ha ha16 hsupp
      hai hai1 hinner hγ hγ1 hR hρ hρ1 hη hηa hsize hsep
  obtain ⟨K, V, hV, hELip, hEc⟩ := hlocal Zinit hinit.2.1 hinit.2.2
  let U : Set (FiniteCircularIndex N → LittleContourSpace γ) := V ∩
    (ball 0 (a / 4) ∩ {W | IsQuarterPhaseLittleContourFamily
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) W})
  have hU : U ∈ 𝓝 Zinit := inter_mem hV (inter_mem
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hinit.2.1))
    ((isOpen_quarterPhaseLittleContourFamilies _ _).mem_nhds hinit.2.2))
  obtain ⟨r, hr, δ, hδ, hδε, X, hX, hmat⟩ :=
    exists_finitePhase_time_restart hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g Zinit hinit.1 E hε hU
      (fun t => (hELip t).mono inter_subset_left)
      (fun W hW => hEc W hW.1) 0
  have hball : Zinit ∈ ball Zinit r := mem_ball_self hr
  let Z := X Zinit
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) δ) :
      IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (Z t) ∧ ‖Z t‖ < a / 4 ∧
      IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (Z t) := by
    have hh := hX.mem Zinit hball t ht
    exact ⟨hh.1, mem_ball_zero_iff.mp hh.2.2.1, hh.2.2.2⟩
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) δ) :
      S.actualPartialContourForcing q t (Z t) = E t (Z t) :=
    S.actualPartialContourForcing_eq_of_lift
      (hE t ⟨ht.1, ht.2.trans hδε⟩ (Z t) (hmem t ht).2.1 (hmem t ht).2.2)
  refine ⟨δ, hδ, hδε, Z, hX.initial Zinit hball, hX.continuous Zinit hball, ?_, hmem, ?_⟩
  · intro t ht
    rw [heq t ht]
    simpa only [zero_add, Z] using hX.hasDerivAt Zinit hball t ht
  · intro t ht i θ
    have hh := hmat Zinit hball t ht i θ
    simp only [zero_add] at hh
    rw [hE t ⟨ht.1, ht.2.trans hδε⟩ (Z t) (hmem t ht).2.1 (hmem t ht).2.2 i θ] at hh
    exact hh

end BoundedEulerParticleSystem
end Euler2D

end
