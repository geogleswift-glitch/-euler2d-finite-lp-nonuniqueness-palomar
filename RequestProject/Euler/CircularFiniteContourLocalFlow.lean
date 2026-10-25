module

public import RequestProject.Euler.TorusForcedFiniteContourFlow
public import RequestProject.Euler.CircularFiniteContourDensity
public import RequestProject.Euler.TorusPhysicalCorrectionIdentity

/-! Actual finite circular initial contours evolve with the correction
from the same finite torus Euler system. The interval here may depend on
the cutoff; no uniform capture or density identification is asserted. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) circularLocalLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularLocalLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularLocalC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularLocalC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteEuler_localContourFlow {s A₀ b R ρ q T a : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hT : 0 < T) (hRa : (5 / 4) * R < a) (ha16 : a ≤ 1 / 16)
    (hsize : R * max ‖P.ancient s‖ ‖littleCircularReference hγ hγ1‖ < a / 4)
    (N : ℕ)
    (hZ : IsAdmissibleLittleContourFamily
      (finiteCircularReferenceC1 hγ hγ1 R ρ : FiniteCircularIndex N → ContourC1Space γ)
      (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N))
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T)
    (hS : IsFourfoldBoundedEulerParticleSystem S) :
    ∃ δ > 0, δ ≤ T ∧ ∃ Z : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
      Z 0 = finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N ∧
      ContinuousOn Z (Icc (0 : ℝ) δ) ∧
      (∀ t ∈ Icc (0 : ℝ) δ,
        IsAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Z t) ∧ ‖Z t‖ < a / 4) ∧
      ∀ t ∈ Icc (0 : ℝ) δ, ∀ i θ,
        HasDerivAt (fun τ => LittleContourSpace.lift γ (Z τ i) θ)
          (contourBoundaryField (finiteCircularInterfaceStrength A₀ b)
            (fun j => LittleContourSpace.lift γ (Z t j)) i θ +
            planeComplexEquiv (S.correctionLabelField t
              (complexTorusPoint (LittleContourSpace.lift γ (Z t i) θ)))) t := by
  have ha : 0 < a := lt_trans (by positivity : 0 < (5 / 4) * R) hRa
  have ha1 : a < 1 := by linarith
  obtain ⟨ε, hε, hεT, hsupp⟩ := P.exists_finiteEuler_short_support
    (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 hq hqE hT hRa ha1 N S
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with x hx hxbox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hxbox).trans hx.symm
  have hmean : (∫ x in torusBox, finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x) = 0 :=
    (integral_congr_ae hwf).symm.trans
      (P.integral_finiteInitialPeriodicDensity_zero hs hR hRmax hρ hρ1 N)
  let Zinit := finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
  have hZn : ‖Zinit‖ < a / 4 :=
    (norm_finiteCircularInitialContours_le hγ hγ1 hR hρ hρ1 (P.ancient s) N).trans_lt hsize
  obtain ⟨E, _, η, hη, δ, hδ, hδε, X, hX, hderiv⟩ :=
    S.exists_local_finiteContour_with_actual_correction hS hwf
      (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
      (P.finiteInitialPeriodicDensity_quarterTurn hs N) hmean hε hεT ha ha16 hsupp
      hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceStrength A₀ b) Zinit hZ hZn
  have hinit : Zinit ∈ ball Zinit η := mem_ball_self hη
  refine ⟨δ, hδ, hδε.trans hεT, fun t => X Zinit t, hX.initial Zinit hinit,
    hX.continuous Zinit hinit, ?_, ?_⟩
  · intro t ht
    exact ⟨(hX.mem Zinit hinit t ht).1, mem_ball_zero_iff.mp (hX.mem Zinit hinit t ht).2⟩
  · intro t ht i θ
    have hd := hderiv Zinit hinit t ht i θ
    rw [S.actualTorusCorrectionVelocity_physicalComplexSource hwf
      ⟨ht.1, ht.2.trans (hδε.trans hεT)⟩] at hd
    exact hd

end CircularMaterialTransferProfile

end Euler2D

end
