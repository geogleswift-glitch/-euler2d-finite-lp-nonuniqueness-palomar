module

public import RequestProject.Euler.TorusClampedContourForcing

/-! The time-continuous Little forcing for the same actual finite Euler
family and its complete finite patch density. The nonempty support window
and every temporal regularity hypothesis are obtained from that family. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteEuler_contourCorrection {s A₀ b R ρ q T a : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hT : 0 < T) (hRa : (5 / 4) * R < a) (ha16 : a ≤ 1 / 16) (N : ℕ)
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T)
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {η : ℝ≥0} (hη1 : (η : ℝ) ≤ 1) :
    ∃ ε > 0, ε ≤ T ∧ ∃ K : ℝ≥0,
      ∃ E : ℝ → LittleContourSpace η → LittleContourSpace η,
        (∀ t, LipschitzOnWith K (E t) (ball 0 (a / 4))) ∧
        (∀ Z ∈ ball (0 : LittleContourSpace η) (a / 4), Continuous (fun t => E t Z)) ∧
        (∀ t ∈ Icc (0 : ℝ) ε, ∀ Z, ‖Z‖ < a / 4 → ∀ θ,
          LittleContourSpace.lift η (E t Z) θ =
            actualTorusCorrectionVelocity
              (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
              (LittleContourSpace.lift η Z θ)) := by
  have ha : 0 < a := lt_trans (by positivity : 0 < (5 / 4) * R) hRa
  have ha1 : a < 1 := by linarith
  obtain ⟨ε, hε, hεT, hsupport⟩ := P.exists_finiteEuler_short_support
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
  obtain ⟨K, E, _, hLip, hcont, hlift⟩ := S.exists_clamped_actualTorusCorrection_LittleField
    hS hwf (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
    (P.finiteInitialPeriodicDensity_quarterTurn hs N) hmean hε hεT ha ha16 hsupport hη1
  exact ⟨ε, hε, hεT, K, E, hLip, hcont, hlift⟩

end CircularMaterialTransferProfile
end Euler2D

end
