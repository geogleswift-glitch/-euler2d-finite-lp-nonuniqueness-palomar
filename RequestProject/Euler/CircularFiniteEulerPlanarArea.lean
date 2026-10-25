module

public import RequestProject.Euler.CircularFiniteEulerFamily
public import RequestProject.Euler.FourfoldBoundedEulerPlanarArea

/-! Choose the actual finite Euler system once, with the original
ancient-base datum, weak equation, fourfold symmetry and both global
planar volume identities needed by material stability. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteBase_fourfoldEuler_with_planar_area {s A₀ b R ρ q T : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hT : 0 ≤ T) (N : ℕ) :
    ∃ S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S ∧ IsWeakEulerSolution T
        (biotSavartL2 (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N))
        (particleVelocity (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
          S.backward S.backward_area) ∧
      ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume := by
  let f := finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
    (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N
  have hf := P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_torusBox] with x hfx hx
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx).trans hfx.symm
  have hmean : (∫ x in torusBox, f x) = 0 :=
    (integral_congr_ae (scalarLpLowerToTwo_ae hqE _)).trans
      (P.integral_finiteBaseTorusLp_zero hs hR hRmax hρ hρ1 hq N)
  have hB : ∀ᵐ x ∂μT, ‖f x‖ ≤ finiteInitialDensityBound A₀ b N := by
    filter_upwards [hf] with x hx
    rw [hx]
    exact P.norm_finiteInitialPlanarDensity_le hs N _
  obtain ⟨S, hS, harea⟩ := exists_fourfoldBoundedEulerParticleSystem_with_planar_area f hwf
    (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
    (P.finiteInitialPeriodicDensity_quarterTurn hs N) hT
    (finiteInitialDensityBound_nonneg A₀ b N) hB
  exact ⟨S, hS, S.weakEuler hT hmean (finiteInitialDensityBound_nonneg A₀ b N) hB, harea⟩

end CircularMaterialTransferProfile
end Euler2D

end