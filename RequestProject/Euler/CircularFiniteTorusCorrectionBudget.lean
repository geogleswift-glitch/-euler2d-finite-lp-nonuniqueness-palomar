module

public import RequestProject.Euler.CircularFiniteSourceMass
public import RequestProject.Euler.UniformActualTorusContourBudget

/-! The true finite torus correction has the original R⁸(bρ²)^j
relative contour budget. The constant is uniform in physical shrinking,
the cutoff N and the chosen ancient entry time. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteEuler_uniformTorusCorrection_labelBudget :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 < A₀) (_hb : 0 < b)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
        (_hsmall : ρ ^ 2 < b) (_hc : 0 < c) (_hc16 : c * R ≤ 1 / 16),
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ t ∈ Icc (0 : ℝ) T,
      (∀ x ∈ torusBox, c * R < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0) →
      ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 → ∀ (j : ℕ) {L : ℝ}, 0 ≤ L →
      (L + 1) * radScale R ρ j ≤ (c * R) / 2 →
      ∀ Z : LittleContourSpace η, ‖Z‖ ≤ L * radScale R ρ j →
      ∀ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        actualTorusCorrectionVelocity
          (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
          (LittleContourSpace.lift η Z θ)) →
      ‖Q‖ / (ampScale A₀ b j * radScale R ρ j) ≤
        C * torusCorrectionContourBudget (η : ℝ) L * c ^ 4 *
          circularFiniteL1Coefficient b ρ * R ^ 8 * (b * ρ ^ 2) ^ j := by
  obtain ⟨C, hC, hbudget⟩ := exists_uniform_actualTorusCorrection_contourLittle_budget
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T c _ hs hA hb hR hRmax hρ hρ1 hq hqE hsmall hc hc16 N S hS
    t ht hsupp η hη j L hL hgeom Z hZ Q hQ
  let w := P.finiteInitialPeriodicDensity s A₀ b R ρ N
  have hwf : w =ᵐ[μT] (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with x hx hxbox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hxbox).trans hx.symm
  have hmean : (∫ x in torusBox, finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x) = 0 :=
    (integral_congr_ae hwf).symm.trans
      (P.integral_finiteInitialPeriodicDensity_zero hs hR hRmax hρ hρ1 N)
  have hrj : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  have hAj : 0 < ampScale A₀ b j := div_pos hA (pow_pos hb j)
  have hactual := hbudget (mul_pos hc hR) hc16 hη (S.physicalComplexSource w t)
    (S.integrable_physicalComplexSource hwf t) (S.physicalComplexSource_support hsupp)
    ((S.integral_physicalComplexSource hwf t).trans hmean)
    (S.physicalComplexSource_fourfold hS
      (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
      (P.finiteInitialPeriodicDensity_quarterTurn hs N) (by linarith) ht hsupp)
    hrj hL hgeom Z hZ Q hQ
  have hmass := S.physicalComplexSource_fourthAbsoluteMoment_le_initialL1 hwf hsupp
  have hf := P.integral_abs_finiteBaseCurlL2_le hs hA.le hb hR hρ hq hqE hsmall N
  rw [finiteBaseNormBound_one_eq] at hf
  have hfour : (∫ z : ℂ, ‖z‖ ^ 4 * |S.physicalComplexSource w t z|) ≤
      (c * R) ^ 4 * (circularFiniteL1Coefficient b ρ * (A₀ * R ^ 2)) :=
    hmass.trans (mul_le_mul_of_nonneg_left hf (by positivity))
  have hB : 0 ≤ torusCorrectionContourBudget (η : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hnorm := hactual.trans (mul_le_mul_of_nonneg_left hfour (by positivity))
  calc
    ‖Q‖ / (ampScale A₀ b j * radScale R ρ j) =
        (‖Q‖ / radScale R ρ j) / ampScale A₀ b j := by rw [div_div]; ring
    _ ≤ (C * torusCorrectionContourBudget (η : ℝ) L * (radScale R ρ j) ^ 2 *
        ((c * R) ^ 4 * (circularFiniteL1Coefficient b ρ * (A₀ * R ^ 2)))) /
          ampScale A₀ b j := div_le_div_of_nonneg_right hnorm hAj.le
    _ = _ := by
      have hp : (ρ ^ 2) ^ j = (ρ ^ j) ^ 2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 j]
      rw [mul_pow b (ρ ^ 2) j, hp]
      unfold ampScale radScale
      field_simp [hA.ne', hb.ne']
      <;> ring

end CircularMaterialTransferProfile
end Euler2D

end
