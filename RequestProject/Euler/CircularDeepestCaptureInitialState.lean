module

public import RequestProject.Euler.CircularCanonicalInitialState
public import RequestProject.Euler.CircularCanonicalCurrentCoordinates
public import RequestProject.Euler.CircularFiniteStageRadialSupport

/-! The first capture uses fixed original ancient data, independently
of the provisional actual path. The deepest prefix has no omitted
inner labels and has a genuine positive particle buffer. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem canonicalPrefixAlignedCurrentCell_zero_entrance {γ : ℝ≥0}
    (A₀ b R ρ : ℝ) (k : ℕ) (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) :
    canonicalPrefixAlignedCurrentCell A₀ b R ρ k 0 X τ =
      canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X τ (Fin.last k) := by
  have hz : circularRetardedMaterialShift 0 0 = (0 : Fin 2 → ℝ) := by
    funext i
    simp only [circularRetardedMaterialShift, neg_zero, mul_zero, sub_zero, Pi.zero_apply]
  simp only [canonicalPrefixAlignedCurrentCell, mul_zero, hz, contourParameterShiftFamilyCLM_zero]

theorem exists_deepest_prefix_particle_buffer {R ρ : ℝ} (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    ∃ ai > 0, ai < 1 ∧ ∀ p : FiniteCircularIndex N, 32 * ai ≤ finiteCircularInterfaceRadius R ρ p := by
  let ai := cellA * radScale R ρ N / 64
  have hrN : 0 < radScale R ρ N := radScale_pos hR hρ N
  have hrNR : radScale R ρ N ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hprod : cellA * radScale R ρ N ≤ R :=
    (mul_le_of_le_one_left hrN.le cellA_lt_one.le).trans hrNR
  refine ⟨ai, div_pos (mul_pos cellA_pos hrN) (by norm_num), ?_, ?_⟩
  · dsimp only [ai]
    nlinarith only [hprod, hRmax]
  · intro p
    have hrp : 0 < radScale R ρ p.1 := radScale_pos hR hρ p.1
    have hrNp : radScale R ρ N ≤ radScale R ρ p.1 := by
      by_cases hj : (p.1 : ℕ) = N
      · rw [hj]
      · have hjN : (p.1 : ℕ) < N := by have hp := p.1.isLt; omega
        exact (radScale_le_ratio_of_lt hR hρ hρ1 hjN).trans
          (mul_le_of_le_one_left hrp.le hρ1)
    have h1 := mul_le_mul_of_nonneg_left hrNp cellA_pos.le
    have h2 := mul_le_mul_of_nonneg_left (circularContourRadii_bounds p.2).2.1 hrp.le
    change 32 * ai ≤ radScale R ρ p.1 * circularContourRadii p.2
    dsimp only [ai]
    nlinarith only [h1, h2, mul_pos cellA_pos hrN]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteInnerActiveInitialLabels_deepest (s A₀ b R ρ : ℝ) (N : ℕ) :
    P.finiteInnerActiveInitialLabels s A₀ b R ρ N N = ∅ := by
  ext z
  simp only [finiteInnerActiveInitialLabels, Finset.Ico_self, Finset.notMem_empty, false_and,
    exists_false, and_false, mem_setOf_eq, Set.notMem_empty]

theorem actualCanonicalPrefix_initial_aligned_deepest
    {s A₀ b R ρ a Hglob D : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (N : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (X : ℝ → FiniteCircularIndex N → LittleContourSpace γ)
    (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ le_rfl S D X) :
    canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X 0 = P.ancient s := by
  rw [canonicalPrefixAlignedCurrentCell_zero_entrance]
  exact P.actualCanonicalPrefix_initial_deepest hR hρ N S X hX

theorem actualCanonicalPrefix_initial_deepest_deviation
    {s A₀ b R ρ a Hglob D : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (N : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (X : ℝ → FiniteCircularIndex N → LittleContourSpace γ)
    (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ le_rfl S D X) :
    canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X 0 N =
      P.ancient s - littleCircularReference hγ hγ1 := by
  unfold canonicalPrefixStageDeviation
  simp only [canonicalPrefixAbsoluteFamily, dif_pos (le_refl N), mul_zero, add_zero,
    littleCircularMaterialContours_zero]
  change canonicalPrefixAbsoluteCell A₀ b R ρ N 0 X 0 (Fin.last N) - _ = _
  rw [P.actualCanonicalPrefix_initial_deepest hR hρ N S X hX]

theorem norm_ancient_sub_reference_le {s η : ℝ} (hη : 0 ≤ η)
    (hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) :
    ‖P.ancient s - littleCircularReference hγ hγ1‖ ≤ η := by
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro i
  exact hancient i

end CircularMaterialTransferProfile
end Euler2D

end
