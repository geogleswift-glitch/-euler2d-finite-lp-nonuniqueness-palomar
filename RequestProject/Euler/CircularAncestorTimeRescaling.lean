module

public import RequestProject.Euler.CircularFiniteActivePhysicalGauge

/-! Every actual ancestor is slow on the current cell's original
physical clock. Reparametrization retains the same material path and
the same stage gauge, and does not create a new flow or reset a gauge. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Set
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

local instance ancestorTimeReal_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := (smul_smul a b Z).symm

theorem ampScale_ratio_eq_pow {A₀ b : ℝ} (hA : A₀ ≠ 0) (hb : b ≠ 0)
    {j k : ℕ} (hjk : j ≤ k) :
    ampScale A₀ b j / ampScale A₀ b k = b ^ (k - j) := by
  have hp : b ^ k = b ^ j * b ^ (k - j) := by rw [← pow_add, Nat.add_sub_of_le hjk]
  unfold ampScale
  rw [hp]
  field_simp
  <;> ring

theorem ancestor_ampScale_ratio_le {A₀ b : ℝ} (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    {j k : ℕ} (hjk : j < k) :
    0 < ampScale A₀ b j / ampScale A₀ b k ∧
      ampScale A₀ b j / ampScale A₀ b k ≤ b := by
  rw [ampScale_ratio_eq_pow hA.ne' hb.ne' hjk.le]
  refine ⟨pow_pos hb _, ?_⟩
  simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ k - j by omega)

theorem physicalTime_ancestor_common_clock {A₀ b : ℝ} (hA : 0 < A₀) (hb : 0 < b)
    (j k : ℕ) (τ : ℝ) :
    physicalTimeFromNormalized (ampScale A₀ b j) 0
        ((ampScale A₀ b j / ampScale A₀ b k) * τ) =
      physicalTimeFromNormalized (ampScale A₀ b k) 0 τ := by
  have hj : ampScale A₀ b j ≠ 0 := (div_pos hA (pow_pos hb j)).ne'
  unfold physicalTimeFromNormalized
  field_simp
  <;> ring

theorem hasDerivAt_same_ancestor_common_clock {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (y : ℝ → Fin 2 → LittleContourSpace γ)
    (p : Fin 2 → LittleContourSpace γ) (a τ : ℝ)
    (hy : HasDerivAt y (circularBanachField hγ hγ1 (y (a * τ)) + p) (a * τ)) :
    HasDerivAt (fun u => y (a * u))
      (a • (circularBanachField hγ hγ1 (y (a * τ)) + p)) τ := by
  exact hy.scomp τ (by simpa only [id_eq, mul_one] using (hasDerivAt_id τ).const_mul a)

theorem hasDerivAt_circular_slow_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (a τ : ℝ) :
    HasDerivAt (fun u => littleCircularMaterialContours hγ hγ1 (a * u))
      (a • circularBanachField hγ hγ1 (littleCircularMaterialContours hγ hγ1 (a * τ))) τ := by
  exact (littleCircularMaterialContours_hasDerivAt hγ hγ1 (a * τ)).scomp τ
    (by simpa only [id_eq, mul_one] using (hasDerivAt_id τ).const_mul a)

theorem circularAncestor_actual_initial_normalized {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {A r Ω : ℝ} (hr : r ≠ 0)
    (z : ℝ → Fin 2 → LittleContourSpace γ)
    (h0 : z 0 = r • littleCircularReference hγ hγ1) :
    rigidRotationGauge (Ω / A) 0 0 • normalizedPhysicalCurve A r 0 z 0 =
      littleCircularMaterialContours hγ hγ1 0 := by
  rw [rigidRotationGauge_entrance, one_smul, normalizedPhysicalCurve_initial, h0,
    inv_smul_smul₀ hr]
  funext i
  simp only [littleCircularMaterialContours, mul_zero, Real.cos_zero, Real.sin_zero,
    one_smul, zero_smul, add_zero]

end Euler2D

end
