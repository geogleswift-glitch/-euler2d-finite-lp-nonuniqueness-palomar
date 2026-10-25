module

public import Mathlib

/-! Actual bounded sequence Green operators for backward orbits.
The stable future convolution is summed in operator norm, using a true
power bound strictly below the chosen sequence weight. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def natSequenceShiftCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.compContinuous ⟨fun n => n + k, continuous_of_discreteTopology⟩
      map_add' := fun f g => by ext n; rfl
      map_smul' := fun a f => by ext n; rfl }
    1 (fun f => by
      change ‖f.compContinuous ⟨fun n => n + k, continuous_of_discreteTopology⟩‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using
        BoundedContinuousFunction.norm_compContinuous_le f
          ⟨fun n => n + k, continuous_of_discreteTopology⟩)

theorem natSequenceShiftCLM_apply (k : ℕ) (f : ℕ →ᵇ E) (n : ℕ) :
    natSequenceShiftCLM E k f n = f (n + k) := rfl

def stableSequenceGreenTermCLM (ρ : ℝ) (A : E →L[ℝ] E) (k : ℕ) :
    (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  (ρ⁻¹) ^ (k + 1) • ((A ^ k).compLeftContinuousBounded ℕ).comp (natSequenceShiftCLM E (k + 1))

theorem stableSequenceGreenTermCLM_apply (ρ : ℝ) (A : E →L[ℝ] E)
    (k : ℕ) (f : ℕ →ᵇ E) (n : ℕ) :
    stableSequenceGreenTermCLM ρ A k f n =
      (ρ⁻¹) ^ (k + 1) • (A ^ k) (f (n + (k + 1))) := rfl

theorem norm_stableSequenceGreenTermCLM_le {ρ : ℝ} (hρ : 0 < ρ) (A : E →L[ℝ] E) (k : ℕ) :
    ‖stableSequenceGreenTermCLM ρ A k‖ ≤ (ρ⁻¹) ^ (k + 1) * ‖A ^ k‖ := by
  have hw : 0 ≤ (ρ⁻¹) ^ (k + 1) := pow_nonneg (inv_nonneg.mpr hρ.le) _
  apply (stableSequenceGreenTermCLM ρ A k).opNorm_le_bound (mul_nonneg hw (norm_nonneg _))
  intro f
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (mul_nonneg hw (norm_nonneg _)) (norm_nonneg f))).mpr
  intro n
  rw [stableSequenceGreenTermCLM_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  calc
    _ ≤ (ρ⁻¹) ^ (k + 1) * (‖A ^ k‖ * ‖f (n + (k + 1))‖) :=
      mul_le_mul_of_nonneg_left ((A ^ k).le_opNorm _) hw
    _ ≤ (ρ⁻¹) ^ (k + 1) * (‖A ^ k‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm f _) (norm_nonneg _)) hw
    _ = _ := by ring

theorem norm_stableSequenceGreenTermCLM_le_geometric {ρ β C : ℝ}
    (hρ : 0 < ρ) (A : E →L[ℝ] E) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k) (k : ℕ) :
    ‖stableSequenceGreenTermCLM ρ A k‖ ≤ (C / ρ) * (β / ρ) ^ k := by
  calc
    _ ≤ (ρ⁻¹) ^ (k + 1) * ‖A ^ k‖ := norm_stableSequenceGreenTermCLM_le hρ A k
    _ ≤ (ρ⁻¹) ^ (k + 1) * (C * β ^ k) :=
      mul_le_mul_of_nonneg_left (hA k) (pow_nonneg (inv_nonneg.mpr hρ.le) _)
    _ = _ := by simp only [pow_succ, div_eq_mul_inv, mul_pow]; ring

variable [CompleteSpace E]

theorem summable_stableSequenceGreenTermCLM {ρ β C : ℝ}
    (hρ : 0 < ρ) (hβ0 : 0 ≤ β) (hβρ : β < ρ) (A : E →L[ℝ] E)
    (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k) :
    Summable (stableSequenceGreenTermCLM ρ A) := by
  have hr : ‖β / ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hβ0 hρ.le)]
    exact (div_lt_one hρ).mpr hβρ
  exact ((summable_geometric_of_norm_lt_one hr).mul_left (C / ρ)).of_norm_bounded
    (fun k => norm_stableSequenceGreenTermCLM_le_geometric hρ A hA k)

def stableSequenceGreenCLM (ρ : ℝ) (A : E →L[ℝ] E) :
    (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) := ∑' k : ℕ, stableSequenceGreenTermCLM ρ A k

theorem norm_stableSequenceGreenCLM_le {ρ β C : ℝ}
    (hρ : 0 < ρ) (hβ0 : 0 ≤ β) (hβρ : β < ρ) (A : E →L[ℝ] E)
    (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k) :
    ‖stableSequenceGreenCLM ρ A‖ ≤ C / (ρ - β) := by
  have hr : ‖β / ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hβ0 hρ.le)]
    exact (div_lt_one hρ).mpr hβρ
  have hb := tsum_of_norm_bounded ((summable_geometric_of_norm_lt_one hr).mul_left (C / ρ)).hasSum
    (fun k => norm_stableSequenceGreenTermCLM_le_geometric hρ A hA k)
  change ‖∑' k : ℕ, stableSequenceGreenTermCLM ρ A k‖ ≤ _
  calc
    _ ≤ ∑' k : ℕ, (C / ρ) * (β / ρ) ^ k := hb
    _ = (C / ρ) * (1 - β / ρ)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
    _ = C / (ρ - β) := by
      field_simp [hρ.ne', (sub_pos.mpr hβρ).ne', (sub_pos.mpr ((div_lt_one hρ).mpr hβρ)).ne'] <;> ring

end Euler2D

end
