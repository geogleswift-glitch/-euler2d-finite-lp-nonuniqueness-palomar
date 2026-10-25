module

public import RequestProject.Euler.BanachSequenceGreen

/-! A genuine causal sequence Green operator for the expanding
direction, constructed from bounded zero-padded shifts and an actually
convergent operator series. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def natSequencePastShift (k : ℕ) (f : ℕ →ᵇ E) : ℕ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => if k < n then f (n - k) else 0) ‖f‖ (by
      intro n
      split_ifs
      · exact BoundedContinuousFunction.norm_coe_le_norm f _
      · simpa only [norm_zero] using (norm_nonneg f))

def natSequencePastShiftCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := natSequencePastShift k
      map_add' := fun f g => by
        ext n
        change (if k < n then (f + g) (n - k) else 0) =
          (if k < n then f (n - k) else 0) + (if k < n then g (n - k) else 0)
        split_ifs <;> simp
      map_smul' := fun a f => by
        ext n
        change (if k < n then (a • f) (n - k) else 0) = a • (if k < n then f (n - k) else 0)
        split_ifs <;> simp }
    1 (fun f => by
      rw [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
      intro n
      change ‖if k < n then f (n - k) else 0‖ ≤ ‖f‖
      split_ifs
      · exact BoundedContinuousFunction.norm_coe_le_norm f _
      · simpa only [norm_zero] using (norm_nonneg f))

theorem natSequencePastShiftCLM_apply (k : ℕ) (f : ℕ →ᵇ E) (n : ℕ) :
    natSequencePastShiftCLM E k f n = if k < n then f (n - k) else 0 := rfl

theorem norm_natSequencePastShiftCLM_le (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    ‖natSequencePastShiftCLM E k‖ ≤ 1 := by
  apply (natSequencePastShiftCLM E k).opNorm_le_bound (by norm_num)
  intro f
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro n
  rw [natSequencePastShiftCLM_apply]
  split_ifs
  · exact BoundedContinuousFunction.norm_coe_le_norm f _
  · simpa only [norm_zero] using (norm_nonneg f)

def unstableSequenceGreenTermCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ a : ℝ) (k : ℕ) : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  ((-a⁻¹) * (ρ / a) ^ k) • natSequencePastShiftCLM E k

theorem norm_unstableSequenceGreenTermCLM_le {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) (k : ℕ) :
    ‖unstableSequenceGreenTermCLM E ρ a k‖ ≤ a⁻¹ * (ρ / a) ^ k := by
  have ha : 0 < a := hρ.trans hρa
  have hw : 0 ≤ (ρ / a) ^ k := pow_nonneg (div_nonneg hρ.le ha.le) _
  have hcoef : ‖(-a⁻¹) * (ρ / a) ^ k‖ = a⁻¹ * (ρ / a) ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (inv_nonneg.mpr ha.le), abs_of_nonneg hw]
  rw [unstableSequenceGreenTermCLM, norm_smul, hcoef]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_natSequencePastShiftCLM_le E k)
    (mul_nonneg (inv_nonneg.mpr ha.le) hw)

variable [CompleteSpace E]

theorem summable_unstableSequenceGreenTermCLM {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) : Summable (unstableSequenceGreenTermCLM E ρ a) := by
  have ha : 0 < a := hρ.trans hρa
  have hr : ‖ρ / a‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hρ ha)]
    exact (div_lt_one ha).mpr hρa
  exact ((summable_geometric_of_norm_lt_one hr).mul_left a⁻¹).of_norm_bounded
    (fun k => norm_unstableSequenceGreenTermCLM_le hρ hρa k)

def unstableSequenceGreenCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ρ a : ℝ) : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  ∑' k : ℕ, unstableSequenceGreenTermCLM E ρ a k

theorem norm_unstableSequenceGreenCLM_le {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) : ‖unstableSequenceGreenCLM E ρ a‖ ≤ (a - ρ)⁻¹ := by
  have ha : 0 < a := hρ.trans hρa
  have hr : ‖ρ / a‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hρ ha)]
    exact (div_lt_one ha).mpr hρa
  have hb := tsum_of_norm_bounded ((summable_geometric_of_norm_lt_one hr).mul_left a⁻¹).hasSum
    (fun k => norm_unstableSequenceGreenTermCLM_le (E := E) hρ hρa k)
  change ‖∑' k : ℕ, unstableSequenceGreenTermCLM E ρ a k‖ ≤ _
  calc
    _ ≤ ∑' k : ℕ, a⁻¹ * (ρ / a) ^ k := hb
    _ = a⁻¹ * (1 - ρ / a)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
    _ = (a - ρ)⁻¹ := by
      field_simp [ha.ne', (sub_pos.mpr hρa).ne', (sub_pos.mpr ((div_lt_one ha).mpr hρa)).ne'] <;> ring

end Euler2D

end
