module

public import Mathlib

/-! Actual restrictions of commuting Banach operators to a closed
kernel, and true complement projections into that kernel. These retain
the original power bounds in the inherited norm. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def invariantKernelCLM (L P : E →L[ℝ] E) (hLP : L.comp P = P.comp L) : P.ker →L[ℝ] P.ker :=
  (L.comp P.ker.subtypeL).codRestrict P.ker (fun v => by
    have he := congrArg (fun A : E →L[ℝ] E => A v.val) hLP
    change L (P v.val) = P (L v.val) at he
    have hz : P v.val = 0 := v.property
    rw [hz, map_zero] at he
    exact he.symm)

theorem invariantKernelCLM_val (L P : E →L[ℝ] E) (hLP : L.comp P = P.comp L) (v : P.ker) :
    (invariantKernelCLM L P hLP v).val = L v.val := rfl

theorem invariantKernelCLM_pow_val (L P : E →L[ℝ] E) (hLP : L.comp P = P.comp L)
    (k : ℕ) (v : P.ker) :
    (((invariantKernelCLM L P hLP) ^ k) v).val = (L ^ k) v.val := by
  let A := invariantKernelCLM L P hLP
  change ((A ^ k) v).val = (L ^ k) v.val
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      _ = (A ((A ^ k) v)).val := by rw [pow_succ', ContinuousLinearMap.mul_apply]
      _ = L ((A ^ k) v).val := invariantKernelCLM_val L P hLP _
      _ = L ((L ^ k) v.val) := congrArg L ih
      _ = _ := by rw [pow_succ', ContinuousLinearMap.mul_apply]

theorem norm_invariantKernelCLM_pow_le (L P : E →L[ℝ] E) (hLP : L.comp P = P.comp L)
    {M β : ℝ} (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ M * β ^ k * ‖v‖)
    (k : ℕ) : ‖(invariantKernelCLM L P hLP) ^ k‖ ≤ M * β ^ k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (pow_nonneg hβ k))
  intro v
  change ‖(((invariantKernelCLM L P hLP) ^ k) v).val‖ ≤ M * β ^ k * ‖v.val‖
  rw [invariantKernelCLM_pow_val]
  exact hbound k v.val v.property

def projectionComplementToKernelCLM (P : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) : E →L[ℝ] P.ker :=
  (ContinuousLinearMap.id ℝ E - P).codRestrict P.ker (fun v => by
    change P (v - P v) = 0
    rw [map_sub, hP, sub_self])

theorem projectionComplementToKernelCLM_val (P : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) (v : E) :
    (projectionComplementToKernelCLM P hP v).val = v - P v := rfl

theorem projectionComplementToKernelCLM_of_mem (P : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v)
    (v : P.ker) : projectionComplementToKernelCLM P hP v.val = v := by
  apply Subtype.ext
  change v.val - P v.val = v.val
  have hz : P v.val = 0 := v.property
  rw [hz, sub_zero]

theorem norm_projectionComplementToKernelCLM_le (P : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) :
    ‖projectionComplementToKernelCLM P hP‖ ≤ 1 + ‖P‖ := by
  apply (projectionComplementToKernelCLM P hP).opNorm_le_bound (by positivity)
  intro v
  change ‖(projectionComplementToKernelCLM P hP v).val‖ ≤ _
  rw [projectionComplementToKernelCLM_val]
  calc
    _ ≤ ‖v‖ + ‖P v‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + ‖P‖ * ‖v‖ := add_le_add le_rfl (P.le_opNorm v)
    _ = _ := by ring

end Euler2D

end
