module

public import RequestProject.Euler.BanachFullOrbitAsymptotic

/-! The full quadratic ancient asymptotic on the actual closed
kernel of the original bounded unstable projection, retaining its
original inherited norm and true operator power bound. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_kernel_quadratic_backward_asymptotic
    {F : E → E} (L P : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    (hP : ∀ v, P (P v) = P v) (hLP : L.comp P = P.comp L)
    {a b κ C M β : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hβ : 0 ≤ β) (hab : a * b ^ 2 < 1)
    (hβb : β * b < 1) (hβb2 : β * b ^ 2 < 1)
    (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ M * β ^ k * ‖v‖)
    (x : ℕ → E) (hrec : ∀ n, F (x (n + 1)) = x n)
    (hnorm : ∀ n, ‖x n‖ ≤ C * b ^ n)
    (hquad : ∀ n, ‖banachLocalRemainder F (x n)‖ ≤ κ * ‖x n‖ ^ 2) :
    let Q := projectionComplementToKernelCLM P hP
    ∃ c : E, P c = c ∧ Tendsto (fun n : ℕ => a ^ n • P (x n)) atTop (𝓝 c) ∧
      ‖c - P (x 0)‖ ≤ (‖P‖ * κ * C ^ 2 * b ^ 2) / (1 - a * b ^ 2) ∧
      ∀ n : ℕ, ‖x n - (a⁻¹) ^ n • c‖ ≤
        ((‖P‖ * κ * C ^ 2 * b ^ 2) / (1 - a * b ^ 2) +
          (M * ‖Q‖ * κ * C ^ 2 * b ^ 2) / (1 - β * b ^ 2)) * (b ^ 2) ^ n := by
  letI : CompleteSpace P.ker := P.isClosed_ker.completeSpace_coe
  let A := invariantKernelCLM L P hLP
  let J : P.ker →L[ℝ] E := P.ker.subtypeL
  let Q := projectionComplementToKernelCLM P hP
  have hA (k : ℕ) : ‖A ^ k‖ ≤ M * β ^ k :=
    norm_invariantKernelCLM_pow_le L P hLP hM hβ hbound k
  have hJ (v : P.ker) : ‖J v‖ ≤ ‖v‖ := le_rfl
  have hJQ (v : E) : J (Q v) = v - P v := rfl
  have hQL (v : E) : Q (L v) = A (Q v) :=
    projectionComplementToKernelCLM_intertwines L P hP hLP v
  have hPL (v : E) : P (L v) = a • P v := by
    have he : L (P v) = P (L v) := congrArg (fun D : E →L[ℝ] E => D v) hLP
    exact he.symm.trans (heigen v)
  exact exists_full_quadratic_backward_asymptotic L P hderiv hP ha hb hκ hC hM hβ hab
    hβb hβb2 hPL A hA J Q hJ hJQ hQL x hrec hnorm hquad

end Euler2D

end
