module

public import RequestProject.Euler.BanachNonlinearBackwardOrbit
public import RequestProject.Euler.BanachInvariantKernel

/-! The stable space is the actual closed kernel of the bounded
unstable projection. Its power bound is inherited in the original norm. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_banachBackwardOrbit_of_kernel_bound
    (F : E → E) (hf : ContDiffAt ℝ 1 F 0) (hzero : F 0 = 0)
    (L : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    {ρ a β C : ℝ} (hρ : 1 < ρ) (hρa : ρ < a) (hβ0 : 0 ≤ β) (hβρ : β < ρ) (hC : 0 ≤ C)
    (P : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) (hLP : L.comp P = P.comp L)
    (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ C * β ^ k * ‖v‖)
    {ε rmax : ℝ} (hε : 0 < ε) (hrmax : 0 < rmax) :
    ∃ r > 0, r ≤ rmax ∧ ∀ ξ : E, P ξ = ξ → ‖ξ‖ ≤ r / 2 →
      ∃ x : ℕ → E,
        (∀ n, F (x (n + 1)) = x n) ∧
        (∀ n, x n ∈ closedBall 0 r) ∧
        (∀ n, ‖x n‖ ≤ 2 * (ρ⁻¹) ^ n * ‖ξ‖) ∧
        P (x 0) = ξ ∧ ‖x 0 - ξ‖ ≤ ε * ‖ξ‖ ∧
        Tendsto x atTop (𝓝 (0 : E)) := by
  letI : CompleteSpace P.ker := P.isClosed_ker.completeSpace_coe
  let A := invariantKernelCLM L P hLP
  let J : P.ker →L[ℝ] E := P.ker.subtypeL
  let Q := projectionComplementToKernelCLM P hP
  have hA (k : ℕ) : ‖A ^ k‖ ≤ C * β ^ k :=
    norm_invariantKernelCLM_pow_le L P hLP hC hβ0 hbound k
  have hLJ (v : P.ker) : L (J v) = J (A v) := rfl
  have hJQ (v : E) : J (Q v) = v - P v := rfl
  have hPJ (v : P.ker) : P (J v) = 0 := v.property
  exact exists_banachBackwardOrbit_of_splitting F hf hzero L hderiv hρ hρa hβ0 hβρ
    A hA J Q P heigen hLJ hJQ hPJ hε hrmax

end Euler2D

end
