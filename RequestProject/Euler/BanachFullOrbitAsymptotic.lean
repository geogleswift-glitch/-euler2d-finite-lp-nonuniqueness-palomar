module

public import RequestProject.Euler.BanachUnstableAsymptotic
public import RequestProject.Euler.BanachStableFutureFormula
public import RequestProject.Euler.BanachInvariantKernel

/-! A full Banach-space asymptotic expansion of a genuine nonlinear
backward orbit. Both the expanding coefficient and the stable remainder
are derived from the actual equation and quadratic remainder estimate. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology

namespace Euler2D

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

theorem projectionComplementToKernelCLM_intertwines (L P : E →L[ℝ] E)
    (hP : ∀ v, P (P v) = P v) (hLP : L.comp P = P.comp L) (v : E) :
    projectionComplementToKernelCLM P hP (L v) =
      invariantKernelCLM L P hLP (projectionComplementToKernelCLM P hP v) := by
  apply Subtype.ext
  change L v - P (L v) = L (v - P v)
  rw [L.map_sub]
  have he : L (P v) = P (L v) := congrArg (fun A : E →L[ℝ] E => A v) hLP
  rw [he]

theorem exists_full_quadratic_backward_asymptotic
    {F : E → E} (L P : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    (hP : ∀ v, P (P v) = P v)
    {a b κ C M β : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hβ : 0 ≤ β) (hab : a * b ^ 2 < 1)
    (hβb : β * b < 1) (hβb2 : β * b ^ 2 < 1)
    (hPL : ∀ v, P (L v) = a • P v)
    (A : K →L[ℝ] K) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ M * β ^ k)
    (J : K →L[ℝ] E) (Q : E →L[ℝ] K)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) (hJQ : ∀ v, J (Q v) = v - P v)
    (hQL : ∀ v, Q (L v) = A (Q v))
    (x : ℕ → E) (hrec : ∀ n, F (x (n + 1)) = x n)
    (hnorm : ∀ n, ‖x n‖ ≤ C * b ^ n)
    (hquad : ∀ n, ‖banachLocalRemainder F (x n)‖ ≤ κ * ‖x n‖ ^ 2) :
    ∃ c : E, P c = c ∧ Tendsto (fun n : ℕ => a ^ n • P (x n)) atTop (𝓝 c) ∧
      ‖c - P (x 0)‖ ≤ (‖P‖ * κ * C ^ 2 * b ^ 2) / (1 - a * b ^ 2) ∧
      ∀ n : ℕ, ‖x n - (a⁻¹) ^ n • c‖ ≤
        ((‖P‖ * κ * C ^ 2 * b ^ 2) / (1 - a * b ^ 2) +
          (M * ‖Q‖ * κ * C ^ 2 * b ^ 2) / (1 - β * b ^ 2)) * (b ^ 2) ^ n := by
  obtain ⟨c, hlim, herr, hc0⟩ := exists_unstableCoefficient_of_quadratic_backward_orbit
    L P hderiv ha hb hκ hC hab hPL x hrec hnorm (fun n => hquad (n + 1))
  have hlimP := (P.continuous.tendsto c).comp hlim
  have hseq : (fun n : ℕ => P (a ^ n • P (x n))) = (fun n : ℕ => a ^ n • P (x n)) := by
    funext n
    rw [P.map_smul, hP]
  change Tendsto (fun n : ℕ => P (a ^ n • P (x n))) atTop (𝓝 (P c)) at hlimP
  rw [hseq] at hlimP
  have hc : P c = c := tendsto_nhds_unique hlimP hlim
  let u : ℕ → K := fun n => Q (x n)
  let y : ℕ → K := fun n => Q (banachLocalRemainder F (x n))
  have hu (n : ℕ) : ‖u n‖ ≤ (‖Q‖ * C) * b ^ n := by
    calc
      _ ≤ ‖Q‖ * ‖x n‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (C * b ^ n) := mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg Q)
      _ = _ := by ring
  have hy (n : ℕ) : ‖y n‖ ≤ (‖Q‖ * κ * C ^ 2) * (b ^ 2) ^ n := by
    have hs : ‖x n‖ ^ 2 ≤ (C * b ^ n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2
    have hp : (b ^ n) ^ 2 = (b ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
    calc
      _ ≤ ‖Q‖ * ‖banachLocalRemainder F (x n)‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (κ * ‖x n‖ ^ 2) := mul_le_mul_of_nonneg_left (hquad n) (norm_nonneg Q)
      _ ≤ ‖Q‖ * (κ * (C * b ^ n) ^ 2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs hκ) (norm_nonneg Q)
      _ = _ := by rw [mul_pow, hp]; ring
  have hpoint (n : ℕ) : x n = L (x (n + 1)) + banachLocalRemainder F (x (n + 1)) := by
    rw [← hrec n, banachLocalRemainder, hderiv]
    abel
  have hurec (n : ℕ) : u n = A (u (n + 1)) + y (n + 1) := by
    change Q (x n) = _
    rw [hpoint n, Q.map_add, hQL]
  let U : ℝ := (‖P‖ * κ * C ^ 2 * b ^ 2) / (1 - a * b ^ 2)
  let V : ℝ := (M * ‖Q‖ * κ * C ^ 2 * b ^ 2) / (1 - β * b ^ 2)
  have hstable (n : ℕ) : ‖J (Q (x n))‖ ≤ V * (b ^ 2) ^ n := by
    have he := (backwardRecurrence_future_formula A hM hβ hb (sq_nonneg b) hβb hβb2
      hA u y hu hy hurec n).2
    calc
      _ ≤ ‖Q (x n)‖ := hJ _
      _ ≤ (M * (‖Q‖ * κ * C ^ 2) * (b ^ 2) ^ (n + 1)) / (1 - β * b ^ 2) := he
      _ = _ := by dsimp only [V]; rw [pow_succ]; ring
  have hunstable (n : ℕ) : ‖P (x n) - (a⁻¹) ^ n • c‖ ≤ U * (b ^ 2) ^ n := by
    have he : P (x n) - (a⁻¹) ^ n • c = (a⁻¹) ^ n • (a ^ n • P (x n) - c) := by
      rw [smul_sub, smul_smul, ← mul_pow, inv_mul_cancel₀ ha.ne', one_pow, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr ha.le) n)]
    calc
      _ ≤ (a⁻¹) ^ n * (U * (a * b ^ 2) ^ n) := mul_le_mul_of_nonneg_left (herr n)
        (pow_nonneg (inv_nonneg.mpr ha.le) n)
      _ = U * ((a⁻¹) ^ n * (a * b ^ 2) ^ n) := by ring
      _ = _ := by rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  refine ⟨c, hc, hlim, hc0, ?_⟩
  intro n
  have he : x n - (a⁻¹) ^ n • c = (P (x n) - (a⁻¹) ^ n • c) + J (Q (x n)) := by
    rw [hJQ]
    abel
  rw [he]
  calc
    _ ≤ ‖P (x n) - (a⁻¹) ^ n • c‖ + ‖J (Q (x n))‖ := norm_add_le _ _
    _ ≤ U * (b ^ 2) ^ n + V * (b ^ 2) ^ n := add_le_add (hunstable n) (hstable n)
    _ = _ := by dsimp only [U, V]; ring

end Euler2D

end
