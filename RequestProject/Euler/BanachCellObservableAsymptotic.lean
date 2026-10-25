module

public import RequestProject.Euler.BanachCompactQuadraticTaylor

/-! A true quadratic expansion about a compact reference curve
transfers a uniform full-space cell asymptotic to every C² observable.
Only an eventual smallness condition is needed, and it is proved
from the actual geometric decay. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff NNReal

namespace Euler2D

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem exists_uniform_cell_observable_asymptotic
    {φ : E → H} (hφ : ContDiff ℝ 2 φ) {T : ℝ}
    {c v : ℝ → E} (hc : Continuous c) (y : ℕ → ℝ → E)
    {q b B M : ℝ} (hq : 0 ≤ q) (hqb : q ≤ b) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hv : ∀ s ∈ Icc (0 : ℝ) T, ‖v s‖ ≤ M)
    (he : ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) T,
      ‖y n s - c s - q ^ n • v s‖ ≤ B * (b ^ 2) ^ n) :
    ∃ N : ℕ, ∃ K > 0, ∀ n ≥ N, ∀ s ∈ Icc (0 : ℝ) T,
      ‖φ (y n s) - φ (c s) - q ^ n • fderiv ℝ φ (c s) (v s)‖ ≤ K * (b ^ 2) ^ n := by
  let C := B + M
  have hC : 0 ≤ C := add_nonneg hB hM
  have hb2 : b ^ 2 ≤ b := by nlinarith
  have hnorm (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : ‖y n s - c s‖ ≤ C * b ^ n := by
    calc
      _ ≤ ‖y n s - c s - q ^ n • v s‖ + ‖q ^ n • v s‖ := norm_le_norm_sub_add _ _
      _ ≤ B * (b ^ 2) ^ n + q ^ n * M := add_le_add (he n s hs) (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq n)]
        exact mul_le_mul_of_nonneg_left (hv s hs) (pow_nonneg hq n))
      _ ≤ B * b ^ n + b ^ n * M := add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg b) hb2 n) hB)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq hqb n) hM)
      _ = _ := by dsimp only [C]; ring
  obtain ⟨κ, r, hr, hTaylor⟩ := exists_uniform_quadratic_taylor_on_compact
    isOpen_univ hφ.contDiffOn (isCompact_Icc.image hc) (subset_univ _)
  have hlim : Tendsto (fun n : ℕ => C * b ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1).const_mul C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hr))
  have hDc := (hφ.continuous_fderiv (by norm_num)).comp hc
  obtain ⟨D, hD⟩ := (isCompact_Icc.image hDc).isBounded.exists_norm_le
  let K := (κ : ℝ) * C ^ 2 + max D 0 * B + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨N, K, hK, ?_⟩
  intro n hn s hs
  let d := y n s - c s
  let L := fderiv ℝ φ (c s)
  have hd : ‖d‖ ≤ C * b ^ n := hnorm n s hs
  have hsmall : ‖d‖ ≤ r := hd.trans (hN n hn).le
  have hquad := (hTaylor (c s) (mem_image_of_mem _ hs) d hsmall).2
  rw [show c s + d = y n s by dsimp only [d]; abel] at hquad
  have hid : φ (y n s) - φ (c s) - q ^ n • L (v s) =
      (φ (y n s) - φ (c s) - L d) + L (d - q ^ n • v s) := by
    rw [L.map_sub d (q ^ n • v s), L.map_smul]
    abel
  have hp : (b ^ n) ^ 2 = (b ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  have hsquare : ‖d‖ ^ 2 ≤ C ^ 2 * (b ^ 2) ^ n := by
    convert pow_le_pow_left₀ (norm_nonneg d) hd 2 using 1
    rw [mul_pow, hp]
  have hL : ‖L‖ ≤ max D 0 := (hD _ (mem_image_of_mem _ hs)).trans (le_max_left D 0)
  rw [hid]
  calc
    _ ≤ ‖φ (y n s) - φ (c s) - L d‖ + ‖L (d - q ^ n • v s)‖ := norm_add_le _ _
    _ ≤ (κ : ℝ) * ‖d‖ ^ 2 + ‖L‖ * ‖d - q ^ n • v s‖ :=
      add_le_add hquad (L.le_opNorm _)
    _ ≤ (κ : ℝ) * (C ^ 2 * (b ^ 2) ^ n) + max D 0 * (B * (b ^ 2) ^ n) := add_le_add
      (mul_le_mul_of_nonneg_left hsquare κ.coe_nonneg)
      (mul_le_mul hL (he n s hs) (norm_nonneg _) (le_max_right D 0))
    _ ≤ K * (b ^ 2) ^ n := by
      dsimp only [K]
      nlinarith [pow_nonneg (sq_nonneg b) n]

end Euler2D

end
