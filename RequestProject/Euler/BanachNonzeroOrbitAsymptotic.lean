module

public import RequestProject.Euler.BanachKernelOrbitAsymptotic
public import RequestProject.Euler.BanachQuadraticRemainder
public import RequestProject.Euler.BanachBackwardOrbitDeparture

/-! A sufficiently small genuine nonlinear backward orbit has a
nonzero leading expanding coefficient, a quantitative full-space
asymptotic, and a true observable departure at its endpoint. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem exists_backwardOrbit_nonzero_asymptotic
    {F : E → E} (hf : ContDiffAt ℝ 2 F 0) (hzero : F 0 = 0)
    (L P : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    (hP : ∀ v, P (P v) = P v) (hLP : L.comp P = P.comp L)
    {w a M β : ℝ} (hw : 1 < w) (ha : 0 < a) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hab : a * (w⁻¹) ^ 2 < 1) (hβb : β * w⁻¹ < 1) (hβb2 : β * (w⁻¹) ^ 2 < 1)
    (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ M * β ^ k * ‖v‖)
    (horbit : HasFlatBackwardOrbits F P w)
    {φ : E → H} {Dφ : E →L[ℝ] H} (hφ : HasFDerivAt φ Dφ 0)
    (g : E) (hPg : P g = g) (hg : Dφ g ≠ 0) {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ t : ℝ, 0 < t ∧ ∃ x : ℕ → E, ∃ c : E, ∃ B > 0,
      (∀ n, F (x (n + 1)) = x n) ∧
      (∀ n, x n ∈ closedBall 0 rmax) ∧
      (∀ n, ‖x n‖ ≤ 2 * (w⁻¹) ^ n * ‖t • g‖) ∧
      P (x 0) = t • g ∧ P c = c ∧ c ≠ 0 ∧
      (∀ n : ℕ, ‖x n - (a⁻¹) ^ n • c‖ ≤ B * ((w⁻¹) ^ 2) ^ n) ∧
      φ (x 0) ≠ φ 0 ∧ Tendsto x atTop (𝓝 0) := by
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hb : 0 ≤ w⁻¹ := inv_nonneg.mpr hw0.le
  obtain ⟨κ, hκ, rq, hrq, hquad⟩ := exists_banachLocalRemainder_quadratic_bound hf hzero
  let C₀ : ℝ := (4 * ‖P‖ * κ * (w⁻¹) ^ 2) / (1 - a * (w⁻¹) ^ 2)
  have hC₀ : 0 ≤ C₀ := div_nonneg (by positivity) (sub_pos.mpr hab).le
  let den : ℝ := 2 * (C₀ + 1) * (‖P‖ + 1)
  have hden : 0 < den := by dsimp only [den]; positivity
  let radius := min rq (min rmax (1 / den))
  have hradius : 0 < radius := lt_min hrq (lt_min hrmax (div_pos zero_lt_one hden))
  have hrq' : radius ≤ rq := min_le_left _ _
  have hrmax' : radius ≤ rmax := (min_le_right _ _).trans (min_le_left _ _)
  have hrden : radius * den ≤ 1 := (le_div_iff₀ hden).mp
    ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨t, ht, x, hrec, hball, hnorm, hproj, hdep, hdepne, hlim⟩ :=
    exists_backwardOrbit_with_observable_departure horbit hφ g hPg hg hradius
  let ξ := t • g
  have hξ : ξ ≠ 0 := by
    have hg0 : g ≠ 0 := by intro hz; apply hg; rw [hz, map_zero]
    exact smul_ne_zero ht.ne' hg0
  have hx0 : ‖x 0‖ ≤ radius := by
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hball 0
  have hξnorm : ‖ξ‖ ≤ ‖P‖ * radius := by
    calc
      _ = ‖P (x 0)‖ := congrArg norm hproj.symm
      _ ≤ ‖P‖ * ‖x 0‖ := P.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left hx0 (norm_nonneg P)
  have hsmall : C₀ * ‖ξ‖ < 1 := by
    have he : C₀ * (‖P‖ * radius) < 1 := by
      dsimp only [den] at hrden
      have h1 := mul_nonneg hradius.le hC₀
      have h2 := mul_nonneg hradius.le (norm_nonneg P)
      nlinarith
    exact (mul_le_mul_of_nonneg_left hξnorm hC₀).trans_lt he
  have hxn (n : ℕ) : ‖x n‖ ≤ (2 * ‖ξ‖) * (w⁻¹) ^ n := by
    calc
      _ ≤ 2 * (w⁻¹) ^ n * ‖ξ‖ := hnorm n
      _ = _ := by ring
  have hxq (n : ℕ) : ‖banachLocalRemainder F (x n)‖ ≤ κ * ‖x n‖ ^ 2 :=
    hquad _ (closedBall_subset_closedBall hrq' (hball n))
  obtain ⟨c, hcP, hclim, hc0, herr⟩ := exists_kernel_quadratic_backward_asymptotic
    L P hderiv hP hLP ha hb hκ.le (by positivity : 0 ≤ 2 * ‖ξ‖) hM hβ hab hβb hβb2
    heigen hbound x hrec hxn hxq
  have hclose : ‖c - ξ‖ ≤ C₀ * ‖ξ‖ ^ 2 := by
    calc
      _ = ‖c - P (x 0)‖ := by rw [hproj]
      _ ≤ (‖P‖ * κ * (2 * ‖ξ‖) ^ 2 * (w⁻¹) ^ 2) / (1 - a * (w⁻¹) ^ 2) := hc0
      _ = _ := by dsimp only [C₀]; ring
  have hcne : c ≠ 0 := ne_zero_of_quadratic_distance hξ hsmall hclose
  let Q := projectionComplementToKernelCLM P hP
  let Aerr : ℝ := (‖P‖ * κ * (2 * ‖ξ‖) ^ 2 * (w⁻¹) ^ 2) / (1 - a * (w⁻¹) ^ 2) +
    (M * ‖Q‖ * κ * (2 * ‖ξ‖) ^ 2 * (w⁻¹) ^ 2) / (1 - β * (w⁻¹) ^ 2)
  let B := |Aerr| + 1
  have hB : 0 < B := by dsimp only [B]; linarith [abs_nonneg Aerr]
  refine ⟨t, ht, x, c, B, hB, hrec,
    fun n => closedBall_subset_closedBall hrmax' (hball n), hnorm, hproj, hcP, hcne, ?_, hdepne, hlim⟩
  intro n
  calc
    _ ≤ Aerr * ((w⁻¹) ^ 2) ^ n := herr n
    _ ≤ B * ((w⁻¹) ^ 2) ^ n := mul_le_mul_of_nonneg_right
      (by dsimp only [B]; linarith [le_abs_self Aerr]) (pow_nonneg (sq_nonneg _) n)

end Euler2D

end
