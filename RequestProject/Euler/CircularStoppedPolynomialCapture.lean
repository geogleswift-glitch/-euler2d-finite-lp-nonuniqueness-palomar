module

public import RequestProject.Euler.CircularStoppedCaptureEnvelope
public import RequestProject.Euler.CapturePolynomialBlockBudget

/-! Actual pointwise polynomial forcing supplies the stopped capture
argument. The discrete source budget and endpoint chart recovery are
derived, rather than supplied as separate trajectory assumptions. -/

@[expose] public section

set_option maxHeartbeats 22000000
set_option maxRecDepth 6500

noncomputable section

open Set Metric
open scoped NNReal ContDiff BigOperators

namespace Euler2D

attribute [local instance 2000] captureBlockLittle_group captureBlockLittle_space
  captureBlockFamily_tower captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

theorem exists_circular_stopped_polynomial_capture {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r₀ εchart : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hεchart : 0 < εchart)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ x) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : ℝ, 1 < q ∧ q ^ 2 < circularCaptureBlockMultiplier k ∧
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let g := fun v => x v 0 - v
      let T := circularCaptureBlockTime k
      let lam := circularCaptureBlockMultiplier k
      ∃ C > 0, ∃ d > 0, d ≤ r₀ / 2 ∧ ∃ E > 0, ∃ F > 0, ∃ r > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0,
        ∀ (y p : ℝ → Fin 2 → LittleContourSpace γ) (N : ℕ) {κ Damp D Bpoly ρ offset : ℝ},
        let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
          (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
        let α := fun n => P (v n)
        let w := fun n => (v n - α n) - g (α n)
        0 < N → D ∈ Icc (0 : ℝ) ((N : ℝ) * T) →
        0 ≤ κ → κ ≤ κ₀ → 3 * Damp ≤ d → 0 ≤ Bpoly → 0 ≤ offset →
        0 < ‖α 0‖ → ‖α 0‖ * lam ^ N ≤ Damp → q + 3 * C * Damp ≤ lam →
        9 * C * Damp / (lam - 1) + 3 * (E * κ) * (N : ℝ) ≤ 1 / 16 →
        ‖w 0‖ ≤ ‖α 0‖ / 32 → F * Bpoly * ρ ^ 6 * (1 + offset) ^ 4 ≤ ‖α 0‖ / 32 →
        Bpoly * ρ ^ 6 * (1 + offset + (N : ℝ) * T) ^ 4 + κ * (3 * Damp) ≤ ε₀ →
        (∀ t ∈ Icc (0 : ℝ) D,
          y t ∈ ball (littleCircularReference hγ hγ1) εchart →
            circularConstrainedChart hγ hγ1
              (circularConstraintProjectionToTangentCLM hγ hγ1.le (y t - littleCircularReference hγ hγ1)) = y t) →
        (∀ t ∈ Icc (0 : ℝ) D, HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
        (∀ t ∈ Icc (0 : ℝ) D, ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ r) →
        (∀ t ∈ Icc (0 : ℝ) D, ‖p t‖ ≤
          κ * ‖y t - littleCircularMaterialContours hγ hγ1 t‖ + Bpoly * ρ ^ 6 * (1 + offset + t) ^ 4) →
        (∀ n ≤ N, (n : ℝ) * T ≤ D →
          (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
          ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
          ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n) ∧
        ∀ t ∈ Icc (0 : ℝ) D,
          ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ H * ‖α 0‖ * Real.exp (sigma * t) := by
  obtain ⟨k, hk, q, hq, hgap, C, hC, d, hdpos, hdr, E, hE, rs, hrs, κ₀, hκ₀, ε₀, hε₀, H, hH, hstopped⟩ :=
    exists_circular_stopped_capture_envelope hγ hγ1 hR hr₀ hX hd hfix harea hg
  let T := circularCaptureBlockTime k
  let lam := circularCaptureBlockMultiplier k
  have hT : 0 < T := circularCaptureBlockTime_pos hk
  have hlam : 1 < lam := by
    rw [show lam = Real.exp (sigma * T) from circularCaptureBlockMultiplier_eq_exp k]
    exact Real.one_lt_exp_iff.mpr (mul_pos sigma_pos hT)
  obtain ⟨Fb, hFb, hsum⟩ := exists_capture_polynomial_block_budget hlam hT.le
  let F := Fb * E
  let r := min rs (εchart / 2)
  have hF : 0 < F := mul_pos hFb hE
  have hr : 0 < r := lt_min hrs (by positivity)
  refine ⟨k, hk, q, hq, hgap, C, hC, d, hdpos, hdr, E, hE, F, hF, r, hr, κ₀, hκ₀, ε₀, hε₀, H, hH, ?_⟩
  intro y p N κ Damp D Bpoly ρ offset
  dsimp only
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let g := fun v => x v 0 - v
  let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
    (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
  let α := fun n => P (v n)
  let w := fun n => (v n - α n) - g (α n)
  intro hN hD hκ hκcap hDd hBpoly hoff ha hterminal hcomp hsmall hw0 hweighted hcap hchart hyd hnear hp
  let B : ℕ → ℝ := fun n => Bpoly * ρ ^ 6 * (1 + offset + ((n + 1 : ℕ) : ℝ) * T) ^ 4
  have hB0 (n : ℕ) : 0 ≤ B n := by dsimp only [B]; positivity
  have hpoly (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
      Bpoly * ρ ^ 6 * (1 + offset + t₁) ^ 4 ≤ Bpoly * ρ ^ 6 * (1 + offset + t₂) ^ 4 :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [hoff, ht₁]) (by linarith only [h12]) 4) (by positivity)
  have hf (n : ℕ) (_hn : n ≤ N) :
      ∑ j ∈ Finset.range n, (E * B j) / lam ^ (j + 1) ≤ ‖α 0‖ / 32 := by
    have hh := hsum (S := offset) (B := E * Bpoly) (ρ := ρ) hoff (mul_nonneg hE.le hBpoly) n
    have heq : (∑ j ∈ Finset.range n, (E * B j) / lam ^ (j + 1)) =
        ∑ j ∈ Finset.range n, ((E * Bpoly) * ρ ^ 6 * (1 + offset + ((j + 1 : ℕ) : ℝ) * T) ^ 4) /
          lam ^ (j + 1) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [B]
      ring
    rw [heq]
    apply hh.trans
    simpa only [F, mul_assoc] using hweighted
  have hBcap (n : ℕ) (hn : n < N) : 0 ≤ B n ∧ B n + κ * (3 * Damp) ≤ ε₀ := by
    have hclock : ((n + 1 : ℕ) : ℝ) * T ≤ (N : ℝ) * T :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.succ_le_of_lt hn)) hT.le
    have hh := hpoly (((n + 1 : ℕ) : ℝ) * T) ((N : ℝ) * T)
      (mul_nonneg (Nat.cast_nonneg _) hT.le) hclock
    exact ⟨hB0 n, (add_le_add hh le_rfl).trans hcap⟩
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) T :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * k)
  have hcgrid (n : ℕ) : littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T) = littleCircularReference hγ hγ1 :=
    (hperiod.nat_mul_eq n).trans (littleCircularMaterialContours_zero hγ hγ1)
  have hgridchart (n : ℕ) (_hn : n ≤ N) (hnt : (n : ℝ) * T ≤ D) :
      circularConstrainedChart hγ hγ1 (v n) = y ((n : ℝ) * T) := by
    have ht : (n : ℝ) * T ∈ Icc (0 : ℝ) D := ⟨mul_nonneg (Nat.cast_nonneg _) hT.le, hnt⟩
    have hh := hnear _ ht
    change ‖y ((n : ℝ) * T) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T)‖ ≤ r at hh
    rw [hcgrid] at hh
    have hsmall' : ‖y ((n : ℝ) * T) - littleCircularReference hγ hγ1‖ < εchart :=
      hh.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hεchart))
    exact hchart _ ht (by simpa only [mem_ball, dist_eq_norm] using hsmall')
  have hblockforcing (n : ℕ) (hn : n < N) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T)
      (hvalid : (n : ℝ) * T + u ≤ D) :
      ‖p ((n : ℝ) * T + u)‖ ≤ B n + κ *
        ‖y ((n : ℝ) * T + u) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + u)‖ := by
    have ht0 : 0 ≤ (n : ℝ) * T + u := add_nonneg (mul_nonneg (Nat.cast_nonneg _) hT.le) hu.1
    have hclock : (n : ℝ) * T + u ≤ ((n + 1 : ℕ) : ℝ) * T := by push_cast; nlinarith only [hu.2]
    have hbnd := hpoly ((n : ℝ) * T + u) (((n + 1 : ℕ) : ℝ) * T) ht0 hclock
    have hh := hp _ ⟨ht0, hvalid⟩
    change Bpoly * ρ ^ 6 * (1 + offset + ((n : ℝ) * T + u)) ^ 4 ≤ B n at hbnd
    linarith only [hh, hbnd]
  exact hstopped y p N B (κ := κ) (Damp := Damp) (D := D) hN hD hκ hκcap hDd
    ha hterminal hcomp hsmall hw0 hf hBcap hgridchart hyd
    (fun t ht => (hnear t ht).trans (min_le_left _ _)) hblockforcing

end Euler2D

end
