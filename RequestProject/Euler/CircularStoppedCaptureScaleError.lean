module

public import RequestProject.Euler.CircularStoppedSharpPolynomialCapture
public import RequestProject.Euler.CircularCaptureOffGraphBlocks
public import RequestProject.Euler.CaptureComplementScaleDecay

/-! Scale error on every existing stopped capture interval. The
pointwise real forcing supplies both weighted budgets, while the
continuous exponential envelope is retained for joint continuation.
No portion of the actual path after the stopping time is used. -/

@[expose] public section

set_option maxHeartbeats 28000000
set_option maxRecDepth 7000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff BigOperators

namespace Euler2D

attribute [local instance 2000] captureBlockLittle_group captureBlockLittle_space
  captureBlockFamily_tower captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedUnstableProjectionCLM
  circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

theorem exists_circular_stopped_capture_scale_error_constants {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r εchart : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hεchart : 0 < εchart)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaX : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ q : ℝ, 1 < q ∧ q ^ 2 < circularCaptureBlockMultiplier ℓ ∧
      ∃ C > 0, ∃ d > 0, d ≤ r / 2 ∧ ∃ Ec > 0, ∃ F > 0, ∃ rn > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0, ∃ Eg > 0, ∃ Rg > 0,
      ∀ qbar : ℝ, 1 < qbar → qbar ^ 2 < circularCaptureBlockMultiplier ℓ → ∃ Fbar > 0,
      ∀ (y p : ℝ → Fin 2 → LittleContourSpace γ) (N : ℕ)
        {κ Damp D Bpoly ρ offset c W0 : ℝ},
        let T := circularCaptureBlockTime ℓ
        let lam := circularCaptureBlockMultiplier ℓ
        let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
        let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
        let v := fun n : ℕ => J (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
        let α := fun n => Q (v n)
        let w := fun n => (v n - α n) - (x (α n) 0 - α n)
        0 < N → D ∈ Icc (0 : ℝ) ((N : ℝ) * T) → q + 3 * C * Damp ≤ qbar →
        0 ≤ κ → κ ≤ κ₀ → 3 * Damp ≤ d → 0 ≤ Bpoly → 0 ≤ offset →
        0 ≤ ρ → 0 < c → 0 ≤ W0 → c * ρ ^ 6 ≤ ‖α 0‖ →
        0 < ‖α 0‖ → ‖α 0‖ * lam ^ N ≤ Damp →
        9 * C * Damp / (lam - 1) + 3 * (Ec * κ) * (N : ℝ) ≤ 1 / 16 →
        ‖w 0‖ ≤ ‖α 0‖ / 32 → ‖w 0‖ ≤ W0 * ρ ^ 6 →
        F * Bpoly * ρ ^ 6 * (1 + offset) ^ 4 ≤ ‖α 0‖ / 32 →
        Bpoly * ρ ^ 6 * (1 + offset + (N : ℝ) * T) ^ 4 + κ * (3 * Damp) ≤ ε₀ →
        (∀ t ∈ Icc (0 : ℝ) D, y t ∈ ball (littleCircularReference hγ hγ1) εchart →
          circularConstrainedChart hγ hγ1
            (J (y t - littleCircularReference hγ hγ1)) = y t) →
        (∀ t ∈ Icc (0 : ℝ) D, HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
        (∀ t ∈ Icc (0 : ℝ) D, ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ rn) →
        (∀ t ∈ Icc (0 : ℝ) D, ‖p t‖ ≤ κ * ‖y t - littleCircularMaterialContours hγ hγ1 t‖ +
          Bpoly * ρ ^ 6 * (1 + offset + t) ^ 4) →
        (∀ n ≤ N, (n : ℝ) * T ≤ D →
          (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
          ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
          ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n) ∧
        (∀ t ∈ Icc (0 : ℝ) D,
          ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ H * ‖α 0‖ * Real.exp (sigma * t)) ∧
        ∀ t ∈ Icc (0 : ℝ) D,
          let vc := J (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1)
          ‖vc - x (Q vc) 0‖ ≤ Eg *
            ((W0 + Fbar * Bpoly * (1 + offset) ^ 4) * (Damp / c + 1) * ρ ^ 3 +
              3 * (Ec * κ) * Damp / (lam - qbar) +
              Bpoly * ρ ^ 6 * (1 + offset + (N : ℝ) * T) ^ 4 + κ * Rg) := by
  obtain ⟨ℓ, hℓ, q, hq, hqgap, C, hC, dp, hdp, hdpr, Ec, hEc, F, hF,
    rp, hrp, κ₀, hκ₀, ε₀, hε₀, H, hH, hpolyCapture⟩ :=
    exists_circular_stopped_sharp_polynomial_capture hγ hγ1 hR hr hεchart hX hd hfix hareaX hg
  obtain ⟨dg, hdg, hdgr, rg, hrg, Eg, hEg, hblocks⟩ :=
    exists_circular_capture_offGraph_block_constants hγ hγ1 hR hr hℓ hX hd hfix hareaX hg
  let d := min dp dg
  let rn := min rp (min rg (εchart / 2))
  have hdpos : 0 < d := lt_min hdp hdg
  have hrn : 0 < rn := lt_min hrp (lt_min hrg (by positivity))
  refine ⟨ℓ, hℓ, q, hq, hqgap, C, hC, d, hdpos, (min_le_left _ _).trans hdpr,
    Ec, hEc, F, hF, rn, hrn, κ₀, hκ₀, ε₀, hε₀, H, hH, Eg, hEg, rg, hrg, ?_⟩
  intro qbar hqbar hgapbar
  obtain ⟨Fbar, hFbar, hcapture⟩ := hpolyCapture qbar hqbar hgapbar
  refine ⟨Fbar, hFbar, ?_⟩
  intro y p N κ Damp D Bpoly ρ offset c W0
  dsimp only
  let T := circularCaptureBlockTime ℓ
  let lam := circularCaptureBlockMultiplier ℓ
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let v := fun n : ℕ => J (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
  let α := fun n => Q (v n)
  let w := fun n => (v n - α n) - (x (α n) 0 - α n)
  have hwdef (n : ℕ) : w n = v n - x (α n) 0 := by
    dsimp only [w]
    exact sub_sub_sub_cancel_right _ _ _
  intro hN hD hcompbar hκ hκcap hDd hBpoly hoff hρ hc hW0 hseed ha hterminal hsmall
    hw0 hwScale hmargin hcap hchart hyd hnear hforce
  have hT : 0 < T := circularCaptureBlockTime_pos hℓ
  have hlam : 1 < lam := by nlinarith only [hq, hqgap, sq_nonneg (q - 1)]
  have hqbarLam : qbar < lam := by nlinarith only [hqbar, hgapbar, sq_nonneg (qbar - 1)]
  have hcapt := hcapture y p N hN hD hcompbar hκ hκcap (hDd.trans (min_le_left _ _))
    hBpoly hoff ha hterminal hsmall hw0 hmargin hcap hchart hyd
    (fun t ht => (hnear t ht).trans (min_le_left _ _)) hforce
  let A := W0 + Fbar * Bpoly * (1 + offset) ^ 4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hwscale (n : ℕ) (hn : n ≤ N) (hnt : (n : ℝ) * T ≤ D) :
      ‖w n‖ ≤ A * (Damp / c + 1) * ρ ^ 3 + 3 * (Ec * κ) * Damp / (lam - qbar) := by
    have hs : ‖w 0‖ + Fbar * Bpoly * ρ ^ 6 * (1 + offset) ^ 4 ≤ A * ρ ^ 6 := by
      dsimp only [A]
      nlinarith only [hwScale]
    have hh := (hcapt.2.2 n hn hnt).trans (add_le_add
      (mul_le_mul_of_nonneg_left hs (pow_nonneg (zero_lt_one.trans hqbar).le n)) le_rfl)
    have hterm : ‖α 0‖ * lam ^ n ≤ Damp :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam.le hn) (norm_nonneg _)).trans hterminal
    exact sharp_capture_error_le_cube hρ hc (zero_lt_one.trans hqbar).le hgapbar.le hqbarLam
      (mul_nonneg hEc.le hκ) hA hseed n hterm hh
  let B := fun n : ℕ => Bpoly * ρ ^ 6 * (1 + offset + ((n + 1 : ℕ) : ℝ) * T) ^ 4
  let Bmax := Bpoly * ρ ^ 6 * (1 + offset + (N : ℝ) * T) ^ 4
  have hpoly (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
      Bpoly * ρ ^ 6 * (1 + offset + t₁) ^ 4 ≤ Bpoly * ρ ^ 6 * (1 + offset + t₂) ^ 4 :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [hoff, ht₁]) (by linarith only [h12]) 4) (by positivity)
  have hB (n : ℕ) (hn : n < N) : 0 ≤ B n ∧ B n ≤ Bmax := by
    refine ⟨by dsimp only [B]; positivity, ?_⟩
    exact hpoly _ _ (mul_nonneg (Nat.cast_nonneg _) hT.le)
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.succ_le_of_lt hn)) hT.le)
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) T :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * ℓ)
  have hgridchart (n : ℕ) (_hn : n < N) (hnt : (n : ℝ) * T ≤ D) :
      circularConstrainedChart hγ hγ1 (v n) = y ((n : ℝ) * T) := by
    have ht : (n : ℝ) * T ∈ Icc (0 : ℝ) D := ⟨mul_nonneg (Nat.cast_nonneg n) hT.le, hnt⟩
    have href : littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T) = littleCircularReference hγ hγ1 :=
      (hperiod.nat_mul_eq n).trans (littleCircularMaterialContours_zero hγ hγ1)
    have hh := hnear _ ht
    rw [href] at hh
    have hrne : rn < εchart :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hεchart)
    exact hchart _ ht (by simpa only [mem_ball, dist_eq_norm] using hh.trans_lt hrne)
  have hsize (n : ℕ) (hn : n < N) (hnt : (n : ℝ) * T ≤ D) :
      ‖α n‖ + ‖v n - x (α n) 0‖ ≤ dg := by
    have hh : ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n := (hcapt.1 n hn.le hnt).2
    have hterm : ‖α 0‖ * lam ^ n ≤ Damp :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam.le hn.le) (norm_nonneg _)).trans hterminal
    have hscale : 0 ≤ ‖α 0‖ * lam ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (zero_lt_one.trans hlam).le n)
    have hlocal : ‖α n‖ + ‖w n‖ ≤ 3 * Damp := by nlinarith only [hh.1, hh.2, hterm, hscale]
    rw [hwdef] at hlocal
    exact hlocal.trans (hDd.trans (min_le_right _ _))
  have hforceBlock (n : ℕ) (hn : n < N) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T)
      (hvalid : (n : ℝ) * T + u ≤ D) :
      ‖p ((n : ℝ) * T + u)‖ ≤ B n + κ *
        ‖y ((n : ℝ) * T + u) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + u)‖ := by
    have ht0 : 0 ≤ (n : ℝ) * T + u := add_nonneg (mul_nonneg (Nat.cast_nonneg n) hT.le) hu.1
    have hclock : (n : ℝ) * T + u ≤ ((n + 1 : ℕ) : ℝ) * T := by push_cast; nlinarith only [hu.2]
    have hbnd := hpoly _ _ ht0 hclock
    have hh := hforce _ ⟨ht0, hvalid⟩
    change Bpoly * ρ ^ 6 * (1 + offset + ((n : ℝ) * T + u)) ^ 4 ≤ B n at hbnd
    linarith only [hh, hbnd]
  have hglobal := hblocks y p B N hN hD hκ (fun n hn => (hB n hn).1)
    hgridchart hsize hyd
    (fun t ht => (hnear t ht).trans ((min_le_right _ _).trans (min_le_left _ _))) hforceBlock
  refine ⟨hcapt.1, hcapt.2.1, ?_⟩
  intro t ht
  obtain ⟨n, hn, u, hu, htime, herr⟩ := hglobal t ht
  have hnt : (n : ℝ) * T ≤ D := by linarith only [htime, ht.2, hu.1]
  have hws : ‖v n - x (α n) 0‖ ≤ A * (Damp / c + 1) * ρ ^ 3 +
      3 * (Ec * κ) * Damp / (lam - qbar) := by
    have hh := hwscale n hn.le hnt
    rw [hwdef] at hh
    exact hh
  have hright := add_le_add (add_le_add hws (hB n hn).2) (le_refl (κ * rg))
  exact herr.trans (mul_le_mul_of_nonneg_left hright hEg.le)

end Euler2D

end
