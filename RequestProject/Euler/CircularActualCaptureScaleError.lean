module

public import RequestProject.Euler.CircularExistingSharpFiniteCapture
public import RequestProject.Euler.CircularCaptureOffGraphBlocks
public import RequestProject.Euler.CaptureComplementScaleDecay

/-! A scale-decaying off-graph error at every real time of an actual
finite capture. The discrete bounds come from the original contour
equation; intermediate times use the true same-graph flow. All chart
and comparison constants precede the scale and finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 6500

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

theorem exists_circular_actual_capture_scale_error_constants {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
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
      ∃ C > 0, ∃ d > 0, d ≤ r / 2 ∧ ∃ Ec > 0, ∃ rn > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0, ∃ Eg > 0, ∃ Rg > 0,
      ∀ (y p : ℝ → Fin 2 → LittleContourSpace γ) (B : ℕ → ℝ) (N : ℕ)
        {κ Damp qbar ρ c A Bmax : ℝ},
        let T := circularCaptureBlockTime ℓ
        let lam := circularCaptureBlockMultiplier ℓ
        let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
        let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
        let v := fun n : ℕ => J (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
        let α := fun n => Q (v n)
        let w := fun n => v n - x (α n) 0
        0 < N → 1 < qbar → qbar ^ 2 < lam → q + 3 * C * Damp ≤ qbar →
        0 ≤ κ → κ ≤ κ₀ → 3 * Damp ≤ d → 0 ≤ ρ → 0 < c → 0 ≤ A →
        c * ρ ^ 6 ≤ ‖α 0‖ → 0 < ‖α 0‖ → ‖α 0‖ * lam ^ N ≤ Damp →
        9 * C * Damp / (lam - 1) + 3 * (Ec * κ) * (N : ℝ) ≤ 1 / 16 →
        ‖w 0‖ ≤ ‖α 0‖ / 32 →
        (∀ n ≤ N, ∑ j ∈ Finset.range n, (Ec * B j) / lam ^ (j + 1) ≤ ‖α 0‖ / 32) →
        (∀ n ≤ N, ‖w 0‖ + ∑ j ∈ Finset.range n, (Ec * B j) / qbar ^ (j + 1) ≤ A * ρ ^ 6) →
        (∀ n < N, 0 ≤ B n ∧ B n ≤ Bmax) → Bmax + κ * (3 * Damp) ≤ ε₀ →
        (∀ t ∈ Icc (0 : ℝ) ((N : ℝ) * T),
          HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
        (∀ t ∈ Icc (0 : ℝ) ((N : ℝ) * T),
          ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ rn) →
        (∀ t ∈ Icc (0 : ℝ) ((N : ℝ) * T), ∀ i, y t i ∈ fourfoldLittleContourSubmodule γ) →
        (∀ t ∈ Icc (0 : ℝ) ((N : ℝ) * T), ∀ i,
          littleContourArea γ (y t i) = Real.pi * circularContourRadii i ^ 2) →
        (∀ n < N, ∀ u ∈ Icc (0 : ℝ) T,
          ‖p ((n : ℝ) * T + u)‖ ≤ B n + κ *
            ‖y ((n : ℝ) * T + u) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + u)‖) →
        (∀ n ≤ N, (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
          ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
          ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n) ∧
        (∀ n < N, ∀ u ∈ Icc (0 : ℝ) T,
          ‖y ((n : ℝ) * T + u) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + u)‖ ≤
            H * ((11 / 8 : ℝ) * ‖α 0‖ * lam ^ n + B n)) ∧
        ∀ t ∈ Icc (0 : ℝ) ((N : ℝ) * T),
          let vc := J (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1)
          ‖vc - x (Q vc) 0‖ ≤ Eg *
            (A * (Damp / c + 1) * ρ ^ 3 + 3 * (Ec * κ) * Damp / (lam - qbar) + Bmax + κ * Rg) := by
  obtain ⟨ℓ, hℓ, q, hq, hqgap, C, hC, dc, hdc, hdcr, Ec, hEc, rc, hrc,
    κ₀, hκ₀, ε₀, hε₀, H, hH, hcapture⟩ :=
    exists_circular_existing_sharp_finite_capture hγ hγ1 hR hr hX hd hfix hareaX hg
  obtain ⟨dg, hdg, hdgr, rg, hrg, Eg, hEg, hblocks⟩ :=
    exists_circular_capture_offGraph_block_constants hγ hγ1 hR hr hℓ hX hd hfix hareaX hg
  obtain ⟨e, he, hchart⟩ := exists_circular_actualConstraintChart_radius hγ hγ1
  let d := min dc dg
  let rn := min rc (min rg (e / 2))
  have hdpos : 0 < d := lt_min hdc hdg
  have hrn : 0 < rn := lt_min hrc (lt_min hrg (by positivity))
  refine ⟨ℓ, hℓ, q, hq, hqgap, C, hC, d, hdpos, (min_le_left _ _).trans hdcr,
    Ec, hEc, rn, hrn, κ₀, hκ₀, ε₀, hε₀, H, hH, Eg, hEg, rg, hrg, ?_⟩
  intro y p B N κ Damp qbar ρ c A Bmax
  dsimp only
  let T := circularCaptureBlockTime ℓ
  let lam := circularCaptureBlockMultiplier ℓ
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let v := fun n : ℕ => J (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
  let α := fun n => Q (v n)
  let w := fun n => v n - x (α n) 0
  intro hN hqbar hgapbar hcompbar hκ hκcap hDd hρ hc hA hseed ha hterminal hsmall hw0
    hmargin hslow hB hcap hyd hnear hfour harea hforce
  have hT : 0 < T := circularCaptureBlockTime_pos hℓ
  have hlam : 1 < lam := by nlinarith only [hq, hqgap, sq_nonneg (q - 1)]
  have hqbarLam : qbar < lam := by nlinarith only [hqbar, hgapbar, sq_nonneg (qbar - 1)]
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) T :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * ℓ)
  have hgridtime (n : ℕ) (hn : n ≤ N) : (n : ℝ) * T ∈ Icc (0 : ℝ) ((N : ℝ) * T) :=
    ⟨mul_nonneg (Nat.cast_nonneg n) hT.le, mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hT.le⟩
  have hgridchart (n : ℕ) (hn : n ≤ N) : circularConstrainedChart hγ hγ1 (v n) = y ((n : ℝ) * T) := by
    have href : littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T) = littleCircularReference hγ hγ1 :=
      (hperiod.nat_mul_eq n).trans (littleCircularMaterialContours_zero hγ hγ1)
    have hh := hnear _ (hgridtime n hn)
    rw [href] at hh
    have hrne : rn < e :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self he)
    exact hchart _ (by simpa only [mem_ball, dist_eq_norm] using hh.trans_lt hrne)
      (hfour _ (hgridtime n hn)) (harea _ (hgridtime n hn))
  have hBc (n : ℕ) (hn : n < N) : 0 ≤ B n ∧ B n + κ * (3 * Damp) ≤ ε₀ :=
    ⟨(hB n hn).1, (add_le_add (hB n hn).2 le_rfl).trans hcap⟩
  have hcapt := hcapture y p N B hqbar hgapbar hcompbar hκ hκcap
    (hDd.trans (min_le_left _ _)) ha hterminal hsmall
    (by simpa only [sub_sub_sub_cancel_right] using hw0) hmargin hBc hgridchart hyd
    (fun t ht => (hnear t ht).trans (min_le_left _ _)) hforce
  have hcoarse : ∀ n ≤ N, (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
      ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
      ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n := by
    intro n hn
    simpa only [sub_sub_sub_cancel_right] using hcapt.1 n hn
  have hsharp (n : ℕ) (hn : n ≤ N) :
      ‖w n‖ ≤ qbar ^ n * (A * ρ ^ 6) + (Ec * κ) * (3 * ‖α 0‖) * lam ^ n / (lam - qbar) := by
    have hh := hcapt.2.2 n hn
    have hb := mul_le_mul_of_nonneg_left (hslow n hn) (pow_nonneg (zero_lt_one.trans hqbar).le n)
    have hh' : ‖w n‖ ≤ qbar ^ n * (‖w 0‖ + ∑ j ∈ Finset.range n, (Ec * B j) / qbar ^ (j + 1)) +
        (Ec * κ) * (3 * ‖α 0‖) * lam ^ n / (lam - qbar) := by
      simpa only [sub_sub_sub_cancel_right] using hh
    exact hh'.trans (add_le_add hb le_rfl)
  have hwscale (n : ℕ) (hn : n ≤ N) :
      ‖w n‖ ≤ A * (Damp / c + 1) * ρ ^ 3 + 3 * (Ec * κ) * Damp / (lam - qbar) := by
    have hterm : ‖α 0‖ * lam ^ n ≤ Damp :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam.le hn) (norm_nonneg _)).trans hterminal
    exact sharp_capture_error_le_cube hρ hc (zero_lt_one.trans hqbar).le hgapbar.le hqbarLam
      (mul_nonneg hEc.le hκ) hA hseed n hterm (hsharp n hn)
  have hsize (n : ℕ) (hn : n < N) (_hnt : (n : ℝ) * T ≤ (N : ℝ) * T) : ‖α n‖ + ‖w n‖ ≤ dg := by
    have hh := hcoarse n hn.le
    have hterm : ‖α 0‖ * lam ^ n ≤ Damp :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam.le hn.le) (norm_nonneg _)).trans hterminal
    have hscale : 0 ≤ ‖α 0‖ * lam ^ n := mul_nonneg (norm_nonneg _) (pow_nonneg (zero_lt_one.trans hlam).le n)
    have hlocal : ‖α n‖ + ‖w n‖ ≤ 3 * Damp := by nlinarith only [hh.2.1, hh.2.2, hterm, hscale]
    exact hlocal.trans (hDd.trans (min_le_right _ _))
  have hglobal := hblocks y p B N hN ⟨by positivity, le_rfl⟩ hκ (fun n hn => (hB n hn).1)
    (fun n hn _ => hgridchart n hn.le) hsize hyd
    (fun t ht => (hnear t ht).trans ((min_le_right _ _).trans (min_le_left _ _)))
    (fun n hn u hu _ => hforce n hn u hu)
  refine ⟨hcoarse, ?_, ?_⟩
  · simpa only using hcapt.2.1
  · intro t ht
    obtain ⟨n, hn, u, hu, htime, herr⟩ := hglobal t ht
    have hright := add_le_add (add_le_add (hwscale n hn.le) (hB n hn).2) (le_refl (κ * rg))
    exact herr.trans (mul_le_mul_of_nonneg_left hright hEg.le)

end Euler2D

end
