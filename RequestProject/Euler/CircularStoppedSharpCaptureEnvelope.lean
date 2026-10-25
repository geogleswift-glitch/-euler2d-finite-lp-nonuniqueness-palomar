module

public import RequestProject.Euler.CircularExistingSharpFiniteCapture
public import RequestProject.Euler.CircularExistingPartialCaptureEnvelope
public import RequestProject.Euler.FiniteCaptureContinuousEnvelope

/-! Capture estimates on the actual stopped interval. Only completed
returns are used for the discrete induction. Every remaining block
portion is bounded directly on the already existing path. -/

@[expose] public section

set_option maxHeartbeats 24000000
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

theorem exists_circular_stopped_sharp_capture_envelope {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀)
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
      ∃ C > 0, ∃ d > 0, d ≤ r₀ / 2 ∧ ∃ E > 0, ∃ r > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0,
        ∀ (y p : ℝ → Fin 2 → LittleContourSpace γ) (N : ℕ) (B : ℕ → ℝ) {κ Damp D qbar : ℝ},
        let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
          (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
        let α := fun n => P (v n)
        let w := fun n => (v n - α n) - g (α n)
        0 < N → D ∈ Icc (0 : ℝ) ((N : ℝ) * T) →
        1 < qbar → qbar ^ 2 < lam → q + 3 * C * Damp ≤ qbar →
        0 ≤ κ → κ ≤ κ₀ → 3 * Damp ≤ d →
        0 < ‖α 0‖ → ‖α 0‖ * lam ^ N ≤ Damp →
        9 * C * Damp / (lam - 1) + 3 * (E * κ) * (N : ℝ) ≤ 1 / 16 →
        ‖w 0‖ ≤ ‖α 0‖ / 32 →
        (∀ n ≤ N, ∑ j ∈ Finset.range n, (E * B j) / lam ^ (j + 1) ≤ ‖α 0‖ / 32) →
        (∀ n < N, 0 ≤ B n ∧ B n + κ * (3 * Damp) ≤ ε₀) →
        (∀ n ≤ N, (n : ℝ) * T ≤ D →
          circularConstrainedChart hγ hγ1 (v n) = y ((n : ℝ) * T)) →
        (∀ t ∈ Icc (0 : ℝ) D, HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
        (∀ t ∈ Icc (0 : ℝ) D, ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ r) →
        (∀ n < N, ∀ u ∈ Icc (0 : ℝ) T, (n : ℝ) * T + u ≤ D →
          ‖p ((n : ℝ) * T + u)‖ ≤ B n + κ *
            ‖y ((n : ℝ) * T + u) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + u)‖) →
        (∀ n ≤ N, (n : ℝ) * T ≤ D →
          (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
          ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
          ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n) ∧
        (∀ t ∈ Icc (0 : ℝ) D,
          ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ H * ‖α 0‖ * Real.exp (sigma * t)) ∧
        ∀ n ≤ N, (n : ℝ) * T ≤ D →
          ‖w n‖ ≤ qbar ^ n * (‖w 0‖ + ∑ j ∈ Finset.range n, (E * B j) / qbar ^ (j + 1)) +
            (E * κ) * (3 * ‖α 0‖) * lam ^ n / (lam - qbar) := by
  obtain ⟨k, hk, q, hq, hgap, C, hC, df, hdf, hdr, E, hE, rf, hrf, κf, hκf, ε₀, hε₀, _, _, hfinite⟩ :=
    exists_circular_existing_sharp_finite_capture hγ hγ1 hR hr₀ hX hd hfix harea hg
  let T := circularCaptureBlockTime k
  let lam := circularCaptureBlockMultiplier k
  have hT : 0 < T := circularCaptureBlockTime_pos hk
  have hlam : 1 < lam := by
    rw [show lam = Real.exp (sigma * T) from circularCaptureBlockMultiplier_eq_exp k]
    exact Real.one_lt_exp_iff.mpr (mul_pos sigma_pos hT)
  obtain ⟨dp, hdp, rp, hrp, Hp, hHp, κp, hκp, hpartial⟩ :=
    exists_circular_existing_partial_capture_envelope hγ hγ1 hT
  let d := min df (dp / 2)
  let r := min rf rp
  let κ₀ := min κf κp
  let H := (2 * Hp) * (11 / 8 + lam / (32 * E))
  have hdpos : 0 < d := lt_min hdf (by positivity)
  have hrpos : 0 < r := lt_min hrf hrp
  have hκpos : 0 < κ₀ := lt_min hκf hκp
  have hH : 0 < H := by dsimp only [H]; positivity
  refine ⟨k, hk, q, hq, hgap, C, hC, d, hdpos, (min_le_left _ _).trans hdr,
    E, hE, r, hrpos, κ₀, hκpos, ε₀, hε₀, H, hH, ?_⟩
  intro y p N B κ Damp D qbar
  dsimp only
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let g := fun v => x v 0 - v
  let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
    (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
  let α := fun n => P (v n)
  let w := fun n => (v n - α n) - g (α n)
  intro hN hD hqbar hqbarGap hcompbar hκ hκcap hDd ha hterminal hsmall hw0 hf hB hchart hyd hnear hp
  have hqt : 0 ≤ D / T := div_nonneg hD.1 hT.le
  let m := ⌊D / T⌋₊
  have hmt : (m : ℝ) * T ≤ D := (le_div_iff₀ hT).mp (Nat.floor_le hqt)
  have hmN : m ≤ N := by
    have hh := (Nat.floor_le hqt).trans ((div_le_iff₀ hT).mpr hD.2)
    exact_mod_cast hh
  have hgrid (n : ℕ) (hn : n ≤ m) : (n : ℝ) * T ≤ D :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hT.le).trans hmt
  have hbefore (n : ℕ) (hn : (n : ℝ) * T ≤ D) : n ≤ m :=
    (Nat.le_floor_iff hqt).mpr ((le_div_iff₀ hT).mpr hn)
  have hterminalm : ‖α 0‖ * lam ^ m ≤ Damp :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam.le hmN) ha.le).trans hterminal
  have hsmallm : 9 * C * Damp / (lam - 1) + 3 * (E * κ) * (m : ℝ) ≤ 1 / 16 := by
    have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmN) (show 0 ≤ 3 * (E * κ) by positivity)
    linarith only [hh, hsmall]
  have hfulltime (n : ℕ) (hn : n < m) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      (n : ℝ) * T + u ≤ D := by
    have hh := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Nat.succ_le_of_lt hn) : ((n + 1 : ℕ) : ℝ) ≤ (m : ℝ)) hT.le
    push_cast at hh
    have hh' : (n : ℝ) * T + u ≤ (m : ℝ) * T := by nlinarith only [hh, hu.2]
    exact hh'.trans hmt
  have hcompleted := hfinite y p m B (κ := κ) (D := Damp) (qbar := qbar) hqbar hqbarGap hcompbar hκ
    (hκcap.trans (min_le_left _ _)) (hDd.trans (min_le_left _ _))
    ha hterminalm hsmallm hw0
    (fun n hn => hf n (hn.trans hmN))
    (fun n hn => hB n (hn.trans_le hmN))
    (fun n hn => hchart n (hn.trans hmN) (hgrid n hn))
    (fun t ht => hyd t ⟨ht.1, ht.2.trans hmt⟩)
    (fun t ht => (hnear t ⟨ht.1, ht.2.trans hmt⟩).trans (min_le_left _ _))
    (fun n hn u hu => hp n (hn.trans_le hmN) u hu (hfulltime n hn u hu))
  have hendpoint (n : ℕ) (hn : (n : ℝ) * T ≤ D) :
      (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
      ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
      ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n :=
    hcompleted.1 n (hbefore n hn)
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) T :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * k)
  have hcshift (n : ℕ) (t : ℝ) :
      littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + t) = littleCircularMaterialContours hγ hγ1 t := by
    simpa only [add_comm] using (hperiod.nat_mul n) t
  have hblock (n : ℕ) (hn : n < N) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T)
      (hvalid : (n : ℝ) * T + u ≤ D) :
      ‖y ((n : ℝ) * T + u) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + u)‖ ≤
        (2 * Hp) * ((11 / 8 : ℝ) * ‖α 0‖ * lam ^ n + B n) := by
    have hnt : (n : ℝ) * T ≤ D := by linarith only [hu.1, hvalid]
    have henv := hendpoint n hnt
    have hstate : ‖α n‖ + ‖w n‖ ≤ (11 / 8 : ℝ) * ‖α 0‖ * lam ^ n := by
      linarith only [henv.2.1, henv.2.2]
    have hterm : ‖α 0‖ * lam ^ n ≤ Damp :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam.le hn.le) ha.le).trans hterminal
    have hscale : 0 ≤ ‖α 0‖ * lam ^ n := mul_nonneg ha.le (pow_nonneg (zero_lt_one.trans hlam).le n)
    have hsize : ‖α n‖ + ‖w n‖ ≤ 3 * Damp := by nlinarith only [hstate, hterm, hscale]
    have hα : P (α n) = α n := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le (v n)
    have hαr : ‖α n‖ ≤ r₀ / 2 :=
      (le_add_of_nonneg_right (norm_nonneg (w n))).trans
        (hsize.trans (hDd.trans ((min_le_left _ _).trans hdr)))
    have hxn := hg.norm_le (α n) hα hαr 0
    simp only [pow_zero, mul_one] at hxn
    have hvrepr : v n = x (α n) 0 + w n := by dsimp only [w, g]; module
    have hvnorm : ‖v n‖ ≤ 2 * (‖α n‖ + ‖w n‖) := by
      rw [hvrepr]
      have hh := (norm_add_le (x (α n) 0) (w n)).trans (add_le_add hxn le_rfl)
      linarith only [hh, norm_nonneg (w n)]
    have hvdp : v n ∈ closedBall (0 : CircularConstrainedTangentSpace γ) dp := by
      apply mem_closedBall_zero_iff.mpr
      have hdpart : d ≤ dp / 2 := min_le_right _ _
      linarith only [hvnorm, hsize, hDd, hdpart]
    let Dn := min T (D - (n : ℝ) * T)
    have hDn : Dn ∈ Icc (0 : ℝ) T :=
      ⟨le_min hT.le (sub_nonneg.mpr hnt), min_le_left _ _⟩
    have huDn : u ∈ Icc (0 : ℝ) Dn := by
      refine ⟨hu.1, le_min hu.2 ?_⟩
      linarith only [hvalid]
    have hlocaltime (s : ℝ) (hs : s ∈ Icc (0 : ℝ) Dn) :
        (n : ℝ) * T + s ∈ Icc (0 : ℝ) D := by
      refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg n) hT.le) hs.1, ?_⟩
      have hh := hs.2.trans (min_le_right T (D - (n : ℝ) * T))
      linarith only [hh]
    have hinit : y ((n : ℝ) * T + 0) = circularConstrainedChart hγ hγ1 (v n) := by
      simpa only [add_zero] using (hchart n hn.le hnt).symm
    have hderiv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) Dn) :
        HasDerivAt (fun t => y ((n : ℝ) * T + t))
          (circularBanachField hγ hγ1 (y ((n : ℝ) * T + s)) + p ((n : ℝ) * T + s)) s := by
      have hh := (hyd _ (hlocaltime s hs)).scomp s ((hasDerivAt_id s).const_add ((n : ℝ) * T))
      simpa only [one_smul] using hh
    have hnear' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) Dn) :
        ‖y ((n : ℝ) * T + s) - littleCircularMaterialContours hγ hγ1 s‖ ≤ rp := by
      have hh := hnear _ (hlocaltime s hs)
      change ‖y ((n : ℝ) * T + s) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + s)‖ ≤ r at hh
      rw [hcshift] at hh
      exact hh.trans (min_le_right _ _)
    have hp' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) Dn) :
        ‖p ((n : ℝ) * T + s)‖ ≤ B n + κ * ‖y ((n : ℝ) * T + s) - littleCircularMaterialContours hγ hγ1 s‖ := by
      have hh := hp n hn s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩ (hlocaltime s hs).2
      change ‖p ((n : ℝ) * T + s)‖ ≤ B n + κ *
        ‖y ((n : ℝ) * T + s) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + s)‖ at hh
      simpa only [hcshift] using hh
    have hh := hpartial (v n) hvdp (hB n hn).1 hκ (hκcap.trans (min_le_right _ _)) hDn
      (fun s => y ((n : ℝ) * T + s)) (fun s => p ((n : ℝ) * T + s)) hinit hderiv hnear' hp' u huDn
    have hrough : ‖y ((n : ℝ) * T + u) - littleCircularMaterialContours hγ hγ1 u‖ ≤
        (2 * Hp) * (‖α n‖ + ‖w n‖ + B n) := by
      have hvb := mul_le_mul_of_nonneg_left hvnorm hHp.le
      have hbpos := mul_nonneg hHp.le (hB n hn).1
      nlinarith only [hh, hvb, hbpos]
    rw [hcshift]
    exact hrough.trans (mul_le_mul_of_nonneg_left (add_le_add hstate le_rfl) (by positivity))
  refine ⟨fun n _ hnt => hendpoint n hnt, ?_, ?_⟩
  · exact finite_capture_stopped_continuous_exponential_envelope
      (fun t => y t - littleCircularMaterialContours hγ hγ1 t) sigma_pos.le hT
      (circularCaptureBlockMultiplier_eq_exp k) (show 0 ≤ 2 * Hp by positivity) ha.le hE hN hD.2
      B (fun n hn => (hB n hn).1) hf hblock
  · intro n hn hnt
    exact hcompleted.2.2 n (hbefore n hnt)

end Euler2D

end
