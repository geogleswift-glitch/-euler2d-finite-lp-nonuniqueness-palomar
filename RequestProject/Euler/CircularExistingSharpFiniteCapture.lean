module

public import RequestProject.Euler.CircularExistingProportionalCaptureStep
public import RequestProject.Euler.FiniteSharpCaptureComplement
public import RequestProject.Euler.FiniteCaptureBootstrap
public import RequestProject.Euler.CircularCaptureBlockClock
public import RequestProject.Euler.ContinuousCaptureSection

/-! The fixed old constraint coordinates of the same existing path
give the finite capture recurrence. No new sequence or flow is assumed. -/

@[expose] public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 6000

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

theorem exists_circular_existing_sharp_finite_capture {γ : ℝ≥0}
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
        ∀ (y p : ℝ → Fin 2 → LittleContourSpace γ) (N : ℕ) (B : ℕ → ℝ) {κ D qbar : ℝ},
        let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
          (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
        let α := fun n => P (v n)
        let w := fun n => (v n - α n) - g (α n)
        1 < qbar → qbar ^ 2 < lam → q + 3 * C * D ≤ qbar →
        0 ≤ κ → κ ≤ κ₀ → 3 * D ≤ d →
        0 < ‖α 0‖ → ‖α 0‖ * lam ^ N ≤ D →
        9 * C * D / (lam - 1) + 3 * (E * κ) * (N : ℝ) ≤ 1 / 16 →
        ‖w 0‖ ≤ ‖α 0‖ / 32 →
        (∀ n ≤ N, ∑ j ∈ Finset.range n, (E * B j) / lam ^ (j + 1) ≤ ‖α 0‖ / 32) →
        (∀ n < N, 0 ≤ B n ∧ B n + κ * (3 * D) ≤ ε₀) →
        (∀ n ≤ N, circularConstrainedChart hγ hγ1 (v n) = y ((n : ℝ) * T)) →
        (∀ t ∈ Icc (0 : ℝ) ((N : ℝ) * T),
          HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
        (∀ t ∈ Icc (0 : ℝ) ((N : ℝ) * T), ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ r) →
        (∀ n < N, ∀ t ∈ Icc (0 : ℝ) T, ‖p ((n : ℝ) * T + t)‖ ≤
          B n + κ * ‖y ((n : ℝ) * T + t) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + t)‖) →
        (∀ n ≤ N, (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
          ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
          ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n) ∧
        (∀ n < N, ∀ t ∈ Icc (0 : ℝ) T,
          ‖y ((n : ℝ) * T + t) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + t)‖ ≤
            H * ((11 / 8 : ℝ) * ‖α 0‖ * lam ^ n + B n)) ∧
        ∀ n ≤ N,
          ‖w n‖ ≤ qbar ^ n * (‖w 0‖ + ∑ j ∈ Finset.range n, (E * B j) / qbar ^ (j + 1)) +
            (E * κ) * (3 * ‖α 0‖) * lam ^ n / (lam - qbar) := by
  obtain ⟨k, hk, q, hq, hgap, C, hC, d, hd₀, hdr, E, hE, r, hr, κ₀, hκ₀, ε₀, hε₀, H, hH, hstep⟩ :=
    exists_circular_existing_proportional_capture_step hγ hγ1 hR hr₀ hX hd hfix harea hg
  refine ⟨k, hk, q, hq, hgap, C, hC, d, hd₀, hdr, E, hE, r, hr, κ₀, hκ₀, ε₀, hε₀, H, hH, ?_⟩
  intro y p N B κ D qbar
  dsimp only
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let g := fun v => x v 0 - v
  let T := circularCaptureBlockTime k
  let lam := circularCaptureBlockMultiplier k
  let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
    (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
  let α := fun n => P (v n)
  let w := fun n => (v n - α n) - g (α n)
  intro hqbar hgapbar hcompbar hκ hκcap hDd ha hterminal hsmall hw0 hf hB hchart hyd hnear hp
  have hqbarLam : qbar < lam := by nlinarith only [hqbar, hgapbar, sq_nonneg (qbar - 1)]
  have hcomp : q + 3 * C * D ≤ lam := hcompbar.trans hqbarLam.le
  have hT : 0 < T := circularCaptureBlockTime_pos hk
  have hlam : 1 < lam := by
    change 1 < circularCaptureBlockMultiplier k
    rw [circularCaptureBlockMultiplier_eq_exp]
    exact Real.one_lt_exp_iff.mpr (mul_pos sigma_pos hT)
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) T :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * k)
  have hcshift (n : ℕ) (t : ℝ) :
      littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + t) = littleCircularMaterialContours hγ hγ1 t := by
    simpa only [add_comm] using (hperiod.nat_mul n) t
  have hlocal (n : ℕ) (hn : n < N) (hs : ‖α n‖ + ‖w n‖ ≤ 3 * D) :
      ‖α (n + 1) - lam • α n‖ ≤ C * (‖α n‖ + ‖w n‖) ^ 2 + E * B n +
        (E * κ) * (‖α n‖ + ‖w n‖) ∧
      ‖w (n + 1)‖ ≤ q * ‖w n‖ + C * (‖α n‖ + ‖w n‖) * ‖w n‖ + E * B n +
        (E * κ) * (‖α n‖ + ‖w n‖) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖y ((n : ℝ) * T + t) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + t)‖ ≤
          H * (‖α n‖ + ‖w n‖ + B n) := by
    have hsd : ‖α n‖ + ‖w n‖ ≤ d := hs.trans hDd
    have hα : P (α n) = α n := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le (v n)
    have hαr : ‖α n‖ ≤ r₀ / 2 := (le_add_of_nonneg_right (norm_nonneg (w n))).trans (hsd.trans hdr)
    have hcoord := hg.coordinate (α n) hα hαr
    have hPg : P (g (α n)) = 0 := by
      dsimp only [g]
      rw [P.map_sub, hcoord, hα, sub_self]
    have hwP : P (w n) = 0 := by
      dsimp only [w]
      rw [P.map_sub, P.map_sub, hPg, hα]
      change α n - α n - 0 = 0
      simp only [sub_self, sub_zero]
    have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        (n : ℝ) * T + t ∈ Icc (0 : ℝ) ((N : ℝ) * T) := by
      refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg n) hT.le) ht.1, ?_⟩
      have hh := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.succ_le_of_lt hn) : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ)) hT.le
      push_cast at hh
      nlinarith only [hh, ht.2]
    have hinit : y ((n : ℝ) * T + 0) = circularConstrainedChart hγ hγ1 (α n + g (α n) + w n) := by
      have he : α n + g (α n) + w n = v n := by dsimp only [w]; module
      rw [add_zero, he]
      exact (hchart n hn.le).symm
    have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        HasDerivAt (fun s => y ((n : ℝ) * T + s))
          (circularBanachField hγ hγ1 (y ((n : ℝ) * T + t)) + p ((n : ℝ) * T + t)) t := by
      have hh := (hyd _ (htime t ht)).scomp t ((hasDerivAt_id t).const_add ((n : ℝ) * T))
      simp only [Function.comp_def, one_smul] at hh
      change HasDerivAt (fun s : ℝ => y ((n : ℝ) * T + s))
        (circularBanachField hγ hγ1 (y ((n : ℝ) * T + t)) + p ((n : ℝ) * T + t)) t
      exact hh
    have hnear' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        ‖y ((n : ℝ) * T + t) - littleCircularMaterialContours hγ hγ1 t‖ ≤ r := by
      have hh := hnear _ (htime t ht)
      change ‖y ((n : ℝ) * T + t) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + t)‖ ≤ r at hh
      simpa only [hcshift] using hh
    have hp' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        ‖p ((n : ℝ) * T + t)‖ ≤ B n + κ * ‖y ((n : ℝ) * T + t) - littleCircularMaterialContours hγ hγ1 t‖ := by
      have hh := hp n hn t ht
      change ‖p ((n : ℝ) * T + t)‖ ≤ B n + κ *
        ‖y ((n : ℝ) * T + t) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + t)‖ at hh
      simpa only [hcshift] using hh
    have hforcing : B n + κ * (‖α n‖ + ‖w n‖) ≤ ε₀ :=
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hκ)).trans (hB n hn).2
    have hh := hstep (α n) (w n) hα hwP hsd (hB n hn).1 hκ hκcap hforcing
      (fun s => y ((n : ℝ) * T + s)) (fun s => p ((n : ℝ) * T + s)) hinit hderiv hnear' hp'
    have hgrid : (n : ℝ) * T + ((2 * k : ℕ) : ℝ) * period = ((n + 1 : ℕ) : ℝ) * T := by
      dsimp only [T, circularCaptureBlockTime]
      push_cast
      ring
    simp only at hh
    rw [hgrid] at hh
    refine ⟨?_, ?_, ?_⟩
    · simpa only [α, v, lam, circularCaptureBlockMultiplier, mul_assoc] using hh.1
    · simpa only [w, α, v, mul_assoc] using hh.2.1
    · intro t ht
      simpa only [hcshift] using hh.2.2 t ht
  have hcapture := finite_capture_bootstrap α w (fun n => E * B n) hlam hC.le
    (mul_nonneg hE.le hκ) ha hterminal hcomp hsmall hw0 hf
    (fun n hn hs => ⟨(hlocal n hn hs).1, (hlocal n hn hs).2.1⟩)
  have hsharp := finite_capture_sharp_complement_of_envelope α w (fun n => E * B n)
    hlam (zero_lt_one.trans hqbar) hqbarLam hC.le (mul_nonneg hE.le hκ)
    hterminal hcompbar (fun n hn => (hcapture n hn).2)
    (fun n hn hs => (hlocal n hn hs).2.1)
  refine ⟨hcapture, ?_, hsharp⟩
  intro n hn t ht
  have henv := hcapture n hn.le
  have hterm : ‖α 0‖ * lam ^ n ≤ D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam.le hn.le) ha.le).trans hterminal
  have hscale : 0 ≤ ‖α 0‖ * lam ^ n := mul_nonneg ha.le (pow_nonneg (zero_lt_one.trans hlam).le _)
  have hsize : ‖α n‖ + ‖w n‖ ≤ 3 * D := by
    nlinarith only [henv.2.1, henv.2.2, hterm, hscale]
  have hs : ‖α n‖ + ‖w n‖ ≤ (11 / 8 : ℝ) * ‖α 0‖ * lam ^ n := by
    linarith only [henv.2.1, henv.2.2]
  exact ((hlocal n hn hsize).2.2 t ht).trans
    (mul_le_mul_of_nonneg_left (add_le_add hs le_rfl) hH.le)

end Euler2D

end
