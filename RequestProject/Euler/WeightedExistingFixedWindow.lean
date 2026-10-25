module

public import RequestProject.Euler.BanachWeightedTrajectoryEnvelope

/-! On a fixed time window the genuine weighted trajectory envelope
retains its small factor h. It is not replaced by an O(1) bound. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5000

noncomputable section

open Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_existing_trajectory_fixed_window_bound
    {f : E → E} {U : Set E} {K b : ℝ≥0} (hLip : LipschitzOnWith K f U)
    {h H T β L F νbar : ℝ} (hh : 0 < h) (hH : 0 ≤ H) (hHT : H ≤ T)
    (hβ : 0 ≤ β) (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hνup : ((b * K : ℝ≥0) : ℝ) + β ≤ νbar)
    (k : ℕ) (a : ℕ → ℝ≥0) (ha : ∀ j : Fin k, a j ≤ b)
    (y c p : ℕ → ℝ → E)
    (hyd : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt (y j) ((a j : ℝ) • f (y j t) + p j t) t)
    (hcd : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt (c j) ((a j : ℝ) • f (c j t)) t)
    (hym : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) H, y j t ∈ U)
    (hcm : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) H, c j t ∈ U)
    (hinit : weightedFamilyNorm h k (fun i => y i 0 - c i 0) ≤ L * h)
    (hp : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) H,
      ‖p j t‖ ≤ h ^ (k - (j : ℕ)) *
        (β * weightedFamilyNorm h k (fun i => y i t - c i t) + F * h)) :
    ∀ t ∈ Icc (0 : ℝ) H,
      weightedFamilyNorm h k (fun i => y i t - c i t) ≤
        (L + F * T) * Real.exp (νbar * T) * h := by
  let ν : ℝ := ((b * K : ℝ≥0) : ℝ) + β
  have hν : 0 ≤ ν := add_nonneg (b * K).coe_nonneg hβ
  have hνbar : 0 ≤ νbar := hν.trans hνup
  have hT : 0 ≤ T := hH.trans hHT
  have hwhole := weighted_existing_trajectory_integral_envelope hLip hh hH hβ k a ha y c p
    (fun _ => F * h) continuousOn_const (fun _ _ => mul_nonneg hF hh.le) hyd hcd hym hcm hp
  intro t ht
  have htT : t ≤ T := ht.2.trans hHT
  have hexp : Real.exp (ν * t) ≤ Real.exp (νbar * T) :=
    Real.exp_le_exp.mpr (mul_le_mul hνup htT ht.1 hνbar)
  have hbase : weightedFamilyNorm h k (fun i => y i 0 - c i 0) * Real.exp (ν * t) ≤
      (L * h) * Real.exp (νbar * T) :=
    mul_le_mul hinit hexp (Real.exp_pos _).le (mul_nonneg hL hh.le)
  have hint : (∫ s in (0)..t, Real.exp (ν * (t - s)) * (F * h)) ≤
      t * (Real.exp (νbar * T) * (F * h)) := by
    calc
      _ ≤ ∫ _s in (0)..t, Real.exp (νbar * T) * (F * h) := by
        apply intervalIntegral.integral_mono_on ht.1
          ((by fun_prop : Continuous (fun s : ℝ => Real.exp (ν * (t - s)) * (F * h))).intervalIntegrable 0 t)
          (continuous_const.intervalIntegrable 0 t)
        intro s hs
        have htime : t - s ≤ T := by linarith only [hs.1, htT]
        have he : Real.exp (ν * (t - s)) ≤ Real.exp (νbar * T) :=
          Real.exp_le_exp.mpr (mul_le_mul hνup htime (sub_nonneg.mpr hs.2) hνbar)
        exact mul_le_mul_of_nonneg_right he (mul_nonneg hF hh.le)
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hn := hwhole t ht
  change weightedFamilyNorm h k (fun i => y i t - c i t) ≤
    weightedFamilyNorm h k (fun i => y i 0 - c i 0) * Real.exp (ν * t) +
      ∫ s in (0)..t, Real.exp (ν * (t - s)) * (F * h) at hn
  calc
    _ ≤ (L * h) * Real.exp (νbar * T) + t * (Real.exp (νbar * T) * (F * h)) :=
      hn.trans (add_le_add hbase hint)
    _ ≤ (L * h) * Real.exp (νbar * T) + T * (Real.exp (νbar * T) * (F * h)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right htT (by positivity))
    _ = (L + F * T) * Real.exp (νbar * T) * h := by ring

end Euler2D

end
