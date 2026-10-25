module

public import RequestProject.Euler.Envelope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-! Weighted norms of already existing trajectories obey an actual
integral inequality directly from their derivatives and the original
self-field Lipschitz bound. No new trajectory or linear propagator
is assumed or constructed. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightedFamilyDifference (h : ℝ) (k : ℕ) (x : ℕ → E) : Fin k → E :=
  fun j => (h ^ (k - (j : ℕ)))⁻¹ • x j

def weightedFamilyNorm (h : ℝ) (k : ℕ) (x : ℕ → E) : ℝ :=
  ‖weightedFamilyDifference h k x‖

theorem norm_le_weightedFamilyNorm {h : ℝ} (hh : 0 < h) (k : ℕ) (x : ℕ → E) (j : Fin k) :
    ‖x j‖ ≤ h ^ (k - (j : ℕ)) * weightedFamilyNorm h k x := by
  have hw : 0 < h ^ (k - (j : ℕ)) := pow_pos hh _
  have hn := norm_le_pi_norm (weightedFamilyDifference h k x) j
  change ‖(h ^ (k - (j : ℕ)))⁻¹ • x j‖ ≤ weightedFamilyNorm h k x at hn
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw] at hn
  exact (inv_mul_le_iff₀ hw).mp hn

theorem weighted_existing_trajectory_integral_envelope
    {f : E → E} {U : Set E} {K b : ℝ≥0} (hLip : LipschitzOnWith K f U)
    {h T β : ℝ} (hh : 0 < h) (hT : 0 ≤ T) (hβ : 0 ≤ β)
    (k : ℕ) (a : ℕ → ℝ≥0) (ha : ∀ j : Fin k, a j ≤ b)
    (y c p : ℕ → ℝ → E) (g : ℝ → ℝ)
    (hgc : ContinuousOn g (Icc (0 : ℝ) T)) (hgn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ g t)
    (hyd : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (y j) ((a j : ℝ) • f (y j t) + p j t) t)
    (hcd : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (c j) ((a j : ℝ) • f (c j t)) t)
    (hym : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T, y j t ∈ U)
    (hcm : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T, c j t ∈ U)
    (hp : ∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) T,
      ‖p j t‖ ≤ h ^ (k - (j : ℕ)) *
        (β * weightedFamilyNorm h k (fun i => y i t - c i t) + g t)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      weightedFamilyNorm h k (fun i => y i t - c i t) ≤
        weightedFamilyNorm h k (fun i => y i 0 - c i 0) *
          Real.exp ((((b * K : ℝ≥0) : ℝ) + β) * t) +
        ∫ s in (0)..t, Real.exp ((((b * K : ℝ≥0) : ℝ) + β) * (t - s)) * g s := by
  let z : ℝ → Fin k → E := fun t => weightedFamilyDifference h k (fun i => y i t - c i t)
  let zd : ℝ → Fin k → E := fun t j => (h ^ (k - (j : ℕ)))⁻¹ •
    ((a j : ℝ) • (f (y j t) - f (c j t)) + p j t)
  let ν : ℝ := ((b * K : ℝ≥0) : ℝ) + β
  have hν : 0 ≤ ν := add_nonneg (b * K).coe_nonneg hβ
  have hzd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt z (zd t) t := by
    apply hasDerivAt_pi.mpr
    intro j
    have hd := ((hyd j t ht).sub (hcd j t ht)).const_smul (h ^ (k - (j : ℕ)))⁻¹
    convert hd using 1 <;>
      (try funext s) <;>
      (try dsimp only [z, zd, weightedFamilyDifference, Pi.smul_def, Pi.sub_def]) <;>
      module
  have hzc : ContinuousOn z (Icc (0 : ℝ) T) :=
    fun t ht => (hzd t ht).continuousAt.continuousWithinAt
  have hnzd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖zd t‖ ≤ ν * ‖z t‖ + g t := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg hν (norm_nonneg _)) (hgn t ht))).mpr
    intro j
    have hw : 0 < h ^ (k - (j : ℕ)) := pow_pos hh _
    have hq := hp j t ht
    have hself : ‖f (y j t) - f (c j t)‖ ≤ (K : ℝ) * ‖y j t - c j t‖ := by
      simpa only [dist_eq_norm] using hLip.dist_le_mul _ (hym j t ht) _ (hcm j t ht)
    have hx := norm_le_weightedFamilyNorm hh k (fun i => y i t - c i t) j
    change ‖y j t - c j t‖ ≤ h ^ (k - (j : ℕ)) * ‖z t‖ at hx
    have hab : (a j : ℝ) * (K : ℝ) ≤ (b : ℝ) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right (show (a j : ℝ) ≤ (b : ℝ) from ha j) K.coe_nonneg
    have hraw : ‖(a j : ℝ) • (f (y j t) - f (c j t)) + p j t‖ ≤
        h ^ (k - (j : ℕ)) * (ν * ‖z t‖ + g t) := by
      calc
        _ ≤ (a j : ℝ) * ‖f (y j t) - f (c j t)‖ + ‖p j t‖ := by
          simpa only [norm_smul, Real.norm_of_nonneg (a j).coe_nonneg] using norm_add_le
            ((a j : ℝ) • (f (y j t) - f (c j t))) (p j t)
        _ ≤ (a j : ℝ) * ((K : ℝ) * (h ^ (k - (j : ℕ)) * ‖z t‖)) +
            h ^ (k - (j : ℕ)) * (β * ‖z t‖ + g t) := by
          exact add_le_add (mul_le_mul_of_nonneg_left
            (hself.trans (mul_le_mul_of_nonneg_left hx K.coe_nonneg)) (a j).coe_nonneg) hq
        _ ≤ h ^ (k - (j : ℕ)) * (ν * ‖z t‖ + g t) := by
          have hh' := mul_le_mul_of_nonneg_right hab (mul_nonneg hw.le (norm_nonneg (z t)))
          dsimp [ν]
          nlinarith only [hh']
    change ‖(h ^ (k - (j : ℕ)))⁻¹ • _‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw]
    exact (inv_mul_le_iff₀ hw).mpr hraw
  have hbase (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖z t‖ ≤ ‖z 0‖ + ∫ s in (0)..t, ν * ‖z s‖ + g s := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
    have hbc : ContinuousOn (fun s => ν * ‖z s‖ + g s) (Icc (0 : ℝ) t) :=
      ((continuousOn_const.mul hzc.norm).add hgc).mono hsub
    have hd := norm_sub_le_integral_of_norm_deriv_le_of_le ht.1 (hzc.mono hsub)
      (fun s hs => (hzd s (hsub (Ioo_subset_Icc_self hs))).differentiableAt.differentiableWithinAt)
      (ae_of_all _ (fun s hs => by
        rw [(hzd s (hsub (Ioo_subset_Icc_self hs))).deriv]
        exact hnzd s (hsub (Ioo_subset_Icc_self hs))))
      (hbc.intervalIntegrable_of_Icc ht.1)
    have hn := norm_le_norm_sub_add (z t) (z 0)
    linarith only [hn, hd]
  intro t ht
  have hfinal := scalar_convolution_gronwall_on hT hzc.norm hgc hν
    (A := ‖z 0‖) (c := 0) (fun t ht => by simpa using hbase t ht) ht
  simpa only [zero_add, z, ν, weightedFamilyNorm] using hfinal

end Euler2D

end

