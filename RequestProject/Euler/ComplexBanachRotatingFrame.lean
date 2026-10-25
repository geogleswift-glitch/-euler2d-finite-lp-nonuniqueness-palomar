module

public import Mathlib

/-! Exact removal of a genuine constant rigid angular velocity, with
the original absolute time and entrance time retained. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open Complex Set Metric
open scoped NNReal

namespace Euler2D

def rigidRotationGauge (ω e t : ℝ) : ℂ := exp ((((t - e) * (-ω) : ℝ) : ℂ) * I)

theorem norm_rigidRotationGauge (ω e t : ℝ) : ‖rigidRotationGauge ω e t‖ = 1 :=
  norm_exp_ofReal_mul_I _

theorem rigidRotationGauge_ne_zero (ω e t : ℝ) : rigidRotationGauge ω e t ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem rigidRotationGauge_entrance (ω e : ℝ) : rigidRotationGauge ω e e = 1 := by
  simp [rigidRotationGauge]

theorem hasDerivAt_rigidRotationGauge (ω e t : ℝ) :
    HasDerivAt (rigidRotationGauge ω e)
      (rigidRotationGauge ω e t * ((-ω : ℂ) * I)) t := by
  have h := ((((hasDerivAt_id t).sub_const e).mul_const (-ω)).ofReal_comp.mul_const I).cexp
  unfold rigidRotationGauge
  simpa only [one_mul, id_eq, Complex.ofReal_neg] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

def rigidRotatedForcing (ω e : ℝ) (q : ℝ → E → E) (t : ℝ) (u : E) : E :=
  rigidRotationGauge ω e t • q t ((rigidRotationGauge ω e t)⁻¹ • u)

theorem hasDerivAt_rigidRotatedCurve {z : ℝ → E} {F : E → E} {q : ℝ → E → E}
    (ω e t : ℝ)
    (hz : HasDerivAt z (F (z t) + ((ω : ℂ) * I) • z t + q t (z t)) t)
    (hcov : F (rigidRotationGauge ω e t • z t) = rigidRotationGauge ω e t • F (z t)) :
    HasDerivAt (fun s => rigidRotationGauge ω e s • z s)
      (F (rigidRotationGauge ω e t • z t) +
        rigidRotatedForcing ω e q t (rigidRotationGauge ω e t • z t)) t := by
  have hh := (hasDerivAt_rigidRotationGauge ω e t).smul hz
  rw [hcov]
  unfold rigidRotatedForcing
  rw [inv_smul_smul₀ (rigidRotationGauge_ne_zero ω e t)]
  convert hh using 1
  module

theorem norm_rigidRotatedForcing (ω e t : ℝ) (q : ℝ → E → E) (u : E) :
    ‖rigidRotatedForcing ω e q t u‖ = ‖q t ((rigidRotationGauge ω e t)⁻¹ • u)‖ := by
  rw [rigidRotatedForcing, norm_smul, norm_rigidRotationGauge, one_mul]

theorem rigidRotatedForcing_lipschitzOn {q : ℝ → E → E} {L : ℝ} {K : ℝ≥0}
    (ω e t : ℝ) (hq : LipschitzOnWith K (q t) (ball 0 L)) :
    LipschitzOnWith K (rigidRotatedForcing ω e q t) (ball 0 L) := by
  have hg := norm_rigidRotationGauge ω e t
  have hi : ‖(rigidRotationGauge ω e t)⁻¹‖ = 1 := by rw [norm_inv, hg, inv_one]
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hu' : (rigidRotationGauge ω e t)⁻¹ • u ∈ ball (0 : E) L := by
    simpa only [mem_ball_zero_iff, norm_smul, hi, one_mul] using hu
  have hv' : (rigidRotationGauge ω e t)⁻¹ • v ∈ ball (0 : E) L := by
    simpa only [mem_ball_zero_iff, norm_smul, hi, one_mul] using hv
  have hh := hq.dist_le_mul _ hu' _ hv'
  change dist (rigidRotationGauge ω e t • _) (rigidRotationGauge ω e t • _) ≤ _
  simp only [dist_eq_norm, ← smul_sub, norm_smul, hg, hi, one_mul] at hh ⊢
  exact hh

theorem rigidRotatedForcing_bound {q : ℝ → E → E} {L B : ℝ}
    (ω e t : ℝ) (hq : ∀ u ∈ ball (0 : E) L, ‖q t u‖ ≤ B) :
    ∀ u ∈ ball (0 : E) L, ‖rigidRotatedForcing ω e q t u‖ ≤ B := by
  intro u hu
  rw [norm_rigidRotatedForcing]
  apply hq
  simpa only [mem_ball_zero_iff, norm_smul, norm_inv, norm_rigidRotationGauge, inv_one, one_mul] using hu

theorem rigidRotatedForcing_continuousOn {q : ℝ → E → E} {L : ℝ}
    {K : ℝ≥0} {J : Set ℝ} (ω e : ℝ)
    (hLip : ∀ t ∈ J, LipschitzOnWith K (q t) (ball 0 L))
    (hcont : ∀ u ∈ ball (0 : E) L, ContinuousOn (fun t => q t u) J) :
    ∀ u ∈ ball (0 : E) L, ContinuousOn (fun t => rigidRotatedForcing ω e q t u) J := by
  have hg : Continuous (rigidRotationGauge ω e) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_rigidRotationGauge ω e t).continuousAt)
  have hi : Continuous (fun t => (rigidRotationGauge ω e t)⁻¹) :=
    hg.inv₀ (fun t => rigidRotationGauge_ne_zero ω e t)
  have hjoint : ContinuousOn (Function.uncurry q) (J ×ˢ ball (0 : E) L) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K hLip hcont
  intro u hu
  have hc : ContinuousOn (fun t => q t ((rigidRotationGauge ω e t)⁻¹ • u)) J :=
    hjoint.comp (continuousOn_id.prodMk (hi.smul continuous_const).continuousOn) (by
      intro t ht
      refine ⟨ht, ?_⟩
      simpa only [Pi.smul_apply', mem_ball_zero_iff, norm_smul, norm_inv,
        norm_rigidRotationGauge, inv_one, one_mul] using hu)
  exact hg.continuousOn.smul hc

end Euler2D

end
