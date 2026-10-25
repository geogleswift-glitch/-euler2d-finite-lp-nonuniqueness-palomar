module

public import RequestProject.Euler.Delay
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Recovering continuous time evolution from its weak identity

Euler's time tests need only vanish before the final time; there is no
left support restriction. Antiderivatives of compactly supported tests
therefore recover the initial-value integral equation directly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

def IsTimeTest (T : ℝ) (η : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧ ∃ b < T, ∀ t ≥ b, η t = 0

def backwardsTimePrimitive (T : ℝ) (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in t..T, θ s

lemma hasDerivAt_backwardsTimePrimitive {θ : ℝ → ℝ} (hθ : Continuous θ) (T t : ℝ) :
    HasDerivAt (backwardsTimePrimitive T θ) (-θ t) t :=
  intervalIntegral.integral_hasDerivAt_left (hθ.intervalIntegrable _ _)
    hθ.aestronglyMeasurable.stronglyMeasurableAtFilter hθ.continuousAt

lemma contDiff_backwardsTimePrimitive {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (T : ℝ) :
    ContDiff ℝ ∞ (backwardsTimePrimitive T θ) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (hasDerivAt_backwardsTimePrimitive hθ.continuous T t).differentiableAt, ?_⟩
  have heq : deriv (backwardsTimePrimitive T θ) = fun t => -θ t :=
    funext fun t => (hasDerivAt_backwardsTimePrimitive hθ.continuous T t).deriv
  rw [heq]
  exact hθ.neg

lemma isTimeTest_backwardsTimePrimitive {θ : ℝ → ℝ} {T : ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hs : ∃ b < T, ∀ t ≥ b, θ t = 0) :
    IsTimeTest T (backwardsTimePrimitive T θ) := by
  obtain ⟨b, hb, hs⟩ := hs
  refine ⟨contDiff_backwardsTimePrimitive hθ T, b, hb, fun t ht => ?_⟩
  unfold backwardsTimePrimitive
  apply intervalIntegral.integral_zero_ae
  exact Eventually.of_forall fun s hs' => hs s
    ((le_min ht hb.le).trans (show min t T ≤ s from (uIoc_subset_uIcc hs').1))

lemma exists_right_time_support_of_compact {θ : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hθ : HasCompactSupport θ) (hs : tsupport θ ⊆ Ioo 0 T) :
    ∃ b < T, ∀ t ≥ b, θ t = 0 := by
  rcases (tsupport θ).eq_empty_or_nonempty with hempty | hne
  · refine ⟨0, hT, fun t _ => ?_⟩
    exact image_eq_zero_of_notMem_tsupport (by simp [hempty])
  obtain ⟨b, hb, hmax⟩ := hθ.exists_isMaxOn hne continuous_id.continuousOn
  refine ⟨(b + T) / 2, by linarith [(hs hb).2], fun t ht => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hmax hmem
  change t ≤ b at this
  linarith [(hs hb).2]

/-- A continuous scalar weak evolution has the expected initial-value
integral formula. No time differentiability is assumed. -/
theorem eq_integral_of_weak_time_identity {T : ℝ} (hT : 0 < T)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hweak : ∀ η : ℝ → ℝ, IsTimeTest T η →
      (∫ t in (0 : ℝ)..T, f t * deriv η t + g t * η t) + f 0 * η 0 = 0) :
    ∀ t ∈ Icc 0 T, f t = f 0 + ∫ s in (0 : ℝ)..t, g s := by
  let H : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s
  have hHder (t : ℝ) : HasDerivAt H (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun t => (hHder t).continuousAt
  let r : ℝ → ℝ := fun t => f t - H t - f 0
  have hr : Continuous r := (hf.sub hH).sub continuous_const
  have htest : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo 0 T → (∫ t, θ t • r t) = 0 := by
    intro θ hθ hc hs
    let η := backwardsTimePrimitive T θ
    have hη : IsTimeTest T η := isTimeTest_backwardsTimePrimitive hθ
      (exists_right_time_support_of_compact hT hc hs)
    have hηder (t : ℝ) : HasDerivAt η (-θ t) t :=
      hasDerivAt_backwardsTimePrimitive hθ.continuous T t
    have hηc : Continuous η := hη.1.continuous
    have hηd : deriv η = fun t => -θ t := funext fun t => (hηder t).deriv
    have hw := hweak η hη
    have hp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
      hH.continuousOn hηc.continuousOn (fun t _ => hHder t)
      (fun t _ => hηder t) (hg.intervalIntegrable 0 T)
      (hθ.continuous.neg.intervalIntegrable 0 T)
    have hηT : η T = 0 := by simp [η, backwardsTimePrimitive]
    have hH0 : H 0 = 0 := by simp [H]
    rw [hηT, hH0, mul_zero, zero_mul, sub_zero] at hp
    simp_rw [hηd] at hw
    have hF : IntervalIntegrable (fun t => f t * -θ t) volume 0 T :=
      (hf.mul hθ.continuous.neg).intervalIntegrable 0 T
    have hG : IntervalIntegrable (fun t => g t * η t) volume 0 T :=
      (hg.mul hηc).intervalIntegrable 0 T
    have hR : IntervalIntegrable (fun t => H t * -θ t) volume 0 T :=
      (hH.mul hθ.continuous.neg).intervalIntegrable 0 T
    rw [intervalIntegral.integral_add hF hG] at hw
    rw [intervalIntegral.integral_add hG hR] at hp
    have hcalc : (∫ t in (0 : ℝ)..T, θ t * r t) = 0 := by
      have heq (t : ℝ) : θ t * r t =
          -(f t * -θ t) + H t * -θ t - f 0 * θ t := by dsimp only [r]; ring
      simp_rw [heq]
      have hN : IntervalIntegrable (fun t => -(f t * -θ t)) volume 0 T := hF.neg
      have hNR : IntervalIntegrable (fun t => -(f t * -θ t) + H t * -θ t) volume 0 T :=
        hN.add hR
      have hZ : IntervalIntegrable (fun t => f 0 * θ t) volume 0 T :=
        (continuous_const.mul hθ.continuous).intervalIntegrable 0 T
      rw [intervalIntegral.integral_sub hNR hZ,
        intervalIntegral.integral_add hN hR, intervalIntegral.integral_neg,
        intervalIntegral.integral_const_mul]
      change -(∫ t in (0 : ℝ)..T, f t * -θ t) + (∫ t in (0 : ℝ)..T, H t * -θ t) -
        f 0 * η 0 = 0
      linarith
    have hext : (∫ t in Ioc (0 : ℝ) T, θ t * r t) = ∫ t, θ t * r t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
        have hzero : θ t = 0 := image_eq_zero_of_notMem_tsupport fun hm =>
          ht ⟨(hs hm).1, (hs hm).2.le⟩
        rw [hzero, zero_mul]
    simpa only [smul_eq_mul, intervalIntegral.integral_of_le hT.le, hext] using hcalc
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hr.locallyIntegrable (μ := volume)).locallyIntegrableOn (Ioo 0 T)) htest
  have hrestr : r =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] (fun _ => 0) :=
    (ae_restrict_iff' measurableSet_Ioo).mpr hae
  have hpoint : EqOn r (fun _ => 0) (Ioo 0 T) :=
    Measure.eqOn_open_of_ae_eq hrestr isOpen_Ioo hr.continuousOn continuousOn_const
  have hclosure : closure (Ioo (0 : ℝ) T) ⊆ {t | r t = 0} :=
    closure_minimal hpoint (isClosed_eq hr continuous_const)
  rw [closure_Ioo hT.ne] at hclosure
  intro t ht
  have hzero := hclosure ht
  change f t - H t - f 0 = 0 at hzero
  dsimp only [H] at hzero
  linarith

end Euler2D

end
