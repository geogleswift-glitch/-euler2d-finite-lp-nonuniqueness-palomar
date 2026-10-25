module

public import RequestProject.Euler.CircularForcedIntervalComparison
public import RequestProject.Euler.UniformNormalizedActualTorusForcing
public import RequestProject.Euler.UniformForcedPeriodSmallness

/-! A normalized actual torus-forced circular P has a common
initial ball and common forcing threshold. Every constant precedes the
Euler system, small source radius, and normalization scales. -/

@[expose] public section

set_option maxHeartbeats 4500000
set_option maxRecDepth 4000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) uniformActualIntervalLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) uniformActualIntervalLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_uniform_circular_actualTorus_forced_interval {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {M : ℝ} (hM : 0 ≤ M)
    {P : ℝ} (hP : 0 < P) :
    ∃ L > 0, ∃ K : ℝ≥0, ∃ δ > 0, ∃ η > 0, ∃ C > 0, ∃ Kphys : ℝ≥0,
      ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {w : R2 → ℝ}, w =ᵐ[μT] (f : R2 → ℝ) → IsTorusPeriodic w →
      (∀ x, w (torusQuarterTurn x) = w x) → (∫ x in torusBox, f x) = 0 →
      (∫ x in torusBox, |f x|) ≤ M →
      ∀ {ε a : ℝ}, 0 < ε → ε ≤ T → 0 < a → a ≤ 1 / 16 →
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
        a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) →
      ∃ E : ℝ → LittleContourSpace γ → LittleContourSpace γ,
      ∀ {R A : ℝ}, 0 < R → 0 < A → P / A ≤ ε →
        R * L < a / 4 → (L + 1) * R ≤ a / 2 → (Kphys : ℝ) ≤ A →
        C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
          (∫ x in torusBox, |f x|) / A ≤ η →
        ∃ Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
          IsNonautonomousBanachFlowOn
            (fun t Z => circularBanachField hγ hγ1 Z +
              fun i => rescaledBanachForcing E A R t (Z i))
            (circularBanachDomain hγ hγ1)
            (ball (littleCircularReference hγ hγ1) δ) P Y ∧
          (∀ Z ∈ ball (littleCircularReference hγ hγ1) δ, ∀ t ∈ Icc (0 : ℝ) P,
            Y Z t ∈ ball 0 L) ∧
          (∀ Z ∈ ball (littleCircularReference hγ hγ1) δ, ∀ t ∈ Icc (0 : ℝ) P, ∀ i θ,
            HasDerivAt (fun s => LittleContourSpace.lift γ (Y Z s i) θ)
              (contourBoundaryField circularContourStrengths
                (fun j => LittleContourSpace.lift γ (Y Z t j)) i θ +
                (A * R)⁻¹ • actualTorusCorrectionVelocity (S.physicalComplexSource w (t / A))
                  (R • LittleContourSpace.lift γ (Y Z t i) θ)) t) ∧
          ∀ {ρ : ℝ} {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ},
            IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
              (ball (littleCircularReference hγ hγ1) ρ) P X →
            ∀ Z ∈ ball (littleCircularReference hγ hγ1) (min ρ δ), ∀ t ∈ Icc (0 : ℝ) P,
              dist (Y Z t) (X Z t) ≤
                (C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
                  (∫ x in torusBox, |f x|) / A) * t * Real.exp ((K : ℝ) * t) := by
  obtain ⟨L, hL, K, r, hr, hperiod⟩ := exists_circular_forced_interval_comparison_constants hγ hγ1 hP
  have hp : 0 < P := hP
  obtain ⟨δ, hδ, η, hη, hsmall₀, hsmall⟩ := exists_uniform_forced_flow_smallness hr hp K
  obtain ⟨C, hC, Kphys, hfields⟩ := exists_uniform_normalized_actualTorusCorrection_fields hM hγ1.le hL
  refine ⟨L, hL, K, δ, hδ, η, hη, C, hC, Kphys, ?_⟩
  intro f T S hS w hwf hwper hwrot hmean hmass ε a hε hεT ha ha16 hsupp
  obtain ⟨E, hE⟩ := hfields S hS hwf hwper hwrot hmean hmass hε hεT ha ha16 hsupp
  refine ⟨E, ?_⟩
  intro R A hR hA hwindow htarget hscale hKA hBη
  obtain ⟨hQLip, hQc, hQlift, hQbound⟩ := hE hR hA hp hwindow htarget hscale
  let J : ℝ≥0 := ⟨(Kphys : ℝ) / A, div_nonneg Kphys.coe_nonneg hA.le⟩
  have hJ : (J : ℝ) ≤ 1 := (div_le_one hA).mpr hKA
  let q : ℝ → (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ :=
    fun t Z i => rescaledBanachForcing E A R t (Z i)
  let B : ℝ := C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
    (∫ x in torusBox, |f x|) / A
  have hcomponent {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ ball 0 L) (i : Fin 2) :
      Z i ∈ ball 0 L :=
    mem_ball_zero_iff.mpr ((norm_le_pi_norm Z i).trans_lt (mem_ball_zero_iff.mp hZ))
  have hBL : 0 ≤ B := (norm_nonneg (rescaledBanachForcing E A R 0 0)).trans
    (hQbound 0 ⟨le_rfl, hp.le⟩ 0 (mem_ball_self hL))
  have hqLip (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) P) :
      LipschitzOnWith J (q t) (ball 0 L) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro Z hZ W hW
    apply (dist_pi_le_iff (mul_nonneg J.2 dist_nonneg)).mpr
    intro i
    exact ((hQLip t).dist_le_mul (Z i) (hcomponent hZ i) (W i) (hcomponent hW i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist Z W i) J.2)
  have hqc (Z : Fin 2 → LittleContourSpace γ) (hZ : Z ∈ ball 0 L) :
      ContinuousOn (fun t => q t Z) (Icc (0 : ℝ) P) :=
    (continuous_pi_iff.mpr (fun i => hQc (Z i) (hcomponent hZ i))).continuousOn
  have hqbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) P)
      (Z : Fin 2 → LittleContourSpace γ) (hZ : Z ∈ ball 0 L) : ‖q t Z‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hBL).mpr
    intro i
    exact hQbound t ht (Z i) (hcomponent hZ i)
  obtain ⟨Y, hY, hYL, hYd, hcompare⟩ :=
    hperiod J hδ hBL hsmall₀ (hsmall J hJ B ⟨hBL, hBη⟩) q hqLip hqc hqbound
  refine ⟨Y, hY, hYL, ?_, hcompare⟩
  intro Z hZ t ht i θ
  have hh := hYd Z hZ t ht i θ
  rw [show LittleContourSpace.lift γ (q t (Y Z t) i) θ = _ from
    hQlift t ht (Y Z t i) (hcomponent (hYL Z hZ t ht) i) θ] at hh
  exact hh

end Euler2D

end


