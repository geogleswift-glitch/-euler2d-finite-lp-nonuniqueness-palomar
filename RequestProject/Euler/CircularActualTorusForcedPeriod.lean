module

public import RequestProject.Euler.CircularForcedPeriodComparison
public import RequestProject.Euler.NormalizedActualTorusContourForcing

/-! A genuine full-period circular contour map driven by the same actual
torus Euler source. Both the forcing and the flow are constructed. The
quantitative smallness tests are explicit; their eventual scale selection
and the identification with the source particle labels remain separate. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) actualPeriodLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) actualPeriodLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_circular_actualTorus_forced_period_constants {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ L > 0, ∃ K : ℝ≥0, ∃ r > 0,
      ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {w : R2 → ℝ}, w =ᵐ[μT] (f : R2 → ℝ) → IsTorusPeriodic w →
      (∀ x, w (torusQuarterTurn x) = w x) → (∫ x in torusBox, f x) = 0 →
      ∀ {ε a R A : ℝ}, 0 < ε → ε ≤ T → 0 < a → a ≤ 1 / 16 →
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
        a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) →
      0 < R → 0 < A → period / A ≤ ε → R * L < a / 4 → (L + 1) * R ≤ a / 2 →
      ∃ C > 0, ∃ J : ℝ≥0,
      ∃ q : ℝ → (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ,
        (∀ t ∈ Icc (0 : ℝ) period, ∀ Z ∈ ball (0 : Fin 2 → LittleContourSpace γ) L, ∀ i θ,
          LittleContourSpace.lift γ (q t Z i) θ = (A * R)⁻¹ •
            actualTorusCorrectionVelocity (S.physicalComplexSource w (t / A))
              (R • LittleContourSpace.lift γ (Z i) θ)) ∧
        ∀ {δ : ℝ}, 0 < δ → δ * Real.exp (2 * (K : ℝ) * period) < r →
          (δ + (C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
            (∫ x in torusBox, |f x|) / A) * period) *
              Real.exp (2 * ((K : ℝ) + J) * period) < r →
          ∃ Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
            IsNonautonomousBanachFlowOn (fun t Z => circularBanachField hγ hγ1 Z + q t Z)
              (circularBanachDomain hγ hγ1)
              (ball (littleCircularReference hγ hγ1) δ) period Y ∧
            (∀ Z ∈ ball (littleCircularReference hγ hγ1) δ, ∀ t ∈ Icc (0 : ℝ) period,
              Y Z t ∈ ball 0 L) ∧
            (∀ Z ∈ ball (littleCircularReference hγ hγ1) δ, ∀ t ∈ Icc (0 : ℝ) period, ∀ i θ,
              HasDerivAt (fun s => LittleContourSpace.lift γ (Y Z s i) θ)
                (contourBoundaryField circularContourStrengths
                  (fun j => LittleContourSpace.lift γ (Y Z t j)) i θ +
                  (A * R)⁻¹ • actualTorusCorrectionVelocity (S.physicalComplexSource w (t / A))
                    (R • LittleContourSpace.lift γ (Y Z t i) θ)) t) ∧
            ∀ {ρ : ℝ} {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ},
              IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
                (ball (littleCircularReference hγ hγ1) ρ) period X →
              ∀ Z ∈ ball (littleCircularReference hγ hγ1) (min ρ δ),
                ∀ t ∈ Icc (0 : ℝ) period,
                  dist (Y Z t) (X Z t) ≤
                    (C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
                      (∫ x in torusBox, |f x|) / A) * t * Real.exp ((K : ℝ) * t) := by
  obtain ⟨L, hL, K, r, hr, hperiod⟩ := exists_circular_forced_period_comparison_constants hγ hγ1
  refine ⟨L, hL, K, r, hr, ?_⟩
  intro f T S hS w hwf hwper hwrot hmean ε a R A hε hεT ha ha16 hs hR hA hwindow htarget hscale
  have hp : 0 < period := by unfold period; positivity
  obtain ⟨C, hC, J, Q, hQLip, hQc, hQlift, hQbound⟩ :=
    S.exists_normalized_actualTorusCorrection_LittleField hS hwf hwper hwrot hmean
      hε hεT ha ha16 hs hR hA hL hp hwindow htarget hscale hγ1.le
  let q : ℝ → (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ :=
    fun t Z i => Q t (Z i)
  let B : ℝ := C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
    (∫ x in torusBox, |f x|) / A
  have hcomponent {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ ball 0 L) (i : Fin 2) :
      Z i ∈ ball 0 L :=
    mem_ball_zero_iff.mpr ((norm_le_pi_norm Z i).trans_lt (mem_ball_zero_iff.mp hZ))
  have hBL : 0 ≤ B := (norm_nonneg (Q 0 0)).trans
    (hQbound 0 ⟨le_rfl, hp.le⟩ 0 (mem_ball_self hL))
  have hqLip (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) period) :
      LipschitzOnWith J (q t) (ball 0 L) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro Z hZ W hW
    apply (dist_pi_le_iff (mul_nonneg J.2 dist_nonneg)).mpr
    intro i
    exact ((hQLip t).dist_le_mul (Z i) (hcomponent hZ i) (W i) (hcomponent hW i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist Z W i) J.2)
  have hqc (Z : Fin 2 → LittleContourSpace γ) (hZ : Z ∈ ball 0 L) :
      ContinuousOn (fun t => q t Z) (Icc (0 : ℝ) period) :=
    (continuous_pi_iff.mpr (fun i => hQc (Z i) (hcomponent hZ i))).continuousOn
  have hqbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) period)
      (Z : Fin 2 → LittleContourSpace γ) (hZ : Z ∈ ball 0 L) : ‖q t Z‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hBL).mpr
    intro i
    exact hQbound t ht (Z i) (hcomponent hZ i)
  have hqlift (t : ℝ) (ht : t ∈ Icc (0 : ℝ) period)
      (Z : Fin 2 → LittleContourSpace γ) (hZ : Z ∈ ball 0 L) (i : Fin 2) (θ : ℝ) :
      LittleContourSpace.lift γ (q t Z i) θ = (A * R)⁻¹ •
        actualTorusCorrectionVelocity (S.physicalComplexSource w (t / A))
          (R • LittleContourSpace.lift γ (Z i) θ) :=
    hQlift t ht (Z i) (hcomponent hZ i) θ
  refine ⟨C, hC, J, q, hqlift, ?_⟩
  intro δ hδ hsmall₀ hsmall
  obtain ⟨Y, hY, hYL, hYd, hcompare⟩ :=
    hperiod J hδ hBL hsmall₀ hsmall q hqLip hqc hqbound
  refine ⟨Y, hY, hYL, ?_, hcompare⟩
  intro Z hZ t ht i θ
  have hh := hYd Z hZ t ht i θ
  rw [hqlift t ht (Y Z t) (hYL Z hZ t ht) i θ] at hh
  exact hh

end Euler2D

end
