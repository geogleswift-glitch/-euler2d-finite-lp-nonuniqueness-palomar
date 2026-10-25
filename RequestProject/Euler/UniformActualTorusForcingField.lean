module

public import RequestProject.Euler.TorusClampedContourForcing
public import RequestProject.Euler.TorusPhysicalSourceMass
public import RequestProject.Euler.UniformActualTorusContourBudget

/-! One physical target Lipschitz constant is chosen before the actual
Euler system, source support radius, and truncation. Its construction uses
the fixed safe radius 1/16 and a common initial L1 mass bound. The sharper
small-source radius is retained for the separate cancellation budget. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_uniform_clamped_actualTorusCorrection_LittleFields
    {M : ℝ} (hM : 0 ≤ M) {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) :
    ∃ K : ℝ≥0, ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {w : R2 → ℝ}, w =ᵐ[μT] (f : R2 → ℝ) → IsTorusPeriodic w →
      (∀ x, w (torusQuarterTurn x) = w x) → (∫ x in torusBox, f x) = 0 →
      (∫ x in torusBox, |f x|) ≤ M →
      ∀ {ε a : ℝ} (hε : 0 < ε), ε ≤ T → 0 < a → a ≤ 1 / 16 →
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
        a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) →
      ∃ E : ℝ → LittleContourSpace γ → LittleContourSpace γ,
        (∀ t Z, ‖Z‖ < (1 / 16 : ℝ) / 4 → ∀ θ,
          LittleContourSpace.lift γ (E t Z) θ = actualTorusCorrectionVelocity
            (S.physicalComplexSource w (projIcc 0 ε hε.le t))
            (LittleContourSpace.lift γ Z θ)) ∧
        (∀ t, LipschitzOnWith K (E t) (ball 0 ((1 / 16 : ℝ) / 4))) ∧
        (∀ Z ∈ ball (0 : LittleContourSpace γ) ((1 / 16 : ℝ) / 4),
          Continuous (fun t => E t Z)) ∧
        ∀ t ∈ Icc (0 : ℝ) ε, ∀ Z, ‖Z‖ < (1 / 16 : ℝ) / 4 → ∀ θ,
          LittleContourSpace.lift γ (E t Z) θ =
            actualTorusCorrectionVelocity (S.physicalComplexSource w t)
              (LittleContourSpace.lift γ Z θ) := by
  have ha₀ : (0 : ℝ) < 1 / 16 := by norm_num
  let M₄ : ℝ := (1 / 16 : ℝ) ^ 4 * M
  have hM₄ : 0 ≤ M₄ := mul_nonneg (by positivity) hM
  obtain ⟨K, hfield⟩ := exists_actualTorusCorrection_LittleField ha₀ le_rfl hM₄ hγ1
  refine ⟨K, ?_⟩
  intro f T S hS w hwf hwper hwrot hmean hmass ε a hε hεT ha ha16 hsupp
  let τ : ℝ → ℝ := fun t => projIcc 0 ε hε.le t
  have hτ : Continuous τ := continuous_subtype_val.comp continuous_projIcc
  have hτmem (t : ℝ) : τ t ∈ Icc (0 : ℝ) ε := (projIcc 0 ε hε.le t).property
  have hτT (t : ℝ) : τ t ∈ Icc (0 : ℝ) T := ⟨(hτmem t).1, (hτmem t).2.trans hεT⟩
  have hs₀ (t : ℝ) : ∀ x ∈ torusBox, (1 / 16 : ℝ) < ‖x - torusCenter‖ →
      S.transportedScalar w (τ t) x = 0 :=
    fun x hx hh => hsupp _ (hτmem t) x hx (ha16.trans_lt hh)
  let v : ℝ → ℂ → ℝ := fun t => S.physicalComplexSource w (τ t)
  have hv (t : ℝ) : Integrable (v t) := S.integrable_physicalComplexSource hwf _
  have hvs (t : ℝ) : ∀ z, (1 / 16 : ℝ) < ‖z‖ → v t z = 0 :=
    S.physicalComplexSource_support (hs₀ t)
  have hvm (t : ℝ) : (∫ z, v t z) = 0 :=
    (S.integral_physicalComplexSource hwf _).trans hmean
  have hvy (t : ℝ) : ∀ z, v t (I * z) = v t z :=
    S.physicalComplexSource_fourfold hS hwper hwrot (by norm_num) (hτT t) (hs₀ t)
  have hvM (t : ℝ) : (∫ z : ℂ, ‖z‖ ^ 4 * |v t z|) ≤ M₄ :=
    (S.physicalComplexSource_fourthAbsoluteMoment_le_initialL1 hwf (hs₀ t)).trans
      (mul_le_mul_of_nonneg_left hmass (by positivity))
  choose E hE hLip using fun t => hfield (v t) (hv t) (hvs t) (hvm t) (hvy t) (hvM t)
  refine ⟨E, hE, hLip, ?_, ?_⟩
  · intro Z hZ
    have hZn : ‖Z‖ < (1 / 16 : ℝ) / 4 := mem_ball_zero_iff.mp hZ
    apply continuous_iff_continuousAt.mpr
    intro s
    apply tendsto_actualTorusCorrection_of_L1 ha₀ le_rfl hγ1 hv (hv s) hvs (hvs s)
      hvm (hvm s) hvy (hvy s) (by norm_num : (0 : ℝ) < (1 / 16 : ℝ) / 4)
      (show (0 : ℝ) ≤ 1 by norm_num) (by norm_num : ((1 : ℝ) + 1) * ((1 / 16 : ℝ) / 4) ≤ (1 / 16 : ℝ) / 2)
      Z (by simpa only [one_mul] using hZn.le) (fun t => hE t Z hZn) (hE s Z hZn)
    exact S.tendsto_physicalComplexSource_L1 hwf (hτ.tendsto s)
  · intro t ht Z hZ θ
    have hh := hE t Z hZ θ
    simpa only [v, τ, projIcc_of_mem hε.le ht] using hh

end Euler2D

end
