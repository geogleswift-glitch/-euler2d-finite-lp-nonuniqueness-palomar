module

public import RequestProject.Euler.UniformActualTorusForcingField
public import RequestProject.Euler.RescaledBanachForcing

/-! The actual normalization preserves both required uniformities:
the cubic budget constant precedes all shrinking source radii, and the
physical target Lipschitz constant precedes all source systems and all
spatial and temporal normalization scales. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) uniformNormalizedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) uniformNormalizedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_uniform_normalized_actualTorusCorrection_fields
    {M : ℝ} (hM : 0 ≤ M) {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {L : ℝ} (hL : 0 < L) :
    ∃ C > 0, ∃ K : ℝ≥0,
      ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {w : R2 → ℝ}, w =ᵐ[μT] (f : R2 → ℝ) → IsTorusPeriodic w →
      (∀ x, w (torusQuarterTurn x) = w x) → (∫ x in torusBox, f x) = 0 →
      (∫ x in torusBox, |f x|) ≤ M →
      ∀ {ε a : ℝ}, 0 < ε → ε ≤ T → 0 < a → a ≤ 1 / 16 →
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
        a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) →
      ∃ E : ℝ → LittleContourSpace γ → LittleContourSpace γ,
      ∀ {R A P : ℝ} (_hR : 0 < R) (hA : 0 < A), 0 < P → P / A ≤ ε →
        R * L < a / 4 → (L + 1) * R ≤ a / 2 →
        (∀ t, LipschitzOnWith (⟨(K : ℝ) / A, div_nonneg K.coe_nonneg hA.le⟩ : ℝ≥0)
          (rescaledBanachForcing E A R t) (ball 0 L)) ∧
        (∀ Z ∈ ball (0 : LittleContourSpace γ) L,
          Continuous (fun t => rescaledBanachForcing E A R t Z)) ∧
        (∀ t ∈ Icc (0 : ℝ) P, ∀ Z ∈ ball (0 : LittleContourSpace γ) L, ∀ θ,
          LittleContourSpace.lift γ (rescaledBanachForcing E A R t Z) θ = (A * R)⁻¹ •
            actualTorusCorrectionVelocity (S.physicalComplexSource w (t / A))
              (R • LittleContourSpace.lift γ Z θ)) ∧
        ∀ t ∈ Icc (0 : ℝ) P, ∀ Z ∈ ball (0 : LittleContourSpace γ) L,
          ‖rescaledBanachForcing E A R t Z‖ ≤
            C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
              (∫ x in torusBox, |f x|) / A := by
  letI : NormSMulClass ℝ (LittleContourSpace γ) :=
    @NormedSpace.toNormSMulClass ℝ (LittleContourSpace γ) _ _
      (uniformNormalizedLittle_space γ)
  obtain ⟨C, hC, hbudget⟩ := exists_uniform_actualTorusCorrection_contourLittle_budget
  obtain ⟨K, hfields⟩ := exists_uniform_clamped_actualTorusCorrection_LittleFields hM hγ1
  refine ⟨C, hC, K, ?_⟩
  intro f T S hS w hwf hwper hwrot hmean hmass ε a hε hεT ha ha16 hsupp
  obtain ⟨E, _, hLip, hc, hE⟩ :=
    hfields S hS hwf hwper hwrot hmean hmass hε hεT ha ha16 hsupp
  refine ⟨E, ?_⟩
  intro R A P hR hA hP hwindow htarget hscale
  have htarget₀ : R * L < (1 / 16 : ℝ) / 4 := htarget.trans_le (by linarith)
  have hnorm (Z : LittleContourSpace γ) : ‖R • Z‖ = R * ‖Z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hZphys (Z : LittleContourSpace γ) (hZ : Z ∈ ball 0 L) :
      ‖R • Z‖ < (1 / 16 : ℝ) / 4 := by
    rw [hnorm]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hZ) hR).trans htarget₀
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) P) : t / A ∈ Icc (0 : ℝ) ε :=
    ⟨div_nonneg ht.1 hA.le, (div_le_div_of_nonneg_right ht.2 hA.le).trans hwindow⟩
  refine ⟨fun t => lipschitzOnWith_rescaledBanachForcing E hA hR htarget₀ t (hLip _),
    fun Z hZ => continuous_rescaledBanachForcing E hA hR htarget₀ hc hZ, ?_, ?_⟩
  · intro t ht Z hZ θ
    have hh := hE (t / A) (htime t ht) (R • Z) (hZphys Z hZ) θ
    change (A * R)⁻¹ • LittleContourSpace.lift γ (E (t / A) (R • Z)) θ = _
    rw [hh]
    rfl
  · intro t ht Z hZ
    have htT : t / A ∈ Icc (0 : ℝ) T := ⟨(htime t ht).1, (htime t ht).2.trans hεT⟩
    have hZnorm : ‖R • Z‖ ≤ L * R := by
      rw [hnorm]
      exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hZ).le hR.le).trans_eq (mul_comm _ _)
    have hh := hbudget ha ha16 hγ1 (S.physicalComplexSource w (t / A))
      (S.integrable_physicalComplexSource hwf _) (S.physicalComplexSource_support (hsupp _ (htime t ht)))
      ((S.integral_physicalComplexSource hwf _).trans hmean)
      (S.physicalComplexSource_fourfold hS hwper hwrot (by linarith) htT (hsupp _ (htime t ht)))
      hR hL.le hscale (R • Z) hZnorm (E (t / A) (R • Z))
      (hE (t / A) (htime t ht) (R • Z) (hZphys Z hZ))
    have hfac : 0 ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 := by
      unfold torusCorrectionContourBudget
      positivity
    have hm₄ := S.physicalComplexSource_fourthAbsoluteMoment_le_initialL1 hwf (hsupp _ (htime t ht))
    have hh' : ‖E (t / A) (R • Z)‖ / R ≤
        C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
          (∫ x in torusBox, |f x|) := by
      refine hh.trans ((mul_le_mul_of_nonneg_left hm₄ hfac).trans_eq ?_)
      ring
    have hrescaled : ‖rescaledBanachForcing E A R t Z‖ =
        ‖E (t / A) (R • Z)‖ / R / A :=
      norm_rescaledBanachForcing E hA hR t Z
    exact hrescaled.trans_le (div_le_div_of_nonneg_right hh' hA.le)

end Euler2D

end
