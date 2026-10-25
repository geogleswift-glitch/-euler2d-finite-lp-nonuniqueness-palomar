module

public import RequestProject.Euler.TorusClampedContourForcing
public import RequestProject.Euler.TorusPhysicalSourceMass

/-! The same actual Euler source gives a normalized contour forcing.
The original spatial and temporal rescaling is retained explicitly,
and the sharp estimate uses the conserved initial physical L1 mass. -/

@[expose] public section

set_option maxHeartbeats 2600000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) normalizedActualLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) normalizedActualLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_normalized_actualTorusCorrection_LittleField
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (hmean : (∫ x in torusBox, f x) = 0)
    {ε a R A L P : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0)
    (hR : 0 < R) (hA : 0 < A) (hL : 0 < L) (hP : 0 < P) (hwindow : P / A ≤ ε)
    (htarget : R * L < a / 4) (hscale : (L + 1) * R ≤ a / 2)
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) :
    ∃ C > 0, ∃ K : ℝ≥0, ∃ q : ℝ → LittleContourSpace γ → LittleContourSpace γ,
      (∀ t, LipschitzOnWith K (q t) (ball 0 L)) ∧
      (∀ Z ∈ ball (0 : LittleContourSpace γ) L, Continuous (fun t => q t Z)) ∧
      (∀ t ∈ Icc (0 : ℝ) P, ∀ Z ∈ ball (0 : LittleContourSpace γ) L, ∀ θ,
        LittleContourSpace.lift γ (q t Z) θ = (A * R)⁻¹ •
          actualTorusCorrectionVelocity (S.physicalComplexSource w (t / A))
            (R • LittleContourSpace.lift γ Z θ)) ∧
      ∀ t ∈ Icc (0 : ℝ) P, ∀ Z ∈ ball (0 : LittleContourSpace γ) L,
        ‖q t Z‖ ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 * a ^ 4 *
          (∫ x in torusBox, |f x|) / A := by
  obtain ⟨K₀, E, _, hLip, hc, hE⟩ :=
    S.exists_clamped_actualTorusCorrection_LittleField hS hwf hwper hwrot hmean
      hε hεT ha ha16 hsupp hγ1
  obtain ⟨C, hC, hbudget⟩ := S.exists_physicalComplexSource_contourLittle_initialL1_budget ha ha16
  let q : ℝ → LittleContourSpace γ → LittleContourSpace γ :=
    fun t Z => (A * R)⁻¹ • E (t / A) (R • Z)
  let K : ℝ≥0 := NNReal.mk ((K₀ : ℝ) / A) (div_nonneg K₀.coe_nonneg hA.le)
  have hnorm (Z : LittleContourSpace γ) : ‖R • Z‖ = R * ‖Z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hZphys (Z : LittleContourSpace γ) (hZ : Z ∈ ball 0 L) : R • Z ∈ ball 0 (a / 4) := by
    apply mem_ball_zero_iff.mpr
    rw [hnorm]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hZ) hR).trans htarget
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) P) : t / A ∈ Icc (0 : ℝ) ε :=
    ⟨div_nonneg ht.1 hA.le, (div_le_div_of_nonneg_right ht.2 hA.le).trans hwindow⟩
  have hqnorm (t : ℝ) (Z : LittleContourSpace γ) :
      ‖q t Z‖ = ‖E (t / A) (R • Z)‖ / R / A := by
    dsimp only [q]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hA.le hR.le))]
    field_simp
  refine ⟨C, hC, K, q, ?_, ?_, ?_, ?_⟩
  · intro t
    apply LipschitzOnWith.of_dist_le_mul
    intro Z hZ W hW
    have hh := (hLip (t / A)).dist_le_mul (R • Z) (hZphys Z hZ) (R • W) (hZphys W hW)
    have hd : dist (R • Z) (R • W) = R * dist Z W := by
      rw [dist_eq_norm, ← smul_sub, hnorm, dist_eq_norm]
    have hqd : dist (q t Z) (q t W) =
        (A * R)⁻¹ * dist (E (t / A) (R • Z)) (E (t / A) (R • W)) := by
      dsimp only [q]
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hA.le hR.le)), dist_eq_norm]
    rw [hqd]
    rw [hd] at hh
    calc
      _ ≤ (A * R)⁻¹ * ((K₀ : ℝ) * (R * dist Z W)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (K : ℝ) * dist Z W := by
        change _ = ((K₀ : ℝ) / A) * dist Z W
        field_simp
        <;> ring
  · intro Z hZ
    exact continuous_const.smul ((hc (R • Z) (hZphys Z hZ)).comp (continuous_id.div_const A))
  · intro t ht Z hZ θ
    have hh := hE (t / A) (htime t ht) (R • Z)
      (mem_ball_zero_iff.mp (hZphys Z hZ)) θ
    change (A * R)⁻¹ • LittleContourSpace.lift γ (E (t / A) (R • Z)) θ = _
    rw [hh]
    rfl
  · intro t ht Z hZ
    have htT : t / A ∈ Icc (0 : ℝ) T := ⟨(htime t ht).1, (htime t ht).2.trans hεT⟩
    have hh := hbudget hγ1 hS w hwf hwper hwrot hmean (t / A) htT (hsupp _ (htime t ht))
      hR hL.le hscale (R • Z)
      (by rw [hnorm]; exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hZ).le hR.le).trans_eq (mul_comm _ _))
      (E (t / A) (R • Z))
      (hE (t / A) (htime t ht) (R • Z) (mem_ball_zero_iff.mp (hZphys Z hZ)))
    rw [hqnorm]
    exact div_le_div_of_nonneg_right hh hA.le

end BoundedEulerParticleSystem

end Euler2D

end
