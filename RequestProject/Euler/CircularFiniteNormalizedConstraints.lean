module

public import RequestProject.Euler.CircularFiniteMaterialArea
public import RequestProject.Euler.CircularRigidRotationGauge
public import RequestProject.Euler.CircularActualConstraintChart

/-! The actual normalized material interface has the original area
and fourfold constraints. Its literal original projection therefore
recovers it through the same constrained chart used by the return map. -/

@[expose] public section

set_option maxHeartbeats 5500000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal ComplexConjugate

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem littleContourArea_unit_complex_smul {γ : ℝ≥0} (a : ℂ) (ha : ‖a‖ = 1)
    (Z : LittleContourSpace γ) : littleContourArea γ (a • Z) = littleContourArea γ Z := by
  have hunit : conj a * a = 1 := by rw [Complex.conj_mul', ha]; simp
  have hder : deriv (fun θ => a * LittleContourSpace.lift γ Z θ) =
      fun θ => a * deriv (LittleContourSpace.lift γ Z) θ := by
    funext θ
    exact (((LittleContourSpace.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt).const_mul a).deriv
  change loopArea (fun θ => a * LittleContourSpace.lift γ Z θ) = loopArea (LittleContourSpace.lift γ Z)
  unfold loopArea
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  rw [hder]
  dsimp only
  rw [map_mul, show conj a * conj (LittleContourSpace.lift γ Z θ) *
      (a * deriv (LittleContourSpace.lift γ Z) θ) =
      (conj a * a) * (conj (LittleContourSpace.lift γ Z θ) *
        deriv (LittleContourSpace.lift γ Z) θ) by ring, hunit, one_mul]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteOuterMaterialTube_normalized_constraints {s R ρ η : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (hη : 0 ≤ η) (hηa : η ≤ cellA / 4)
    (hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η)
    {N k : ℕ} {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T}
    {t c δ : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k) (φ : ℝ)
    (Y : Fin 2 → LittleContourSpace γ)
    (hraw : ∀ i, G.contours (j, i) =
      (radScale R ρ j • (exp ((φ : ℂ) * I) • Y i)).val) :
    (∀ i, Y i ∈ fourfoldLittleContourSubmodule γ) ∧
      ∀ i, littleContourArea γ (Y i) = Real.pi * circularContourRadii i ^ 2 := by
  have hr : 0 < radScale R ρ j := radScale_pos hR hρ j
  have he : ‖exp ((φ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I φ
  constructor
  · intro i
    apply (mem_fourfoldLittleContourSubmodule (Y i)).mpr
    intro θ
    have hh := G.fourfold j hj i θ
    rw [hraw i] at hh
    change (radScale R ρ j : ℂ) * (exp ((φ : ℂ) * I) * LittleContourSpace.lift γ (Y i) (θ + Real.pi / 2)) =
      I * ((radScale R ρ j : ℂ) * (exp ((φ : ℂ) * I) * LittleContourSpace.lift γ (Y i) θ)) at hh
    apply mul_left_cancel₀ (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _))
    calc
      _ = (radScale R ρ j : ℂ) * (exp ((φ : ℂ) * I) *
          LittleContourSpace.lift γ (Y i) (θ + Real.pi / 2)) := by ring
      _ = _ := hh
      _ = _ := by ring
  · intro i
    have hh := P.finiteOuterMaterialTube_area hs hR hρ hη hηa hancient ht G j hj i
    rw [hraw i] at hh
    change contourArea γ (radScale R ρ j • (exp ((φ : ℂ) * I) • Y i).val) = _ at hh
    rw [contourArea_real_smul] at hh
    change radScale R ρ j ^ 2 * littleContourArea γ (exp ((φ : ℂ) * I) • Y i) = _ at hh
    rw [littleContourArea_unit_complex_smul _ he] at hh
    apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
    calc
      _ = Real.pi * (circularContourRadii i * radScale R ρ j) ^ 2 := hh
      _ = _ := by ring

theorem exists_uniform_actualMaterial_constraintChart_radius :
    ∃ ε > 0, ∀ {s R ρ η : ℝ}, s ≤ 0 → ∀ (hR : 0 < R) (hρ : 0 < ρ),
      0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ {N k : ℕ} {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T}
        {t c δ : ℝ}, t ∈ Icc (0 : ℝ) T →
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ (j : Fin (N + 1)), (j : ℕ) ≤ k → ∀ (φ : ℝ) (Y : Fin 2 → LittleContourSpace γ),
      (∀ i, G.contours (j, i) = (radScale R ρ j • (exp ((φ : ℂ) * I) • Y i)).val) →
      Y ∈ ball (littleCircularReference hγ hγ1) ε →
      circularConstrainedChart hγ hγ1
        (circularConstraintProjectionToTangentCLM hγ hγ1.le (Y - littleCircularReference hγ hγ1)) = Y := by
  obtain ⟨ε, hε, hchart⟩ := exists_circular_actualConstraintChart_radius hγ hγ1
  refine ⟨ε, hε, ?_⟩
  intro s R ρ η hs hR hρ hη hηa hancient N k f T S t c δ ht G j hj φ Y hraw hY
  obtain ⟨hfour, harea⟩ := P.finiteOuterMaterialTube_normalized_constraints
    hs hR hρ hη hηa hancient ht G j hj φ Y hraw
  exact hchart Y hY hfour harea

end CircularMaterialTransferProfile
end Euler2D

end
