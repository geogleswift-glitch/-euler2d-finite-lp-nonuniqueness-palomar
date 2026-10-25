module

public import RequestProject.Euler.CircularRetardedLabelDeviation
public import RequestProject.Euler.CircularFiniteOuterInteractionRow

/-! Both real interaction rows are instantiated with the actual
deviation of the same original retarded family. The common prefix
radius is never substituted for each label's weighted deviation. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_retardedInnerLabel_contourLittle_upperRow
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c δ e L : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k m j : ℕ) (l : Fin (N + 1)) (hl : (l : ℕ) ≤ k)
    (hjl : j ≤ (l : ℕ)) (hlm : (l : ℕ) ≤ m)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (Y : Fin (N + 1) → Fin 2 → LittleContourSpace γ) (u φ : Fin (N + 1) → ℝ)
    (hraw : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
      G.contours (j, i) = (radScale R ρ j • (exp (((φ j : ℝ) : ℂ) * I) • Y j i)).val)
    (hsmall : circularRetardedPrefixDeviation hγ hγ1 k Y u ≤ cellA / 4)
    (he : 0 < e) (hsep : 10 * radScale R ρ l ≤ e * radScale R ρ j)
    (W : LittleContourSpace η)
    (hW : ∀ x, e * radScale R ρ j ≤ ‖ContourC1Space.toBCF η W.val x‖)
    (hL : ‖W‖ ≤ radScale R ρ j * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t))
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / (ampScale A₀ b m * radScale R ρ j) ≤
        finiteInnerLabelLittleRowCoefficient (η : ℝ) e L * b ^ (m - (l : ℕ)) *
          ρ ^ (6 * ((l : ℕ) - j)) * ‖Y l - littleCircularMaterialContours hγ hγ1 (u l)‖ := by
  let G' := P.finiteOuterMaterialTubeOfRetardedFamily hR hρ G Y u φ hraw hsmall
  let Gl := P.finiteOuterMaterialTubeRestrict G' hl
  have hql := P.finiteRetardedTube_relative_label hR hρ G Y u φ hraw hsmall l hl
  exact P.exists_finiteInnerLabel_contourLittle_upperRow hη hs hA hb hR hRmax hρ hρ1
    N m j l hjl hlm S t ht Gl (norm_nonneg _) hql he hsep W hW hL

theorem exists_retardedOuterLabel_contourLittle_lowerRow
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c B δ L : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k m j : ℕ) (l : Fin (N + 1)) (hl : (l : ℕ) ≤ k)
    (hlj : (l : ℕ) ≤ j) (hlm : (l : ℕ) ≤ m)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (Y : Fin (N + 1) → Fin 2 → LittleContourSpace γ) (u φ : Fin (N + 1) → ℝ)
    (hraw : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
      G.contours (j, i) = (radScale R ρ j • (exp (((φ j : ℝ) : ℂ) * I) • Y j i)).val)
    (hsmall : circularRetardedPrefixDeviation hγ hγ1 k Y u ≤ cellA / 4)
    (hc : 0 < c) (hB : 0 < B)
    (hsep : 8 * (B * radScale R ρ j) ≤ c * radScale R ρ l)
    (W : LittleContourSpace η)
    (hW : ∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * radScale R ρ j)
    (hL : ‖W‖ ≤ radScale R ρ j * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N l S t)
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / (ampScale A₀ b m * radScale R ρ j) ≤
        finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L * b ^ (m - (l : ℕ)) *
          ρ ^ (2 * (j - (l : ℕ))) * ‖Y l - littleCircularMaterialContours hγ hγ1 (u l)‖ := by
  let G' := P.finiteOuterMaterialTubeOfRetardedFamily hR hρ G Y u φ hraw hsmall
  let Gl := P.finiteOuterMaterialTubeRestrict G' hl
  have hql := P.finiteRetardedTube_relative_label hR hρ G Y u φ hraw hsmall l hl
  exact P.exists_finiteOuterLabel_contourLittle_lowerRow hη hs hA hb hR hRmax hρ hρ1
    N m j l hlj hlm S t ht Gl hql hc hB hsep W hW hL

end CircularMaterialTransferProfile
end Euler2D

end
