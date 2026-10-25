module

public import RequestProject.Euler.CircularFiniteAncestorGeometricForcing
public import RequestProject.Euler.CircularRetardedTubeAlignment
public import RequestProject.Euler.CircularAncientFiniteInitialFamily

/-! The norm of the actual finite ancestor response supplies the
relative radii of its real material tubes, after an exact geometric
parameter shift. The following-layer ancestor forcing uses only that
ancestor prefix; the departing current layer is not required to belong
to the response tube. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def circularRetardedPrefixDeviation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {N : ℕ} (k : ℕ) (Y : Fin (N + 1) → Fin 2 → LittleContourSpace γ)
    (u : Fin (N + 1) → ℝ) : ℝ :=
  ‖fun j : {j : Fin (N + 1) // (j : ℕ) ≤ k} =>
    Y j - littleCircularMaterialContours hγ hγ1 (u j)‖

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteOuterMaterialTubeOfRetardedFamily {s R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T}
    {t c δ : ℝ} (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (Y : Fin (N + 1) → Fin 2 → LittleContourSpace γ) (u φ : Fin (N + 1) → ℝ)
    (hraw : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
      G.contours (j, i) =
        (radScale R ρ j • (exp (((φ j : ℝ) : ℂ) * I) • Y j i)).val)
    (hsmall : circularRetardedPrefixDeviation hγ hγ1 k Y u ≤ cellA / 4) :
    P.FiniteOuterMaterialTube s R ρ N k S t c
      (circularRetardedPrefixDeviation hγ hγ1 k Y u) := by
  let q := circularRetardedPrefixDeviation hγ hγ1 k Y u
  have hrelative (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k) (i : Fin 2) :
      ‖contourParameterShiftC1 (circularRetardedMaterialShift (φ j) (u j) i)
          (G.contours (j, i)) - finiteCircularReferenceC1 hγ hγ1 R ρ (j, i)‖ ≤
        radScale R ρ j * q := by
    rw [hraw j hj i]
    have hc := norm_le_pi_norm
      (contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift (φ j) (u j))
        (radScale R ρ j • (exp (((φ j : ℝ) : ℂ) * I) • Y j)) -
          radScale R ρ j • littleCircularReference hγ hγ1) i
    rw [norm_circularRetardedPhysicalAligned_sub_reference hγ hγ1
      (radScale_pos hR hρ j).le] at hc
    have hpi : ‖Y j - littleCircularMaterialContours hγ hγ1 (u j)‖ ≤ q :=
      norm_le_pi_norm
        (fun j : {j : Fin (N + 1) // (j : ℕ) ≤ k} =>
          Y j - littleCircularMaterialContours hγ hγ1 (u j)) ⟨j, hj⟩
    exact hc.trans (mul_le_mul_of_nonneg_left hpi (radScale_pos hR hρ j).le)
  exact {
    contours := G.contours
    reference := finiteCircularReferenceC1 hγ hγ1 R ρ
    shifts := fun p => circularRetardedMaterialShift (φ p.1) (u p.1) p.2
    reference_lift := fun j _ i => by
      rw [lift_finiteCircularReferenceC1]
      simp only [finiteCircularInterfaceRadius, mul_comm]
    quarter_tube := fun j hj i => (hrelative j hj i).trans (by
      have hi := (circularContourRadii_bounds i).2.1
      have hr := (radScale_pos hR hρ j).le
      change radScale R ρ j * q ≤ _
      have hh : q ≤ circularContourRadii i / 4 := hsmall.trans (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hh hr])
    relative_tube := hrelative
    core := G.core
    fourfold := G.fourfold
    initial_box := G.initial_box
    current_box := G.current_box
    images := G.images }

theorem exists_finiteAncestorResidual_contourLittle_of_prefix
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c B L δ : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmall : b * ρ ^ 2 < 1) (hδ : 0 ≤ δ)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (hc : 0 < c) (hB : 0 < B)
    (G : P.FiniteOuterMaterialTube s R ρ N (k - 1) S t c δ)
    (hsep : 8 * B * ρ ≤ c)
    (W : LittleContourSpace η)
    (hW : ∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * radScale R ρ k)
    (hL : ‖W‖ ≤ radScale R ρ k * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        ∑ j : Fin k, velocityC
          (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (finiteAncestorIndex hk j) S t)
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / (ampScale A₀ b k * radScale R ρ k) ≤
        (interiorContourNormBudget (η : ℝ) 1 c B L *
          (4 * Real.pi * circularRadialPerturbationWeight)) *
            (δ * (b * ρ ^ 2) / (1 - b * ρ ^ 2)) := by
  obtain ⟨Q, hQ, hn⟩ := P.exists_finiteAncestorResidual_contourLittle_weighted hη hs hA hb
    hR hRmax hρ hρ1 N k hk S t ht hc hB (fun _ => δ)
    (fun j => P.finiteOuterMaterialTubeRestrict G (by omega)) hsep W hW hL
  have hCint : 0 ≤ interiorContourNormBudget (η : ℝ) 1 c B L :=
    (interiorSpatialDerivativeBudget_nonneg (by norm_num : (0 : ℝ) ≤ 1) hB 0).trans (le_max_left _ _)
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  exact ⟨Q, hQ, hn.trans (mul_le_mul_of_nonneg_left
    (sum_weighted_ancestor_le_geometric (by positivity) hsmall hδ k (fun _ => δ) (fun _ => le_rfl))
    (by positivity))⟩

end CircularMaterialTransferProfile
end Euler2D

end
