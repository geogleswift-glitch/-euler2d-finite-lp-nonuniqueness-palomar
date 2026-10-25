module

public import RequestProject.Euler.CircularFiniteAncestorContourForcing

/-! The actual weighted ancestor Little forcing has the uniform
geometric-series bound when all material tubes have radius delta. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem sum_weighted_ancestor_le_geometric {κ δ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (hδ : 0 ≤ δ) (k : ℕ) (q : Fin k → ℝ) (hq : ∀ j, q j ≤ δ) :
    (∑ j : Fin k, κ ^ (k - (j : ℕ)) * q j) ≤ δ * κ / (1 - κ) := by
  have hrefl : (∑ j : Fin k, κ ^ (k - (j : ℕ))) = κ * ∑ n ∈ Finset.range k, κ ^ n := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => κ ^ (k - n)) k]
    calc
      _ = ∑ j ∈ Finset.range k, κ * κ ^ (k - 1 - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := Finset.mem_range.mp hj
        rw [show k - j = (k - 1 - j) + 1 by omega, pow_succ, mul_comm]
      _ = κ * ∑ j ∈ Finset.range k, κ ^ (k - 1 - j) := by rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_range_reflect (fun n => κ ^ n) k]
  have hgeom : (∑ n ∈ Finset.range k, κ ^ n) ≤ (1 - κ)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hκ hκ1]
    exact (summable_geometric_of_lt_one hκ hκ1).sum_le_tsum _ (fun n _ => pow_nonneg hκ n)
  calc
    _ ≤ ∑ j : Fin k, κ ^ (k - (j : ℕ)) * δ :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hq j) (pow_nonneg hκ _))
    _ = δ * (∑ j : Fin k, κ ^ (k - (j : ℕ))) := by rw [Finset.mul_sum]; congr 1; ext j; ring
    _ = δ * (κ * ∑ n ∈ Finset.range k, κ ^ n) := by rw [hrefl]
    _ ≤ δ * (κ * (1 - κ)⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeom hκ) hδ
    _ = _ := by ring

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteOuterMaterialTubeRestrict {s R ρ : ℝ} {N k l : ℕ}
    {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T} {t c δ : ℝ}
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ) (hl : l ≤ k) :
    P.FiniteOuterMaterialTube s R ρ N l S t c δ where
  contours := G.contours
  reference := G.reference
  shifts := G.shifts
  reference_lift := fun j hj => G.reference_lift j (hj.trans hl)
  quarter_tube := fun j hj => G.quarter_tube j (hj.trans hl)
  relative_tube := fun j hj => G.relative_tube j (hj.trans hl)
  core := G.core
  fourfold := fun j hj => G.fourfold j (hj.trans hl)
  initial_box := fun j hj => G.initial_box j (hj.trans hl)
  current_box := fun j hj => G.current_box j (hj.trans hl)
  images := fun j hj => G.images j (hj.trans hl)

theorem exists_finiteAncestorResidual_contourLittle_geometric
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c B L δ : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmall : b * ρ ^ 2 < 1) (hδ : 0 ≤ δ)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (hc : 0 < c) (hB : 0 < B)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
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
  obtain ⟨Q, hQ, hn⟩ := P.exists_finiteAncestorResidual_contourLittle_weighted hη hs hA hb hR hRmax hρ hρ1
    N k hk S t ht hc hB (fun _ => δ)
    (fun j => P.finiteOuterMaterialTubeRestrict G (Nat.le_of_lt j.isLt)) hsep W hW hL
  have hCint : 0 ≤ interiorContourNormBudget (η : ℝ) 1 c B L :=
    (interiorSpatialDerivativeBudget_nonneg (by norm_num : (0 : ℝ) ≤ 1) hB 0).trans (le_max_left _ _)
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  refine ⟨Q, hQ, hn.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (sum_weighted_ancestor_le_geometric (by positivity) hsmall hδ k (fun _ => δ) (fun _ => le_rfl))
    (by positivity)

end CircularMaterialTransferProfile
end Euler2D

end
