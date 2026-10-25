module

public import RequestProject.Euler.ScaledRadialSobolev
public import RequestProject.Euler.W1pArithmetic
public import RequestProject.Euler.LocalizedScale

/-!
# Sobolev regularity of the actual infinite physical datum

Each physical circular block has a localized first-derivative bound of
order `A_j * r_j^(2/q)`. The paper's original geometric condition
`ρ^(2/q) < b` therefore controls all finite physical sums uniformly,
and their strong `L²` limit retains the full distributional Sobolev bound.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

noncomputable section

namespace Euler2D

/-- The explicit geometric bound for the actual velocity datum and each
of its four scalar distributional derivatives. -/
def velocityDatumSobolevBound (A₀ b R ρ q : ℝ) : ℝ :=
  (7 * Real.pi ^ (1 / q)) * (A₀ * R ^ (2 / q)) / (1 - ρ ^ (2 / q) / b)

lemma velocityDatumTerm_sobolev_scale_bound {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (j : ℕ) :
    torusLocalizedSobolevBound (ENNReal.ofReal q) (7 * |ampScale A₀ b j|)
        (closedBall torusCenter (radScale R ρ j)) ≤
      (7 * Real.pi ^ (1 / q)) *
        (ampScale A₀ b j * radScale R ρ j ^ (2 / q)) := by
  have hAj : 0 ≤ ampScale A₀ b j := div_nonneg hA (pow_pos hb j).le
  have h := torusLocalizedSobolevBound_closedBall_le hq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) hAj) (radScale_pos hR hρ j).le torusCenter
  rw [abs_of_nonneg hAj]
  exact h.trans_eq (by ring)

lemma sum_velocityDatumTerm_sobolev_bound_le {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q)
    (hsmall : ρ ^ (2 / q) < b) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      torusLocalizedSobolevBound (ENNReal.ofReal q) (7 * |ampScale A₀ b j|)
        (closedBall torusCenter (radScale R ρ j))) ≤ velocityDatumSobolevBound A₀ b R ρ q := by
  let κ : ℝ := ρ ^ (2 / q) / b
  let C : ℝ := (7 * Real.pi ^ (1 / q)) * (A₀ * R ^ (2 / q))
  have hκ0 : 0 ≤ κ := div_nonneg (Real.rpow_nonneg hρ.le _) hb.le
  have hκ1 : κ < 1 := (div_lt_one hb).mpr hsmall
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hgeom := summable_geometric_of_lt_one hκ0 hκ1
  have hsum : ∑ j ∈ Finset.range N, κ ^ j ≤ (1 - κ)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hκ0 hκ1]
    exact hgeom.sum_le_tsum _ (fun j _ => pow_nonneg hκ0 j)
  calc
    (∑ j ∈ Finset.range N,
      torusLocalizedSobolevBound (ENNReal.ofReal q) (7 * |ampScale A₀ b j|)
        (closedBall torusCenter (radScale R ρ j))) ≤ ∑ j ∈ Finset.range N, C * κ ^ j := by
      apply Finset.sum_le_sum
      intro j _
      exact (velocityDatumTerm_sobolev_scale_bound hA hb hR hρ hq j).trans_eq (by
        rw [datum_scale_geometric hR.le hρ.le]
        dsimp only [C, κ]
        ring)
    _ = C * ∑ j ∈ Finset.range N, κ ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (1 - κ)⁻¹ := mul_le_mul_of_nonneg_left hsum hC
    _ = velocityDatumSobolevBound A₀ b R ρ q := by rfl

/-- Every actual finite circular velocity sum has one Sobolev bound
independent of the number of labels. -/
theorem w1pBoundedBy_velocityDatumPartialSumL2 {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 2 ≤ q)
    (hsmall : ρ ^ (2 / q) < b) (N : ℕ) :
    W1pBoundedBy (ENNReal.ofReal q) (velocityDatumSobolevBound A₀ b R ρ q)
      (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N) := by
  have hq0 : 0 < q := by linarith
  have hqE : (2 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa using (ENNReal.ofReal_le_ofReal hq)
  let M : ℕ → ℝ := fun j =>
    torusLocalizedSobolevBound (ENNReal.ofReal q) (7 * |ampScale A₀ b j|)
      (closedBall torusCenter (radScale R ρ j))
  have hM (j : ℕ) : 0 ≤ M j := ENNReal.toReal_nonneg
  have hterm (j : ℕ) : W1pBoundedBy (ENNReal.ofReal q) (M j)
      (velocityDatumTerm A₀ b R ρ j) :=
    (w1pBoundedBy_velocityDatumTermLp hqE hR hR1 hρ hρ1 j).congr_ae
      (coeFn_velocityDatumTermLp hR hρ 2 j)
  have hsum := w1pBoundedBy_sum_range ((by norm_num : (1 : ENNReal) ≤ 2).trans hqE)
    M (velocityDatumTerm A₀ b R ρ) hM hterm N
  have hbound := hsum.mono (sum_velocityDatumTerm_sobolev_bound_le hA hb hR hρ hq0 hsmall N)
  exact hbound.congr_ae (coeFn_velocityDatumPartialSumL2 hR hρ N).symm

/-- The actual physical infinite velocity datum belongs to `W¹,ᵠ`
under the original vorticity summability condition, with the explicit
geometric bound retained for its distributional derivatives. -/
theorem w1pBoundedBy_velocityDatumL2 {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 2 ≤ q) (hsmall : ρ ^ (2 / q) < b) :
    W1pBoundedBy (ENNReal.ofReal q) (velocityDatumSobolevBound A₀ b R ρ q)
      (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ) := by
  have hqE : (2 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa using (ENNReal.ofReal_le_ofReal hq)
  exact w1pBoundedBy_of_tendsto hqE
    (tendsto_velocityDatumPartialSumL2 hA hb hR hR1 hρ hρ1
      (velocity_two_small_of_vorticity_small hρ hρ1 (by linarith) hsmall))
    (w1pBoundedBy_velocityDatumPartialSumL2 hA hb hR hR1 hρ hρ1 hq hsmall)

theorem memW1p_velocityDatumL2 {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 2 ≤ q) (hsmall : ρ ^ (2 / q) < b) :
    MemW1p (ENNReal.ofReal q) (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ) :=
  (w1pBoundedBy_velocityDatumL2 hA hb hR hR1 hρ hρ1 hq hsmall).memW1p

end Euler2D

end
