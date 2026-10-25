module

public import RequestProject.Euler.CircularReferenceUniformTube
public import RequestProject.Euler.BanachWeightedTrajectoryEnvelope

/-! The original circular field has one common Lipschitz domain for
the real slow ancestors and all their material reference phases. A
weighted bootstrap, at small rho, supplies membership automatically. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Set Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) weightedDomainLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) weightedDomainLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_circular_weighted_ancestor_lipschitz_domain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ U : Set (Fin 2 → LittleContourSpace γ), IsOpen U ∧ U ⊆ circularBanachDomain hγ hγ1 ∧
      ∃ K : ℝ≥0, 0 < K ∧ ∃ r > 0, ∃ L > 0,
        LipschitzOnWith K (circularBanachField hγ hγ1) U ∧
        (∀ Y ∈ U, ‖Y‖ ≤ L) ∧
        ∀ {h B : ℝ}, 0 < h → h ≤ 1 → 0 ≤ B → h * B ≤ r →
        ∀ (k : ℕ) (Y : ℕ → Fin 2 → LittleContourSpace γ) (u : ℕ → ℝ),
        weightedFamilyNorm h k (fun l => Y l - littleCircularMaterialContours hγ hγ1 (u l)) ≤ B →
        ∀ j : Fin k, Y j ∈ U ∧ littleCircularMaterialContours hγ hγ1 (u j) ∈ U := by
  obtain ⟨U, hU, hUD, _, K₀, r, hr, L, hL, hLip, htube, hnorm⟩ :=
    exists_circular_reference_uniform_lipschitz_tube hγ hγ1
  let K : ℝ≥0 := K₀ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hLip' : LipschitzOnWith K (circularBanachField hγ hγ1) U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (hLip.dist_le_mul x hx y hy).trans (mul_le_mul_of_nonneg_right
      (show (K₀ : ℝ) ≤ (K : ℝ) by dsimp only [K]; simp) dist_nonneg)
  refine ⟨U, hU, hUD, K, hK, r, hr, L, hL, hLip', hnorm, ?_⟩
  intro h B hh hh1 hB hBr k Y u hZ j
  have hpow : h ^ (k - (j : ℕ)) ≤ h := by
    simpa only [pow_one] using pow_le_pow_of_le_one hh.le hh1 (show 1 ≤ k - (j : ℕ) by omega)
  have hn : ‖Y j - littleCircularMaterialContours hγ hγ1 (u j)‖ ≤ r :=
    (norm_le_weightedFamilyNorm hh k (fun l => Y l - littleCircularMaterialContours hγ hγ1 (u l)) j).trans
      ((mul_le_mul_of_nonneg_left hZ (pow_pos hh _).le).trans
        ((mul_le_mul_of_nonneg_right hpow hB).trans hBr))
  exact ⟨htube (u j) (by simpa only [mem_closedBall, dist_eq_norm] using hn),
    htube (u j) (mem_closedBall_self hr.le)⟩

end Euler2D

end
