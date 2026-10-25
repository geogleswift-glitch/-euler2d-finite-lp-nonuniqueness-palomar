module

public import RequestProject.Euler.CircularFiniteInnerStageConfinement

/-! The starting radius of the actual inner labels follows from the
original circular and ancient datum, including the final ancient label. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finitePlanarLabel_eq_zero_of_radius {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (N j : ℕ) {x : R2}
    (hx : (5 / 4) * radScale R ρ j < ‖x‖) :
    P.finitePlanarLabel s A₀ b R ρ N j x = 0 := by
  have hr : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hscale : (5 / 4 : ℝ) < ‖(radScale R ρ j)⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    exact (lt_inv_mul_iff₀ hr).mpr (by simpa only [mul_comm] using hx)
  by_cases hj : j = N
  · subst j
    have hz : circularPhasePatchPlanarVorticity (P.ancient s)
        ((radScale R ρ N)⁻¹ • x) = 0 := by
      by_contra hn
      exact (not_le.mpr hscale)
        (norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1 (P.ancient_domain s hs) hn)
    simp only [finitePlanarLabel, ite_true, finiteBaseDensity, hz, mul_zero]
  · have hz := cellW_eq_zero_of_one_le_norm (by linarith : 1 ≤ ‖(radScale R ρ j)⁻¹ • x‖)
    simp only [finitePlanarLabel, if_neg hj, datumTerm, hz, mul_zero]

theorem norm_sub_center_le_of_finiteInnerActiveInitialLabels
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ) {y : R2}
    (hy : y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k) :
    ‖y - torusCenter‖ ≤ (5 / 4) * ρ * radScale R ρ k := by
  obtain ⟨hybox, j, hj, hne⟩ := hy
  have hper : P.finitePeriodicLabel s A₀ b R ρ N j y =
      P.finitePlanarLabel s A₀ b R ρ N j (y - torusCenter) :=
    periodicCenteredSource_eq_on_box
      (P.finitePlanarLabel_zero_of_one_le_norm hs hR hRmax hρ hρ1 N j) hybox
  have hyn : ‖y - torusCenter‖ ≤ (5 / 4) * radScale R ρ j := by
    apply le_of_not_gt
    intro hn
    exact hne (hper.trans (P.finitePlanarLabel_eq_zero_of_radius hs hR hρ N j hn))
  have hjk : k + 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have hpow : ρ ^ j ≤ ρ ^ (k + 1) := pow_le_pow_of_le_one hρ.le hρ1 hjk
  calc
    _ ≤ (5 / 4) * radScale R ρ j := hyn
    _ ≤ (5 / 4) * radScale R ρ (k + 1) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hR.le) (by norm_num)
    _ = _ := by simp only [radScale, pow_succ]; ring

theorem finiteInnerActiveInitial_forward_zero_radius
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) :
    ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
      ‖S.forward 0 y - torusCenter‖ ≤ (5 / 4) * ρ * radScale R ρ k := by
  intro y hy
  rw [S.initial]
  exact P.norm_sub_center_le_of_finiteInnerActiveInitialLabels hs hR hRmax hρ hρ1 N k hy

end CircularMaterialTransferProfile
end Euler2D

end
