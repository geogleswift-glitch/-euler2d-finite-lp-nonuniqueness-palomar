module

public import RequestProject.Euler.CoupledPlanarBiotSavartAffine

/-! A genuinely bounded logarithmically continuous common field has
the epsilon-affine modulus required by material Osgood uniqueness. -/

@[expose] public section

noncomputable section

open Set Filter Topology

namespace Euler2D

theorem norm_commonLogField_sub_le_epsilon_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {v : E → F} {M C D ε : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖v x‖ ≤ M)
    (hlog : ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v x - v y‖ ≤ C * logFlowModulus ‖x - y‖)
    (hD : 0 ≤ D) (x y : E) (hxyD : ‖x - y‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖v x - v y‖ ≤ (4 * M + C) * ((1 - Real.log ε) * D + ε) := by
  have hK : 1 ≤ 1 - Real.log ε := by linarith [Real.log_nonpos hε.le hε1]
  have hbase : D ≤ (1 - Real.log ε) * D + ε := by nlinarith
  have hbase0 : 0 ≤ (1 - Real.log ε) * D + ε := hD.trans hbase
  by_cases hsmall : ‖x - y‖ ≤ 1 / 2
  · have hlocal := (hlog x y hsmall).trans
      (mul_le_mul_of_nonneg_left (logFlowModulus_le_epsilon_affine (norm_nonneg _) hε) hC)
    have hscale : (1 - Real.log ε) * ‖x - y‖ + ε ≤ (1 - Real.log ε) * D + ε :=
      add_le_add (mul_le_mul_of_nonneg_left hxyD (by linarith)) (le_refl _)
    exact (hlocal.trans (mul_le_mul_of_nonneg_left hscale hC)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hbase0)
  · have hlarge : 1 / 2 ≤ D := (not_le.mp hsmall).le.trans hxyD
    have hv : ‖v x - v y‖ ≤ 2 * M := by
      have hh := (norm_sub_le _ _).trans (add_le_add (hbound x) (hbound y))
      linarith
    have h1 := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 4 * M by positivity)
    have h2 := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 4 * M + C by positivity)
    have h3 := mul_nonneg hC hD
    exact hv.trans (by nlinarith)

end Euler2D

end
