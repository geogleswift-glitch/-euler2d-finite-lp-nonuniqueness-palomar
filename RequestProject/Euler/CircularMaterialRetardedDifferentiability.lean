module

public import RequestProject.Euler.CircularMaterialTransferProfile
public import RequestProject.Euler.GlobalPlanarFourthMoment
public import RequestProject.Euler.RetardedStrongDifferentiability

/-! Continuity of the ORIGINAL glued material/Euler moment and the
strong derivative of its ORIGINAL retarded transfer response. Both
the negative ancient branch and the actual positive continuation are
retained, including their common value at zero. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem continuous_moment : Continuous P.moment := by
  have hneg : ContinuousOn P.moment (Iic (0 : ℝ)) :=
    ((contDiff_circularBoundaryFourthMoment γ).continuous.comp_continuousOn P.ancient_continuous).congr
      (fun s hs => P.moment_negative s hs)
  have hw := integrable_circularPhasePatchPlanarVorticity hγ hγ1 (P.ancient_domain 0 le_rfl)
  have hsource := fun x => norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1
    (P.ancient_domain 0 le_rfl) (x := x)
  have hpos : ContinuousOn P.moment (Ici (0 : ℝ)) :=
    (P.positive.continuousOn_fourthMoment_nonneg hw (by norm_num : (0 : ℝ) ≤ 5 / 4)
      P.positiveSpeedBound_nonneg hsource P.positive_norm_velocity_le).congr
      (fun s hs => P.moment_positive s hs)
  have hh := hneg.union_of_isClosed hpos isClosed_Iic isClosed_Ici
  have hunion : Iic (0 : ℝ) ∪ Ici (0 : ℝ) = univ := by
    ext s
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total s 0
  rw [hunion] at hh
  exact continuousOn_univ.mp hh

theorem hasDerivAt_retarded_transfer {b ρ : ℝ} (hb : b ∈ Ioo (0 : ℝ) (1 / 4)) (t : ℝ) :
    HasDerivAt (retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
      ((ρ : ℂ) ^ 6 * Kstar) P.moment)
      (((b : ℂ) * lamStar) *
        retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          ((ρ : ℂ) ^ 6 * Kstar) P.moment t +
        ((ρ : ℂ) ^ 6 * Kstar) * Complex.exp (-(2 * I * b) * (t : ℂ)) * P.moment t) t := by
  have hz0 : 0 < (((b : ℂ) * (sigma + 5 / 4 * I) : ℂ)).re := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.div_re, Complex.normSq_ofNat]
    norm_num
    exact mul_pos hb.1 sigma_pos
  have hz1 : (((b : ℂ) * (sigma + 5 / 4 * I) : ℂ)).re < sigma := by
    have hb1 : b < 1 := by linarith only [hb.2]
    simpa using mul_lt_of_lt_one_left sigma_pos hb1
  have hh := hasDerivAt_retardedSol_of_continuous P.laplace.expWindow P.continuous_moment hz0 hz1
    ((b : ℂ) * lamStar) ((ρ : ℂ) ^ 6 * Kstar) t
  simpa only [transfer_frequency] using hh

end CircularMaterialTransferProfile
end Euler2D

end
