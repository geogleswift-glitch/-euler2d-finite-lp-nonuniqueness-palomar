module

public import RequestProject.Euler.SmoothSobolev

/-! The genuine small-radius factor in localized Sobolev estimates. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace Euler2D

lemma torusLocalizedSobolevBound_closedBall_le {q B r : ℝ}
    (hq : 0 < q) (hB : 0 ≤ B) (hr : 0 ≤ r) (c : R2) :
    torusLocalizedSobolevBound (ENNReal.ofReal q) B (closedBall c r) ≤
      B * Real.pi ^ (1 / q) * r ^ (2 / q) := by
  have hvol : (μT (closedBall c r)).toReal ≤ r ^ 2 * Real.pi := by
    have hm := ENNReal.toReal_mono (measure_closedBall_lt_top (μ := volume) (x := c) (r := r)).ne
      (Measure.restrict_apply_le (μ := volume) torusBox (closedBall c r))
    simpa only [EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le] using hm
  rw [torusLocalizedSobolevBound, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hB, ENNReal.toReal_ofReal hq.le]
  have hrad : (r ^ 2) ^ q⁻¹ = r ^ (2 / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    congr 1
  calc
    (μT (closedBall c r)).toReal ^ q⁻¹ * B ≤ (r ^ 2 * Real.pi) ^ q⁻¹ * B :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow ENNReal.toReal_nonneg hvol (inv_nonneg.mpr hq.le)) hB
    _ = B * Real.pi ^ (1 / q) * r ^ (2 / q) := by
      rw [Real.mul_rpow (sq_nonneg _) Real.pi_pos.le, hrad, one_div]
      ring

end Euler2D

end
