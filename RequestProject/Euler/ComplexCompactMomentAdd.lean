module

public import RequestProject.Euler.ComplexSourceMomentBounds

/-! Exact conjugate volume-moment addition for compact integrable
sources. This identifies the activated child's actual moment inside
the actual rough inner cluster. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

theorem integrable_complexMomentIntegrand_of_support {w : ℂ → ℝ} {S : ℝ}
    (hw : Integrable w) (hsupp : ∀ z, S < ‖z‖ → w z = 0) (n : ℕ) :
    Integrable (fun z => (w z : ℂ) * conj z ^ n) := by
  refine (integrable_norm_pow_mul_of_supp hw hsupp n).mono' ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul
      (by fun_prop : Continuous (fun z : ℂ => conj z ^ n)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => by
      change ‖(w z : ℂ) * conj z ^ n‖ ≤ ‖z‖ ^ n * |w z|
      rw [norm_mul, norm_pow, norm_conj, Complex.norm_real, Real.norm_eq_abs, mul_comm])

theorem complexMoment_add_of_compact_support {u v : ℂ → ℝ} {Su Sv : ℝ}
    (hu : Integrable u) (hv : Integrable v)
    (hsu : ∀ z, Su < ‖z‖ → u z = 0) (hsv : ∀ z, Sv < ‖z‖ → v z = 0) (n : ℕ) :
    momentN (fun z => u z + v z) n = momentN u n + momentN v n := by
  unfold momentN
  simp_rw [Complex.ofReal_add, add_mul]
  exact integral_add (integrable_complexMomentIntegrand_of_support hu hsu n)
    (integrable_complexMomentIntegrand_of_support hv hsv n)

end Euler2D

end
