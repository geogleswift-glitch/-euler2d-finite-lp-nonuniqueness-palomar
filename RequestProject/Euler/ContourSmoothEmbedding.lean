module

public import RequestProject.Euler.LittleContourSpace
public import RequestProject.Euler.ContourChordArc

/-!
# Genuine smooth periodic functions in the contour Banach space

All actual smooth 2π-periodic functions, including the reference circles,
embed in the little C¹ Hölder space for 0 < γ ≤ 1.  The derivative Hölder
bound is proved using true shortest circle representatives and a bound on
the actual second derivative of the periodic function.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal BoundedContinuousFunction ContDiff

namespace Euler2D

lemma continuous_periodicContourLift {p : ℝ → ℂ}
    (hp : Function.Periodic p (2 * Real.pi)) (hc : Continuous p) :
    Continuous hp.lift := by
  have hq : Topology.IsQuotientMap (fun θ : ℝ => (θ : ContourCircle)) :=
    isQuotientMap_quotient_mk'
  exact hq.continuous_iff.mpr hc

/-- Actual differentiation preserves actual periodicity. -/
lemma periodic_deriv_contour {p : ℝ → ℂ}
    (hp : Function.Periodic p (2 * Real.pi)) (hd : Differentiable ℝ p) :
    Function.Periodic (deriv p) (2 * Real.pi) := by
  intro θ
  have hh := ((hd (θ + 2 * Real.pi)).hasDerivAt).scomp θ
    ((hasDerivAt_id θ).add_const (2 * Real.pi))
  simp only [id_eq] at hh
  have he : (p ∘ (fun t : ℝ => t + 2 * Real.pi)) = p := funext hp
  rw [he] at hh
  simpa only [one_smul] using hh.deriv.symm

theorem lipschitzWith_contour_of_deriv_bound {f : ContourCircle → ℂ} {C : ℝ≥0}
    (hf : ContDiff ℝ 1 (fun θ : ℝ => f (θ : ContourCircle)))
    (hd : ∀ θ : ℝ, ‖deriv (fun t : ℝ => f (t : ContourCircle)) θ‖ ≤ C) :
    LipschitzWith C f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨θ, φ, hθ, hφ, _, hdist⟩ := exists_short_contour_representatives x y
  have hb := norm_sub_le_of_contDiff_deriv_bound hf C.coe_nonneg hd θ φ
  rw [hθ, hφ, ← hdist] at hb
  simpa only [dist_eq_norm] using hb

lemma contour_dist_le_pi (x y : ContourCircle) : dist x y ≤ Real.pi := by
  obtain ⟨_, _, _, _, hb, hd⟩ := exists_short_contour_representatives x y
  rwa [hd]

/-- A genuine Lipschitz function is Hölder for all exponents at most one
in the genuine circle metric. -/
theorem memHolder_contour_of_lipschitz {γ C : ℝ≥0} {f : ContourCircle → ℂ}
    (hγ : γ ≤ 1) (hf : LipschitzWith C f) : MemHolder γ f := by
  have hb (x y : ContourCircle) : edist x y ≤ ENNReal.ofReal Real.pi := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (contour_dist_le_pi x y)
  exact (hf.holderWith.of_le (D := Real.toNNReal Real.pi) hb hγ).memHolder

/-- A smooth periodic function has a genuine Hölder derivative on the
actual quotient circle, without any assumed derivative bound. -/
theorem memHolder_periodic_deriv {γ : ℝ≥0} (hγ : γ ≤ 1) {p : ℝ → ℂ}
    (hp : Function.Periodic p (2 * Real.pi)) (hs : ContDiff ℝ ∞ p) :
    MemHolder γ (periodic_deriv_contour hp (contDiff_infty_iff_deriv.mp hs).1).lift := by
  have hd := (contDiff_infty_iff_deriv.mp hs).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hpd := periodic_deriv_contour hp (contDiff_infty_iff_deriv.mp hs).1
  have hpdd := periodic_deriv_contour hpd (contDiff_infty_iff_deriv.mp hd).1
  obtain ⟨C, hC, hbound⟩ :=
    (hpdd.isBounded_of_continuous (by positivity) hdd.continuous).exists_pos_norm_le
  apply memHolder_contour_of_lipschitz hγ (C := ⟨C, hC.le⟩)
  apply lipschitzWith_contour_of_deriv_bound
  · simpa only [Function.Periodic.lift_coe] using hd.of_le (by simp)
  · intro θ
    change ‖deriv (deriv p) θ‖ ≤ C
    exact hbound _ (Set.mem_range_self θ)

/-- Every genuine smooth periodic function is an actual C¹ Hölder loop. -/
def contourC1OfPeriodicSmooth {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (p : ℝ → ℂ) (hp : Function.Periodic p (2 * Real.pi)) (hs : ContDiff ℝ ∞ p) :
    ContourC1Space γ :=
  ContourC1Space.ofHasDerivAt
    (BoundedContinuousFunction.mkOfCompact ⟨hp.lift, continuous_periodicContourLift hp hs.continuous⟩)
    (contourHolderOfMemHolder hγ₀
      (periodic_deriv_contour hp (contDiff_infty_iff_deriv.mp hs).1).lift
      (memHolder_periodic_deriv hγ₁ hp hs))
    (fun θ => (contDiff_infty_iff_deriv.mp hs).1 θ |>.hasDerivAt)

@[simp] theorem lift_contourC1OfPeriodicSmooth {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (p : ℝ → ℂ) (hp : Function.Periodic p (2 * Real.pi)) (hs : ContDiff ℝ ∞ p) :
    ContourC1Space.lift γ (contourC1OfPeriodicSmooth hγ₀ hγ₁ p hp hs) = p := rfl

/-- The actual embedding of every smooth periodic loop into the little space. -/
def littleContourOfPeriodicSmooth {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (p : ℝ → ℂ) (hp : Function.Periodic p (2 * Real.pi)) (hs : ContDiff ℝ ∞ p) :
    LittleContourSpace γ :=
  LittleContourSpace.ofSmooth γ (contourC1OfPeriodicSmooth hγ₀ hγ₁ p hp hs) hs

@[simp] theorem lift_littleContourOfPeriodicSmooth {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (p : ℝ → ℂ) (hp : Function.Periodic p (2 * Real.pi)) (hs : ContDiff ℝ ∞ p) :
    LittleContourSpace.lift γ (littleContourOfPeriodicSmooth hγ₀ hγ₁ p hp hs) = p := rfl

lemma contDiff_refCircle (r : ℝ) : ContDiff ℝ ∞ (refCircle r) := by
  unfold refCircle
  have hx : ContDiff ℝ ∞ (fun θ : ℝ => (θ : ℂ)) := Complex.ofRealCLM.contDiff
  have hm : ContDiff ℝ ∞ (fun θ : ℝ => (θ : ℂ) * I) := hx.mul contDiff_const
  exact contDiff_const.mul hm.cexp

lemma periodic_refCircle (r : ℝ) : Function.Periodic (refCircle r) (2 * Real.pi) := by
  intro θ
  unfold refCircle
  rw [show (((θ + 2 * Real.pi : ℝ) : ℂ) * I) =
    (θ : ℂ) * I + 2 * Real.pi * I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The paper's actual reference circle, in the genuine little Banach space. -/
def littleReferenceCircle {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (r : ℝ) :
    LittleContourSpace γ :=
  littleContourOfPeriodicSmooth hγ₀ hγ₁ (refCircle r) (periodic_refCircle r) (contDiff_refCircle r)

@[simp] theorem lift_littleReferenceCircle {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (r : ℝ) :
    LittleContourSpace.lift γ (littleReferenceCircle hγ₀ hγ₁ r) = refCircle r := rfl

end Euler2D

end
