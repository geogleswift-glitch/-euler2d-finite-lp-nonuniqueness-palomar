module

public import RequestProject.Euler.ContourChordArc
public import RequestProject.Euler.ContourTaylor

/-!
# The genuine logarithm of a near-circle chord ratio

A small actual derivative perturbation keeps the chord ratio in the
logarithm's slit plane. Its actual logarithmic derivative is the
difference of the reference and perturbed Cauchy kernels.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace Euler2D

def contourChordRatio (z : ℝ → ℂ) (r θ φ : ℝ) : ℂ :=
  (z θ - z φ) / (refCircle r θ - refCircle r φ)

theorem norm_contourChordRatio_sub_one {z : ℝ → ℂ} {r ε θ φ : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε)
    (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε)
    (hangle : |θ - φ| ≤ Real.pi) (hne : θ ≠ φ) :
    ‖contourChordRatio z r θ φ - 1‖ ≤ ε / (2 * r / Real.pi) := by
  have hcoef : 0 < 2 * r / Real.pi := by positivity
  have hgap : 0 < |θ - φ| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have href := refCircle_chord_lower hr.le hangle
  have hden : 0 < ‖refCircle r θ - refCircle r φ‖ := (mul_pos hcoef hgap).trans_le href
  have hden0 : refCircle r θ - refCircle r φ ≠ 0 := norm_pos_iff.mp hden
  have hnum := norm_sub_le_of_contDiff_deriv_bound hp hε hd θ φ
  have he : contourChordRatio z r θ φ - 1 =
      ((z θ - refCircle r θ) - (z φ - refCircle r φ)) /
        (refCircle r θ - refCircle r φ) := by
    unfold contourChordRatio
    field_simp [hden0]
    ring
  rw [he, norm_div]
  calc
    _ ≤ (ε * |θ - φ|) / ‖refCircle r θ - refCircle r φ‖ :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (ε * |θ - φ|) / ((2 * r / Real.pi) * |θ - φ|) :=
      div_le_div_of_nonneg_left (mul_nonneg hε hgap.le) (mul_pos hcoef hgap) href
    _ = ε / (2 * r / Real.pi) := by
      field_simp

theorem contourChordRatio_mem_slitPlane {z : ℝ → ℂ} {r ε θ φ : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / Real.pi)
    (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε)
    (hangle : |θ - φ| ≤ Real.pi) (hne : θ ≠ φ) :
    contourChordRatio z r θ φ ∈ Complex.slitPlane := by
  have hb := norm_contourChordRatio_sub_one hr hε hp hd hangle hne
  have hh : ‖contourChordRatio z r θ φ - 1‖ < 1 :=
    hb.trans_lt ((div_lt_one (by positivity : 0 < 2 * r / Real.pi)).mpr hsmall)
  have hs := Complex.mem_slitPlane_of_norm_lt_one hh
  have he : 1 + (contourChordRatio z r θ φ - 1) = contourChordRatio z r θ φ := by ring
  simpa only [he] using hs

theorem hasDerivAt_log_contourChordRatio {z : ℝ → ℂ} {r θ φ : ℝ} {dz : ℂ}
    (hz : HasDerivAt z dz φ) (hz0 : z θ - z φ ≠ 0)
    (hr0 : refCircle r θ - refCircle r φ ≠ 0)
    (hslit : contourChordRatio z r θ φ ∈ Complex.slitPlane) :
    HasDerivAt (fun s => Complex.log (contourChordRatio z r θ s))
      (deriv (refCircle r) φ / (refCircle r θ - refCircle r φ) - dz / (z θ - z φ)) φ := by
  have href : HasDerivAt (refCircle r) (deriv (refCircle r) φ) φ :=
    (hasDerivAt_refCircle r φ).differentiableAt.hasDerivAt
  have hq := ((hasDerivAt_const φ (z θ)).sub hz).div
    ((hasDerivAt_const φ (refCircle r θ)).sub href) hr0
  have hl := hq.clog_real hslit
  have hlog := hl.congr_of_eventuallyEq
    (f₁ := fun s => Complex.log (contourChordRatio z r θ s))
    (Filter.Eventually.of_forall fun s => by
      simp only [contourChordRatio, Pi.sub_apply, Pi.div_apply])
  apply hlog.congr_deriv
  simp only [Pi.sub_apply, Pi.div_apply]
  field_simp [hz0, hr0] <;> ring

end Euler2D

end
