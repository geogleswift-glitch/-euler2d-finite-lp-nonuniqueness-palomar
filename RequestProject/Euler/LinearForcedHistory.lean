module

public import RequestProject.Euler.Laplace
public import Mathlib.Analysis.Calculus.MeanValue

/-! A past-source estimate for the actual linear scalar equation.
The proof uses its strong derivative and a continuous real barrier;
the bounded residual itself need not be continuous. The entrance
value is retained, and growth uses Re(c), rather than |c|. -/

@[expose] public section

set_option maxHeartbeats 14000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology Metric

namespace Euler2D

theorem norm_linear_forced_history_le
    {c : ℂ} {σ A ε D a : ℝ} (hc : 0 ≤ c.re) (hgap : 0 < σ - c.re)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (W F : ℝ → ℂ)
    (hW : ∀ t ∈ Icc (0 : ℝ) a, ∃ E : ℂ, ‖E‖ ≤ ε ∧
      HasDerivAt W (c * W t + F t + E) t)
    (hF : ∀ t ∈ Icc (0 : ℝ) a, ‖F t‖ ≤ A * Real.exp (-σ * (D - t))) :
    ‖W a‖ ≤ ‖W 0‖ * Real.exp (c.re * a) +
      A / (σ - c.re) * Real.exp (-σ * (D - a)) + ε * a * Real.exp (c.re * a) := by
  let Z := fun t : ℝ => Complex.exp (-c * (t : ℂ)) * W t
  let coeff := A * Real.exp (-σ * D) / (σ - c.re)
  let B := fun t : ℝ => ‖W 0‖ + coeff * (Real.exp ((σ - c.re) * t) - 1) + ε * t
  let B' := fun t : ℝ => A * Real.exp (-σ * D) * Real.exp ((σ - c.re) * t) + ε
  have hcoeff : 0 ≤ coeff := by dsimp only [coeff]; positivity
  have hEd (t : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (-c * (u : ℂ)))
      (-c * Complex.exp (-c * (t : ℂ))) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one, mul_comm] using
      ((((hasDerivAt_id t).ofReal_comp).const_mul (-c)).cexp)
  have hZd : ∀ t ∈ Icc (0 : ℝ) a, ∃ E : ℂ, ‖E‖ ≤ ε ∧
      HasDerivAt Z (Complex.exp (-c * (t : ℂ)) * (F t + E)) t := by
    intro t ht
    obtain ⟨E, hE, hd⟩ := hW t ht
    refine ⟨E, hE, ?_⟩
    have hh := (hEd t).mul hd
    convert hh using 1 <;>
      (try funext s) <;>
      (try dsimp only [Z, Pi.mul_def, id_eq]) <;> ring
  have hZc : ContinuousOn Z (Icc (0 : ℝ) a) := by
    intro t ht
    obtain ⟨E, _, hd⟩ := hZd t ht
    exact hd.continuousAt.continuousWithinAt
  have hZderiv : ∀ t ∈ Ico (0 : ℝ) a, HasDerivWithinAt Z (deriv Z t) (Ici t) t := by
    intro t ht
    obtain ⟨E, _, hd⟩ := hZd t ⟨ht.1, ht.2.le⟩
    exact hd.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hBd (t : ℝ) : HasDerivAt B (B' t) t := by
    have he : HasDerivAt (fun u : ℝ => Real.exp ((σ - c.re) * u))
        ((σ - c.re) * Real.exp ((σ - c.re) * t)) t := by
      simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul (σ - c.re)).exp
    have hh := (((he.sub_const 1).const_mul coeff).const_add ‖W 0‖).add
      ((hasDerivAt_id t).const_mul ε)
    convert hh using 1 <;>
      (try funext s) <;>
      (try dsimp only [B, B', coeff, Pi.add_def, Pi.mul_def, id_eq]) <;>
      field_simp [hgap.ne'] <;> ring
  have hZbound : ∀ t ∈ Ico (0 : ℝ) a, ‖deriv Z t‖ ≤ B' t := by
    intro t ht
    obtain ⟨E, hE, hd⟩ := hZd t ⟨ht.1, ht.2.le⟩
    rw [hd.deriv, norm_mul, norm_cexp_neg_mul]
    have hphase : Real.exp (-c.re * t) * Real.exp (-σ * (D - t)) =
        Real.exp (-σ * D) * Real.exp ((σ - c.re) * t) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have he1 : Real.exp (-c.re * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith only [hc, ht.1])
    calc
      _ ≤ Real.exp (-c.re * t) * (‖F t‖ + ‖E‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
      _ ≤ Real.exp (-c.re * t) * (A * Real.exp (-σ * (D - t)) + ε) :=
        mul_le_mul_of_nonneg_left (add_le_add (hF t ⟨ht.1, ht.2.le⟩) hE) (Real.exp_pos _).le
      _ = A * (Real.exp (-c.re * t) * Real.exp (-σ * (D - t))) + ε * Real.exp (-c.re * t) := by ring
      _ ≤ B' t := by
        rw [hphase]
        have hh := mul_le_mul_of_nonneg_left he1 hε
        dsimp only [B']
        nlinarith only [hh]
  have hZ0 : ‖Z 0‖ ≤ B 0 := by
    dsimp only [Z, B]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, Real.exp_zero,
      sub_self, zero_mul, add_zero, mul_zero, le_refl]
  have hbar := image_norm_le_of_norm_deriv_right_le_deriv_boundary hZc hZderiv hZ0 hBd hZbound
    (show a ∈ Icc (0 : ℝ) a from ⟨ha, le_rfl⟩)
  have hBdrop : B a ≤ ‖W 0‖ + coeff * Real.exp ((σ - c.re) * a) + ε * a := by
    dsimp only [B]
    linarith only [hcoeff]
  have hrecover : Real.exp (c.re * a) * ‖Z a‖ = ‖W a‖ := by
    dsimp only [Z]
    rw [norm_mul, norm_cexp_neg_mul, ← mul_assoc, ← Real.exp_add,
      show c.re * a + -c.re * a = 0 by ring, Real.exp_zero, one_mul]
  have hphase : Real.exp (c.re * a) * (Real.exp (-σ * D) * Real.exp ((σ - c.re) * a)) =
      Real.exp (-σ * (D - a)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (c.re * a) * ‖Z a‖ := hrecover.symm
    _ ≤ Real.exp (c.re * a) * B a := mul_le_mul_of_nonneg_left hbar (Real.exp_pos _).le
    _ ≤ Real.exp (c.re * a) * (‖W 0‖ + coeff * Real.exp ((σ - c.re) * a) + ε * a) :=
      mul_le_mul_of_nonneg_left hBdrop (Real.exp_pos _).le
    _ = ‖W 0‖ * Real.exp (c.re * a) + A / (σ - c.re) *
        (Real.exp (c.re * a) * (Real.exp (-σ * D) * Real.exp ((σ - c.re) * a))) +
          ε * a * Real.exp (c.re * a) := by dsimp only [coeff]; ring
    _ = _ := by rw [hphase]

theorem norm_linear_forced_residual_le
    {c : ℂ} {ε a : ℝ} (hc : 0 ≤ c.re) (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (W : ℝ → ℂ)
    (hW : ∀ t ∈ Icc (0 : ℝ) a, ∃ E : ℂ, ‖E‖ ≤ ε ∧ HasDerivAt W (c * W t + E) t) :
    ‖W a‖ ≤ (‖W 0‖ + ε * a) * Real.exp (c.re * a) := by
  have hh := norm_linear_forced_history_le (σ := c.re + 1) (A := 0) (D := 0)
    hc (by linarith) (by norm_num) hε ha W (fun _ => 0)
    (by
      intro t ht
      obtain ⟨E, hE, hd⟩ := hW t ht
      exact ⟨E, hE, by simpa only [add_zero] using hd⟩)
    (by intro t _; simp only [norm_zero, zero_mul, le_refl])
  simpa only [zero_div, zero_mul, add_zero, add_mul] using hh

theorem linear_forced_history_lookback_le
    {c : ℂ} {σ A ε D L d : ℝ} (hc : 0 ≤ c.re) (hgap : 0 < σ - c.re)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hLD : L ≤ D)
    (W F : ℝ → ℂ) (hW0 : W 0 = 0)
    (hW : ∀ t ∈ Icc (0 : ℝ) (D - L), ∃ E : ℂ, ‖E‖ ≤ ε ∧
      HasDerivAt W (c * W t + F t + E) t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (D - L), ‖F t‖ ≤ A * Real.exp (-σ * (D - t))) :
    Real.exp (c.re * (L + d)) * ‖W (D - L)‖ ≤
      A / (σ - c.re) * Real.exp (-(σ - c.re) * L) * Real.exp (c.re * d) +
        ε * (D - L) * Real.exp (c.re * (D + d)) := by
  have hh := norm_linear_forced_history_le hc hgap hA hε (sub_nonneg.mpr hLD) W F hW hF
  rw [hW0, norm_zero, zero_mul, zero_add] at hh
  have hphase : Real.exp (c.re * (L + d)) * Real.exp (-σ * (D - (D - L))) =
      Real.exp (-(σ - c.re) * L) * Real.exp (c.re * d) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have herr : Real.exp (c.re * (L + d)) * Real.exp (c.re * (D - L)) =
      Real.exp (c.re * (D + d)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (c.re * (L + d)) * (A / (σ - c.re) *
        Real.exp (-σ * (D - (D - L))) + ε * (D - L) * Real.exp (c.re * (D - L))) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = A / (σ - c.re) *
        (Real.exp (c.re * (L + d)) * Real.exp (-σ * (D - (D - L)))) +
        ε * (D - L) * (Real.exp (c.re * (L + d)) * Real.exp (c.re * (D - L))) := by ring
    _ = _ := by rw [hphase, herr]; ring

end Euler2D

end
