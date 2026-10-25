module

public import RequestProject.Euler.RetardedLogarithmicAbsorption

/-! Uniform rho-cubic absorption of the actual capture error on a
logarithmic normalized horizon. Both the horizon and torus coefficient
may be selected after the scale; only their quantitative bounds enter. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology Polynomial

namespace Euler2D

theorem tendsto_captureLog_polynomial_remainder (B L D₀ : ℝ) :
    Tendsto (fun ξ : ℝ => B * Real.exp (-ξ) ^ 3 * (1 + L * ξ + D₀) ^ 4)
      atTop (𝓝 0) := by
  let p : ℝ[X] := Polynomial.C B * (1 + (Polynomial.C L * X + Polynomial.C D₀)) ^ 4
  have hp (ξ : ℝ) : p.eval ξ = B * (1 + L * ξ + D₀) ^ 4 := by
    simp only [p, eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X]
    ring
  convert tendsto_polynomial_mul_exp_decay p (by norm_num : (0 : ℝ) < 3) using 1
  ext ξ
  have he : Real.exp (-ξ) ^ 3 = Real.exp (-(3 : ℝ) * ξ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hp, ← he]
  ring

theorem exists_eventually_logarithmic_capture_error_budget
    {Eg A Kcorr B Ktor L D₀ : ℝ}
    (hEg : 0 < Eg) (hA : 0 ≤ A) (hKcorr : 0 ≤ Kcorr)
    (hB : 0 ≤ B) (hKtor : 0 ≤ Ktor) :
    ∃ Cerror > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      ∀ κ D : ℝ, 0 ≤ κ → κ ≤ Ktor * ρ ^ 8 → 0 ≤ D → D ≤ L * ξ + D₀ →
      Eg * (A * ρ ^ 3 + Kcorr * κ + B * ρ ^ 6 * (1 + D) ^ 4) ≤ Cerror * ρ ^ 3 := by
  let Cerror := Eg * (A + 2) + 1
  have hCerror : 0 < Cerror := by dsimp only [Cerror]; positivity
  have hpoly : ∀ᶠ ξ : ℝ in atTop,
      B * Real.exp (-ξ) ^ 3 * (1 + L * ξ + D₀) ^ 4 ≤ 1 :=
    ((tendsto_captureLog_polynomial_remainder B L D₀).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
  have htor : ∀ᶠ ξ : ℝ in atTop, (Kcorr * Ktor) * Real.exp (-ξ) ^ 5 ≤ 1 := by
    have ht : Tendsto (fun ξ : ℝ => (Kcorr * Ktor) * Real.exp (-ξ) ^ 5) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : (5 : ℕ) ≠ 0), mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow 5).const_mul (Kcorr * Ktor)
    exact (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
  refine ⟨Cerror, hCerror, ?_⟩
  filter_upwards [hpoly, htor] with ξ hpolyξ htorξ
  dsimp only
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos _
  intro κ D hκ hκtor hD hDlog
  have htorScale : (Kcorr * Ktor) * ρ ^ 8 ≤ ρ ^ 3 := by
    convert mul_le_mul_of_nonneg_right htorξ (pow_nonneg hρ.le 3) using 1 <;> ring
  have hκerror : Kcorr * κ ≤ ρ ^ 3 :=
    (mul_le_mul_of_nonneg_left hκtor hKcorr).trans (by convert htorScale using 1 <;> ring)
  have hpolyScale : B * ρ ^ 6 * (1 + L * ξ + D₀) ^ 4 ≤ ρ ^ 3 := by
    convert mul_le_mul_of_nonneg_right hpolyξ (pow_nonneg hρ.le 3) using 1 <;> ring
  have hpowers : (1 + D) ^ 4 ≤ (1 + L * ξ + D₀) ^ 4 := by
    apply pow_le_pow_left₀ (by linarith only [hD])
    linarith only [hDlog]
  have hDerror : B * ρ ^ 6 * (1 + D) ^ 4 ≤ ρ ^ 3 :=
    (mul_le_mul_of_nonneg_left hpowers (mul_nonneg hB (pow_nonneg hρ.le 6))).trans hpolyScale
  calc
    _ ≤ Eg * (A * ρ ^ 3 + ρ ^ 3 + ρ ^ 3) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hκerror) hDerror) hEg.le
    _ ≤ Cerror * ρ ^ 3 := by
      have hh : Eg * (A + 2) ≤ Cerror := by dsimp only [Cerror]; linarith
      convert mul_le_mul_of_nonneg_right hh (pow_nonneg hρ.le 3) using 1 <;> ring

theorem exists_eventually_circularCapture_scale_error_rhoThree_budget
    {Eg W0 Fbar Bpoly Damp cs E lam qbar Rg Ktor L D₀ : ℝ}
    (hEg : 0 < Eg) (hW0 : 0 ≤ W0) (hFbar : 0 ≤ Fbar) (hBpoly : 0 ≤ Bpoly)
    (hDamp : 0 ≤ Damp) (hcs : 0 < cs) (hE : 0 ≤ E) (hgap : qbar < lam)
    (hRg : 0 ≤ Rg) (hKtor : 0 ≤ Ktor) :
    ∃ Cerror > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      ∀ R D : ℝ, 0 ≤ R → R ≤ ρ → 0 ≤ D → D ≤ L * ξ + D₀ →
      let κ := Ktor * R ^ 8
      Eg * ((W0 + Fbar * Bpoly) * (Damp / cs + 1) * ρ ^ 3 +
        3 * (E * κ) * Damp / (lam - qbar) +
        Bpoly * ρ ^ 6 * (1 + D) ^ 4 + κ * Rg) ≤ Cerror * ρ ^ 3 := by
  let A := (W0 + Fbar * Bpoly) * (Damp / cs + 1)
  let Kcorr := 3 * E * Damp / (lam - qbar) + Rg
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hKcorr : 0 ≤ Kcorr := by dsimp only [Kcorr]; positivity [sub_pos.mpr hgap]
  obtain ⟨Cerror, hCerror, hbudget⟩ := exists_eventually_logarithmic_capture_error_budget
    (L := L) (D₀ := D₀) hEg hA hKcorr hBpoly hKtor
  refine ⟨Cerror, hCerror, ?_⟩
  filter_upwards [hbudget] with ξ hξ
  dsimp only
  let ρ := Real.exp (-ξ)
  intro R D hR hRρ hD hDlog
  have hκ : 0 ≤ Ktor * R ^ 8 := mul_nonneg hKtor (pow_nonneg hR 8)
  have hκρ : Ktor * R ^ 8 ≤ Ktor * ρ ^ 8 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hRρ 8) hKtor
  have hh := hξ (Ktor * R ^ 8) D hκ hκρ hD hDlog
  convert hh using 1 <;> dsimp only [A, Kcorr] <;> ring

end Euler2D

end
