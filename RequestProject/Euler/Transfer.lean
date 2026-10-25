module

public import RequestProject.Euler.NormalEigen
public import RequestProject.Euler.Laplace

/-!
# The nonzero transfer coefficient

Formalization of Proposition `nt:prop:transfer` of the paper, in the following form.
For the fourth normal mode of the parent cell, the growing left coordinate
`ℓ₊(η) = η₁/2 + η₂/(2ia)` satisfies `ℓ₊(v₊) = 1`, `ℓ₊(v₋) = 0` and intertwines `i B₄` with
`λ_*`; projecting the child forcing `ρ⁶ (i/2π)(a⁻⁶, 1) e^{-2ibs} N(s)` gives the scalar
equation `y' = bλ_* y + ρ⁶ K_* e^{-2ibs} N(s)` with `K_* = (i/4π)(a⁻⁶ - i/a) ≠ 0`.
Its unique retarded solution has growing coefficient
`lim_{s→∞} e^{-bλ_* s} y_b(s) = ρ⁶ K_* F(b(σ + 5i/4))`, whose zeros in `b ∈ (0,1)` do not
accumulate.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Complex

namespace Euler2D

/-- `K_* = (i/4π)(a⁻⁶ - i/a)`. -/
noncomputable def Kstar : ℂ := I / (4 * Real.pi) * ((cellA : ℂ)⁻¹ ^ 6 - I / cellA)

/-- The growing left coordinate `ℓ₊(η) = η₁/2 + η₂/(2ia)`. -/
noncomputable def ellPlus (η : Fin 2 → ℂ) : ℂ := η 0 / 2 + η 1 / (2 * I * cellA)

lemma cellA_ne : (cellA : ℂ) ≠ 0 := by exact_mod_cast cellA_pos.ne'

lemma Kstar_ne_zero : Kstar ≠ 0 := by
  unfold Kstar
  have hpi : (4 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (4 * Real.pi : ℝ) ≠ 0)
  refine mul_ne_zero (div_ne_zero I_ne_zero hpi) ?_
  have hrw : ((cellA : ℂ)⁻¹ ^ 6 - I / cellA) =
      ((cellA⁻¹ ^ 6 : ℝ) : ℂ) + ((-cellA⁻¹ : ℝ) : ℂ) * I := by push_cast; ring
  rw [hrw]
  intro h
  have him : (((cellA⁻¹ ^ 6 : ℝ) : ℂ) + ((-cellA⁻¹ : ℝ) : ℂ) * I).im = -cellA⁻¹ := by
    rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  rw [h, Complex.zero_im] at him
  have : cellA⁻¹ ≠ 0 := inv_ne_zero cellA_pos.ne'
  exact this (by linarith)

lemma ellPlus_vPlus : ellPlus vPlus = 1 := by
  have := cellA_ne
  simp [ellPlus, vPlus]; field_simp; ring

lemma ellPlus_vMinus : ellPlus ![1, -I * cellA] = 0 := by
  have := cellA_ne
  simp [ellPlus]; field_simp; ring

/-- `ℓ₊` is a left eigenvector: `ℓ₊(i B₄ η) = λ_* ℓ₊(η)`. -/
lemma ellPlus_left_eigen (η : Fin 2 → ℂ) :
    ellPlus ((I • (Bmat 4).map (fun r : ℝ => (r : ℂ))).mulVec η) = lamStar * ellPlus η := by
  have ha := cellA_ne
  have h2 : (cellA : ℂ) ^ 2 = 3 / 5 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) cellA_sq; push_cast at this; exact this
  have hs : (sigma : ℂ) = 3 / 4 * cellA ^ 3 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) sigma_eq; push_cast at this; exact this
  simp only [ellPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply,
    Matrix.map_apply, Bmat, lamStar, hs]
  simp
  field_simp
  linear_combination (-6 * (cellA : ℂ) ^ 3 * η 1) * I_sq + (10 * I * η 0 * (cellA : ℂ) ^ 4) * h2

/-- Projection of the child forcing direction `(i/2π)(a⁻⁶, 1)` gives `K_*`. -/
lemma ellPlus_forcing : ellPlus ![I / (2 * Real.pi) * (cellA : ℂ)⁻¹ ^ 6, I / (2 * Real.pi)] = Kstar := by
  have ha := cellA_ne
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [ellPlus, Kstar]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The forcing frequency: `b(λ_* + 2i) = b(σ + 5i/4)`. -/
lemma transfer_frequency (b : ℝ) :
    (b : ℂ) * (sigma + 5 / 4 * I) - b * lamStar = 2 * I * b := by
  simp [lamStar]; ring

/-- **Proposition (Nonzero transfer coefficient).** Let `N` satisfy the hypotheses of
Theorem `nt:thm:laplace` with growth rate `σ` (the canonical value of Section `part:pc`).
For `b ∈ (0,1)` and any `ρ`, every solution `y_b` of
`y' = bλ_* y + ρ⁶ K_* e^{-2ibs} N(s)` normalized by `e^{-bλ_* s} y_b(s) → 0` at `-∞`
satisfies `e^{-bλ_* s} y_b(s) → ρ⁶ K_* F(b(σ + 5i/4))` as `s → +∞`. For `ρ ≠ 0` the zeros of
this coefficient, as a function of `b ∈ (0,1)`, do not accumulate in `(0,1)`. -/
theorem transfer_coefficient {ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (hN : LaplaceHyp sigma ν δ d κ N) (b ρ : ℝ) (hb : b ∈ Ioo (0 : ℝ) 1) (y : ℝ → ℂ)
    (hy : IsMildSolution (b * lamStar)
      (fun t : ℝ => (ρ : ℂ) ^ 6 * Kstar * Complex.exp (-(2 * I * b) * t) * N t) y)
    (hnorm : Tendsto (fun s : ℝ => Complex.exp (-(b * lamStar) * s) * y s) atBot (𝓝 0)) :
    Tendsto (fun s : ℝ => Complex.exp (-(b * lamStar) * s) * y s) atTop
      (𝓝 ((ρ : ℂ) ^ 6 * Kstar * bilateral N (b * (sigma + 5 / 4 * I)))) ∧
    (ρ ≠ 0 → ∀ b₀ ∈ Ioo (0 : ℝ) 1, ¬ ∃ᶠ b' : ℝ in 𝓝[≠] b₀,
      (ρ : ℂ) ^ 6 * Kstar * bilateral N (b' * (sigma + 5 / 4 * I)) = 0) := by
  have hσ := sigma_pos
  set z : ℂ := (b : ℂ) * (sigma + 5 / 4 * I)
  have hz0 : 0 < z.re := by simp [z]; nlinarith [hb.1]
  have hz1 : z.re < sigma := by simp [z]; nlinarith [hb.2]
  obtain ⟨hmild, hbot, htop⟩ := retardedSol_spec hN.expWindow hz0 hz1 (b * lamStar)
    ((ρ : ℂ) ^ 6 * Kstar)
  have hf : (fun t : ℝ => (ρ : ℂ) ^ 6 * Kstar * Complex.exp (-(z - b * lamStar) * t) * N t) =
      fun t : ℝ => (ρ : ℂ) ^ 6 * Kstar * Complex.exp (-(2 * I * b) * t) * N t := by
    funext t; rw [transfer_frequency]
  rw [hf] at hmild
  have heq := retarded_unique hy hmild hnorm hbot
  refine ⟨heq ▸ htop, fun hρ b₀ hb₀ hfr => ?_⟩
  have hK : (ρ : ℂ) ^ 6 * Kstar ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hρ)) Kstar_ne_zero
  apply (bilateral_laplace_theorem hN (5 / 4)).2.2 b₀ hb₀
  refine hfr.mono fun b' hb' => ?_
  rcases mul_eq_zero.mp hb' with h | h
  · exact absurd h hK
  · simpa using h

end Euler2D

end
