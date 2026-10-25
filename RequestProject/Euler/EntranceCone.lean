module

public import Mathlib
public import RequestProject.Euler.ScalarLemmas

/-!
# Exit times, parent seed and entrance cone

* Lemma `cp:lem:times` (uniform outer exit times): the exact identity
  `A₀ t₀ = b^N β_N + ∑_{k<N} b^k d_k + s₀ ∑_{k<N} b^{k+1}` obtained from the entrance recursion
  `e_k = t_{k+1} + s₀/A_{k+1}`, `A_k = A₀ b^{-k}` (`exit_time_identity`), and the resulting
  uniform bounds `c₋/A₀ ≤ t₀ ≤ c₊/A₀` with every exit time in a fixed compact subinterval of
  `(0,T)` once `A₀ > c₊/T` (`outer_exit_times_uniform`).
* Corollary `re:cor:seed` (nonzero parent seed): `parent_seed`.
* Corollary `re:cor:cone` (parent entrance cone): the complementary response is eventually
  dominated by the growing one (`complementary_response_bound`, `canonical_cone_eventually`),
  and the strict cone is open at a point with nonzero growing part and invariant under positive
  scaling, so a small entry error places the actual parent in the cone (`entrance_cone_open`).
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Euler2D

/-! ### Uniform outer exit times -/

/-- **Lemma `cp:lem:times`, exact identity.** Put `A_k = A₀ / b^k`. If the entrance of label
`k < N` is `e_k = t_{k+1} + s₀ / A_{k+1}` and its exit is `t_k = e_k + d_k / A_k`, then
`A₀ t₀ = b^N (A_N t_N) + ∑_{k<N} b^k d_k + s₀ ∑_{k<N} b^{k+1}`. -/
theorem exit_time_identity {A₀ b s₀ : ℝ} (hA : A₀ ≠ 0) (hb : b ≠ 0) (N : ℕ) (t e d : ℕ → ℝ)
    (he : ∀ k < N, e k = t (k + 1) + s₀ / (A₀ / b ^ (k + 1)))
    (ht : ∀ k < N, t k = e k + d k / (A₀ / b ^ k)) :
    A₀ * t 0 = b ^ N * ((A₀ / b ^ N) * t N) + ∑ k ∈ Finset.range N, b ^ k * d k +
      s₀ * ∑ k ∈ Finset.range N, b ^ (k + 1) := by
  have key : ∀ j ≤ N, A₀ * t 0 = b ^ j * ((A₀ / b ^ j) * t j) +
      ∑ k ∈ Finset.range j, b ^ k * d k + s₀ * ∑ k ∈ Finset.range j, b ^ (k + 1) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjN : j < N := by omega
      rw [ih (by omega), Finset.sum_range_succ, Finset.sum_range_succ, ht j hjN, he j hjN]
      have hbj : b ^ j ≠ 0 := pow_ne_zero _ hb
      have hbj1 : b ^ (j + 1) ≠ 0 := pow_ne_zero _ hb
      field_simp
      ring
  exact key N le_rfl

/-- **Lemma `cp:lem:times` (uniform outer exit times).** Let `0 < b < 1`, `A₀ > 0`, `s₀ ≥ 0`,
`N ≥ 1`, and `A_k = A₀ / b^k`. Suppose the entrance recursion `e_k = t_{k+1} + s₀ / A_{k+1}`
holds, each normalized capture duration `A_k (t_k - e_k)` lies in `[D₋, D₊]` with `D₋ > 0`, and
`A_N t_N ∈ [S_b - 1/2, S_b + 1/2]` with `S_b ≥ 1/2`. With `c₋ = D₋` and
`c₊ = S_b + 1/2 + (D₊ + b s₀)/(1 - b)` (independent of `N` and `A₀`),
`c₋ / A₀ ≤ t₀ ≤ c₊ / A₀`. If moreover `A₀ > c₊ / T`, then
`[c₋/A₀, c₊/A₀]` is contained in `(0, T)`. -/
theorem outer_exit_times_uniform {A₀ b s₀ Dm Dp Sb T : ℝ} (hA : 0 < A₀) (hb0 : 0 < b)
    (hb1 : b < 1) (hT : 0 < T) (hs₀ : 0 ≤ s₀) (hDm : 0 < Dm) (hSb : 1 / 2 ≤ Sb) {N : ℕ} (hN : 1 ≤ N)
    (t e : ℕ → ℝ)
    (he : ∀ k < N, e k = t (k + 1) + s₀ / (A₀ / b ^ (k + 1)))
    (hd : ∀ k < N, (A₀ / b ^ k) * (t k - e k) ∈ Icc Dm Dp)
    (hβ : (A₀ / b ^ N) * t N ∈ Icc (Sb - 1 / 2) (Sb + 1 / 2)) :
    (Dm / A₀ ≤ t 0 ∧ t 0 ≤ (Sb + 1 / 2 + (Dp + b * s₀) / (1 - b)) / A₀) ∧
      ((Sb + 1 / 2 + (Dp + b * s₀) / (1 - b)) / T < A₀ →
        Icc (Dm / A₀) ((Sb + 1 / 2 + (Dp + b * s₀) / (1 - b)) / A₀) ⊆ Ioo 0 T) := by
  set d : ℕ → ℝ := fun k => (A₀ / b ^ k) * (t k - e k) with hd_def
  have ht : ∀ k < N, t k = e k + d k / (A₀ / b ^ k) := by
    intro k _
    have : A₀ / b ^ k ≠ 0 := div_ne_zero hA.ne' (pow_ne_zero _ hb0.ne')
    simp only [hd_def]; field_simp; ring
  have hid := exit_time_identity hA.ne' hb0.ne' N t e d he ht
  have hbd := exit_time_bounds hb0.le hb1 hDm hSb hβ hs₀ hN d hd
  rw [← hid] at hbd
  obtain ⟨h1, h2⟩ := hbd
  refine ⟨⟨by rw [div_le_iff₀ hA]; linarith, by rw [le_div_iff₀ hA]; linarith⟩, ?_⟩
  intro hcT x hx
  have hc : Dm ≤ Sb + 1 / 2 + (Dp + b * s₀) / (1 - b) := h1.trans h2
  refine ⟨lt_of_lt_of_le (div_pos hDm hA) hx.1, lt_of_le_of_lt hx.2 ?_⟩
  rw [div_lt_iff₀ hT] at hcT
  rw [div_lt_iff₀ hA]; linarith

/-! ### Nonzero parent seed -/

/-- **Corollary `re:cor:seed` (nonzero parent seed).** Let `ℓ` be a bounded real-linear
functional (the growing coordinate `ℓ_χ(s₀)`), `Y = Y_χ(s₀)` the canonical response with
`ℓ Y = Y₊(s₀)`, and `x = x_ρ(s₀)` the actual parent. If the entry estimate gives
`‖ρ⁻⁶ x - Y‖ ≤ δ` and the right-hand side is small, `‖ℓ‖ δ ≤ θ ‖Y₊(s₀)‖`, then
`‖ℓ x‖ ≥ (1 - θ) ρ⁶ ‖Y₊(s₀)‖`, which is positive when `θ < 1`, `ρ > 0` and `Y₊(s₀) ≠ 0`. -/
theorem parent_seed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : E →L[ℝ] ℂ)
    {x Y : E} {ρ δ θ : ℝ} (hρ : 0 < ρ) (hentry : ‖(ρ ^ 6)⁻¹ • x - Y‖ ≤ δ)
    (hsmall : ‖ℓ‖ * δ ≤ θ * ‖ℓ Y‖) :
    (1 - θ) * ρ ^ 6 * ‖ℓ Y‖ ≤ ‖ℓ x‖ ∧
      (θ < 1 → ℓ Y ≠ 0 → 0 < ‖ℓ x‖) := by
  have hρ6 : 0 < ρ ^ 6 := pow_pos hρ 6
  have h1 : ‖ℓ ((ρ ^ 6)⁻¹ • x) - ℓ Y‖ ≤ θ * ‖ℓ Y‖ := by
    rw [← map_sub]
    exact (ℓ.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hentry (norm_nonneg _)).trans hsmall)
  have h2 : ‖ℓ ((ρ ^ 6)⁻¹ • x)‖ = (ρ ^ 6)⁻¹ * ‖ℓ x‖ := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ6.le)]
  have h3 : ‖ℓ Y‖ - θ * ‖ℓ Y‖ ≤ (ρ ^ 6)⁻¹ * ‖ℓ x‖ := by
    have := norm_sub_norm_le (ℓ Y) (ℓ ((ρ ^ 6)⁻¹ • x))
    rw [norm_sub_rev] at this
    linarith
  have key : (1 - θ) * ρ ^ 6 * ‖ℓ Y‖ ≤ ‖ℓ x‖ := by
    have := mul_le_mul_of_nonneg_left h3 hρ6.le
    rw [← mul_assoc, mul_inv_cancel₀ hρ6.ne', one_mul] at this
    nlinarith
  refine ⟨key, fun hθ hY => lt_of_lt_of_le ?_ key⟩
  have : 0 < ‖ℓ Y‖ := norm_pos_iff.mpr hY
  have : 0 < 1 - θ := by linarith
  positivity

/-! ### Parent entrance cone -/

/-- **Corollary `re:cor:cone`, complementary response.** If the complementary part of the
canonical response satisfies `Q(s) ≤ C_μ e^{μs} ∫_{-∞}^s e^{-μt} ‖N(t)‖ dt` and
`t ↦ e^{-μt} ‖N(t)‖` is integrable on `ℝ`, then `Q(s) ≤ C e^{μs}` with
`C = C_μ ∫_ℝ e^{-μt}‖N(t)‖ dt`. -/
theorem complementary_response_bound {N : ℝ → ℂ} {μ Cμ : ℝ} (hCμ : 0 ≤ Cμ)
    (hint : Integrable (fun t => exp (-μ * t) * ‖N t‖)) {Q : ℝ → ℝ}
    (hQ : ∀ s, Q s ≤ Cμ * exp (μ * s) * ∫ t in Iic s, exp (-μ * t) * ‖N t‖) (s : ℝ) :
    Q s ≤ (Cμ * ∫ t, exp (-μ * t) * ‖N t‖) * exp (μ * s) := by
  refine (hQ s).trans ?_
  have hle : ∫ t in Iic s, exp (-μ * t) * ‖N t‖ ≤ ∫ t, exp (-μ * t) * ‖N t‖ :=
    setIntegral_le_integral hint (Eventually.of_forall fun t => by positivity)
  have : 0 ≤ Cμ * exp (μ * s) := by positivity
  nlinarith

/-- **Corollary `re:cor:cone`, canonical cone.** If the complementary part is at most
`C e^{μs}` and the growing part is eventually at least `c e^{bσs}` with `c > 0` and `μ < bσ`,
then for every aperture `ϑ > 0` the canonical response lies in the cone
`Q(s) ≤ ϑ P(s)` for all sufficiently large `s`. -/
theorem canonical_cone_eventually {Q P : ℝ → ℝ} {C c μ ν : ℝ} (hc : 0 < c) (hμν : μ < ν)
    (hQ : ∀ s, Q s ≤ C * exp (μ * s)) (hP : ∀ᶠ s in atTop, c * exp (ν * s) ≤ P s)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∀ᶠ s in atTop, Q s ≤ ϑ * P s := by
  have hlim : Tendsto (fun s => exp ((μ - ν) * s)) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith) |>.congr (fun _ => rfl)
  have hev : ∀ᶠ s in atTop, C * exp ((μ - ν) * s) ≤ ϑ * c := by
    have : Tendsto (fun s => C * exp ((μ - ν) * s)) atTop (𝓝 0) := by
      simpa using hlim.const_mul C
    exact this.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hev, hP] with s h1 h2
  have he : exp (μ * s) = exp ((μ - ν) * s) * exp (ν * s) := by
    rw [← exp_add]; ring_nf
  calc Q s ≤ C * exp (μ * s) := hQ s
    _ = C * exp ((μ - ν) * s) * exp (ν * s) := by rw [he]; ring
    _ ≤ ϑ * c * exp (ν * s) := mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = ϑ * (c * exp (ν * s)) := by ring
    _ ≤ ϑ * P s := mul_le_mul_of_nonneg_left h2 hϑ.le

/-- **Corollary `re:cor:cone`, openness of the strict cone.** Let `P` be a bounded projection
(any continuous linear map suffices) and suppose the canonical response `Y` satisfies
`‖(I - P) Y‖ ≤ ϑ ‖P Y‖` with `P Y ≠ 0`. For every larger aperture `ϑ' > ϑ` there is `δ > 0`
such that every `x` with `‖ρ⁻⁶ x - Y‖ < δ`, `ρ > 0`, lies in the strict cone
`‖(I - P) x‖ < ϑ' ‖P x‖`. -/
theorem entrance_cone_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) {Y : E} {ϑ ϑ' : ℝ} (hY : ‖Y - P Y‖ ≤ ϑ * ‖P Y‖) (hPY : P Y ≠ 0)
    (hϑ : ϑ < ϑ') :
    ∃ δ > 0, ∀ (ρ : ℝ) (x : E), 0 < ρ → ‖(ρ ^ 6)⁻¹ • x - Y‖ < δ →
      ‖x - P x‖ < ϑ' * ‖P x‖ := by
  set f : E → ℝ := fun z => ϑ' * ‖P z‖ - ‖z - P z‖ with hf
  have hcont : Continuous f := by
    simp only [hf]; fun_prop
  have hpos : 0 < f Y := by
    have : 0 < ‖P Y‖ := norm_pos_iff.mpr hPY
    simp only [hf]; nlinarith
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hcont) Y hpos
  refine ⟨δ, hδ, fun ρ x hρ hx => ?_⟩
  have hmem : f ((ρ ^ 6)⁻¹ • x) > 0 := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hx)
  have hc : 0 < (ρ ^ 6)⁻¹ := inv_pos.mpr (pow_pos hρ 6)
  simp only [hf, map_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hc.le] at hmem
  have : (ρ ^ 6)⁻¹ * ‖x - P x‖ < (ρ ^ 6)⁻¹ * (ϑ' * ‖P x‖) := by linarith
  exact lt_of_mul_lt_mul_left this hc.le

end Euler2D
