module

public import RequestProject.Euler.Envelope
public import RequestProject.Euler.Survival

/-!
# Reset and causal bounds (Corollary `ca:cor:reset`)

Consequences of the envelope estimate of Theorem `ca:thm:envelope` used at the change of the
current index. With `E(t) = E₀ e^{σt}`, `h = C₀ρ⁶` and `bσ ≤ ν ≤ ν̄ < σ`:

* `integral_exp_envelope_le`: `∫₀ᵗ e^{ν(t-s)} E(s) ds ≤ E(t)/(σ - ν̄)`;
* `integral_exp_poly_le`: `∫₀ᵗ e^{ν(t-s)} (1+s)⁴ ds ≤ C_b e^{νt}`, uniformly in `ν ≥ bσ`;
* `reset_estimate` (`ca:eq:reset`): `h Z(D) ≤ h M e^{νD} Z(0) + M C_int ρ⁶ δ/(σ - ν̄) +
  h M ∫₀ᴰ e^{ν(D-s)} 𝓡(s) ds` when `E(D) ≤ δ`;
* `reset_contraction` (`ca:eq:Breset`): `h M e^{νD} ≤ C ρ^{6(1 - ν̄/σ)}` when
  `D ≤ 6σ⁻¹ log(1/ρ) + D₀`;
* `causal_bound` (`ca:eq:causal`): if `𝓡(t) ≤ Cρ⁶(1+t)⁴` and `Z(0) ≤ Kh` then
  `Z(t) ≤ C_a E(t) + C_a (K+1) h e^{νt}` with `C_a` independent of `K`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Euler2D

/-- `∫₀ᵗ e^{ν(t-s)} E₀ e^{σs} ds ≤ E₀ e^{σt}/(σ - ν̄)` for `ν ≤ ν̄ < σ`, `E₀ ≥ 0`. -/
theorem integral_exp_envelope_le {σ ν νbar E₀ t : ℝ} (hν : ν ≤ νbar) (hνσ : νbar < σ)
    (hE₀ : 0 ≤ E₀) :
    ∫ s in (0)..t, exp (ν * (t - s)) * (E₀ * exp (σ * s)) ≤ E₀ * exp (σ * t) / (σ - νbar) := by
  have hd : 0 < σ - ν := by linarith
  have hd' : 0 < σ - νbar := by linarith
  have heq : ∀ s, exp (ν * (t - s)) * (E₀ * exp (σ * s)) =
      E₀ * exp (ν * t) * exp ((σ - ν) * s) := fun s => by
    rw [show ν * (t - s) = ν * t + -ν * s by ring, exp_add,
      show (σ - ν) * s = σ * s + -ν * s by ring, exp_add]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => exp x) hd.ne', integral_exp]
  simp only [mul_zero, exp_zero, smul_eq_mul]
  have h1 : exp (ν * t) * exp ((σ - ν) * t) = exp (σ * t) := by rw [← exp_add]; ring_nf
  have h2 : 0 ≤ E₀ * exp (σ * t) := by positivity
  calc E₀ * exp (ν * t) * ((σ - ν)⁻¹ * (exp ((σ - ν) * t) - 1))
      ≤ E₀ * exp (ν * t) * ((σ - ν)⁻¹ * exp ((σ - ν) * t)) := by
        gcongr; linarith
    _ = E₀ * exp (σ * t) / (σ - ν) := by rw [← h1]; field_simp
    _ ≤ E₀ * exp (σ * t) / (σ - νbar) :=
        div_le_div_of_nonneg_left h2 hd' (by linarith)

/-- `∫₀ᵗ e^{ν(t-s)} (1+s)⁴ ds ≤ C e^{νt}`, with `C` depending only on a lower bound `ν₀ > 0`
for `ν`. -/
theorem integral_exp_poly_le {ν₀ : ℝ} (hν₀ : 0 < ν₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν t : ℝ, ν₀ ≤ ν → 0 ≤ t →
      ∫ s in (0)..t, exp (ν * (t - s)) * (1 + s) ^ 4 ≤ C * exp (ν * t) := by
  obtain ⟨C', hC'pos, hC'⟩ := exists_rpow_le_exp (d := 4) (half_pos hν₀)
  refine ⟨C' * (1 / (ν₀ / 2)), by positivity, fun ν t hν ht => ?_⟩
  have hpt : ∀ s ∈ Icc 0 t, exp (ν * (t - s)) * (1 + s) ^ 4 ≤
      exp (ν * t) * C' * exp (-(ν₀ / 2) * (s - 0)) := by
    intro s hs
    have h4 := hC' s hs.1
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h4
    have he : exp (ν * (t - s)) ≤ exp (ν * t) * exp (-ν₀ * s) := by
      rw [← exp_add]; apply exp_le_exp.mpr; nlinarith [hs.1]
    calc exp (ν * (t - s)) * (1 + s) ^ 4
        ≤ (exp (ν * t) * exp (-ν₀ * s)) * (C' * exp (ν₀ / 2 * s)) :=
          mul_le_mul he h4 (by positivity) (by positivity)
      _ = exp (ν * t) * C' * (exp (-ν₀ * s) * exp (ν₀ / 2 * s)) := by ring
      _ = exp (ν * t) * C' * exp (-(ν₀ / 2) * (s - 0)) := by rw [← exp_add]; ring_nf
  calc ∫ s in (0)..t, exp (ν * (t - s)) * (1 + s) ^ 4
      ≤ ∫ s in (0)..t, exp (ν * t) * C' * exp (-(ν₀ / 2) * (s - 0)) :=
        intervalIntegral.integral_mono_on ht (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop) hpt
    _ = exp (ν * t) * C' * ∫ s in (0)..t, exp (-(ν₀ / 2) * (s - 0)) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ exp (ν * t) * C' * (1 / (ν₀ / 2)) :=
        mul_le_mul_of_nonneg_left (integral_exp_neg_le (half_pos hν₀)) (by positivity)
    _ = C' * (1 / (ν₀ / 2)) * exp (ν * t) := by ring

/-- **Corollary `ca:cor:reset`, estimate `ca:eq:reset`.** -/
theorem reset_estimate {σ ν νbar M Cint C₀ ρ E₀ δ D Z₀ ZD : ℝ} {R : ℝ → ℝ}
    (hν : ν ≤ νbar) (hνσ : νbar < σ) (hM : 0 ≤ M) (hC : 0 ≤ Cint) (hC₀ : 0 < C₀)
    (hρ : 0 < ρ) (hE₀ : 0 ≤ E₀) (hδ : E₀ * exp (σ * D) ≤ δ)
    (hZ : ZD ≤ M * exp (ν * D) * Z₀ +
      M * Cint / C₀ * (∫ s in (0)..D, exp (ν * (D - s)) * (E₀ * exp (σ * s))) +
      M * (∫ s in (0)..D, exp (ν * (D - s)) * R s)) :
    C₀ * ρ ^ 6 * ZD ≤ C₀ * ρ ^ 6 * M * exp (ν * D) * Z₀ + M * Cint / (σ - νbar) * ρ ^ 6 * δ +
      C₀ * ρ ^ 6 * M * (∫ s in (0)..D, exp (ν * (D - s)) * R s) := by
  have hI := integral_exp_envelope_le (t := D) hν hνσ hE₀
  have hd' : 0 < σ - νbar := by linarith
  have hh : 0 ≤ C₀ * ρ ^ 6 := by positivity
  have hE : M * Cint / C₀ * (∫ s in (0)..D, exp (ν * (D - s)) * (E₀ * exp (σ * s))) ≤
      M * Cint / C₀ * (δ / (σ - νbar)) := by
    refine mul_le_mul_of_nonneg_left (hI.trans ?_) (by positivity)
    exact div_le_div_of_nonneg_right hδ hd'.le
  have := mul_le_mul_of_nonneg_left hZ hh
  have e : C₀ * ρ ^ 6 * (M * Cint / C₀ * (δ / (σ - νbar))) = M * Cint / (σ - νbar) * ρ ^ 6 * δ := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hE hh]

/-- **Corollary `ca:cor:reset`, estimate `ca:eq:Breset`.** If `ρ > 0`, `0 ≤ ν ≤ ν̄` and
`0 ≤ D ≤ 6σ⁻¹ log(1/ρ) + D₀`, then `h M e^{νD} ≤ C₀ M e^{ν̄ D₀} ρ^{6(1 - ν̄/σ)}`. -/
theorem reset_contraction {σ ν νbar M C₀ ρ D D₀ : ℝ} (hσ : 0 < σ) (hν0 : 0 ≤ ν)
    (hν : ν ≤ νbar) (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀) (hρ0 : 0 < ρ) (hD : 0 ≤ D)
    (hDle : D ≤ 6 / σ * Real.log (1 / ρ) + D₀) :
    C₀ * ρ ^ 6 * M * exp (ν * D) ≤ C₀ * M * exp (νbar * D₀) * ρ ^ (6 * (1 - νbar / σ)) := by
  have hνbar : 0 ≤ νbar := hν0.trans hν
  have hlog : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
  have hρ6 : ρ ^ 6 = exp (6 * Real.log ρ) := by
    rw [show (6 : ℝ) * Real.log ρ = Real.log ρ * ((6 : ℕ) : ℝ) by push_cast; ring,
      ← Real.rpow_def_of_pos hρ0, Real.rpow_natCast]
  have hρr : ρ ^ (6 * (1 - νbar / σ)) = exp (Real.log ρ * (6 * (1 - νbar / σ))) :=
    Real.rpow_def_of_pos hρ0 _
  rw [hρ6, hρr]
  have hexp : exp (6 * Real.log ρ) * exp (ν * D) ≤
      exp (νbar * D₀) * exp (Real.log ρ * (6 * (1 - νbar / σ))) := by
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    have h1 : ν * D ≤ νbar * D := mul_le_mul_of_nonneg_right hν hD
    have h2 : νbar * D ≤ νbar * (6 / σ * Real.log (1 / ρ) + D₀) :=
      mul_le_mul_of_nonneg_left hDle hνbar
    rw [hlog] at h2
    have h3 : νbar * (6 / σ * -Real.log ρ + D₀) =
        νbar * D₀ + Real.log ρ * (6 * (1 - νbar / σ)) - 6 * Real.log ρ := by
      field_simp; ring
    linarith
  calc C₀ * exp (6 * Real.log ρ) * M * exp (ν * D)
      = C₀ * M * (exp (6 * Real.log ρ) * exp (ν * D)) := by ring
    _ ≤ C₀ * M * (exp (νbar * D₀) * exp (Real.log ρ * (6 * (1 - νbar / σ)))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

/-- **Corollary `ca:cor:reset`, estimate `ca:eq:causal`.** Once the gap `bσ ≤ ν ≤ ν̄ < σ` is
fixed, there is `C_a` (independent of `K`) such that, whenever the envelope bound of
Theorem `ca:thm:envelope` holds at time `t` with `E(s) = E₀e^{σs}`, `𝓡(s) ≤ Cρ⁶(1+s)⁴` and
`Z(0) ≤ Kh`, one has `Z(t) ≤ C_a E(t) + C_a (K+1) h e^{νt}`. -/
theorem causal_bound {σ b νbar M Cint C₀ C : ℝ} (hσ : 0 < σ) (hb : 0 < b) (hνσ : νbar < σ)
    (hM : 0 ≤ M) (hCint : 0 ≤ Cint) (hC₀ : 0 < C₀) (hC : 0 ≤ C) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ (ν K E₀ ρ t Z₀ Zt : ℝ) (R : ℝ → ℝ),
      b * σ ≤ ν → ν ≤ νbar → 0 ≤ K → 0 ≤ E₀ → 0 < ρ → 0 ≤ t →
      ContinuousOn R (Icc 0 t) → (∀ s ∈ Icc 0 t, R s ≤ C * ρ ^ 6 * (1 + s) ^ 4) →
      Z₀ ≤ K * (C₀ * ρ ^ 6) →
      Zt ≤ M * exp (ν * t) * Z₀ +
        M * Cint / C₀ * (∫ s in (0)..t, exp (ν * (t - s)) * (E₀ * exp (σ * s))) +
        M * (∫ s in (0)..t, exp (ν * (t - s)) * R s) →
      Zt ≤ Ca * (E₀ * exp (σ * t)) + Ca * (K + 1) * (C₀ * ρ ^ 6) * exp (ν * t) := by
  obtain ⟨Cb, hCb0, hCb⟩ := integral_exp_poly_le (mul_pos hb hσ)
  have hd' : 0 < σ - νbar := by linarith
  set A1 : ℝ := M * Cint / (C₀ * (σ - νbar))
  set A2 : ℝ := M + M * C * Cb / C₀
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  refine ⟨A1 + A2, by positivity, ?_⟩
  intro ν K E₀ ρ t Z₀ Zt R hbν hν hK hE₀ hρ ht hRc hR hZ₀ hZ
  have hνσ' : ν ≤ νbar := hν
  have hh : 0 < C₀ * ρ ^ 6 := by positivity
  have he : 0 < exp (ν * t) := exp_pos _
  -- the three terms
  have t1 : M * exp (ν * t) * Z₀ ≤ M * (K + 1) * (C₀ * ρ ^ 6) * exp (ν * t) := by
    have : Z₀ ≤ (K + 1) * (C₀ * ρ ^ 6) := hZ₀.trans (by nlinarith)
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hM he.le)
    linarith
  have t2 : M * Cint / C₀ * (∫ s in (0)..t, exp (ν * (t - s)) * (E₀ * exp (σ * s))) ≤
      A1 * (E₀ * exp (σ * t)) := by
    have hI := integral_exp_envelope_le (t := t) hν hνσ hE₀
    calc M * Cint / C₀ * (∫ s in (0)..t, exp (ν * (t - s)) * (E₀ * exp (σ * s)))
        ≤ M * Cint / C₀ * (E₀ * exp (σ * t) / (σ - νbar)) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = A1 * (E₀ * exp (σ * t)) := by simp only [A1]; field_simp
  have t3 : M * (∫ s in (0)..t, exp (ν * (t - s)) * R s) ≤
      M * C * Cb / C₀ * (K + 1) * (C₀ * ρ ^ 6) * exp (ν * t) := by
    have hmono : ∫ s in (0)..t, exp (ν * (t - s)) * R s ≤
        ∫ s in (0)..t, C * ρ ^ 6 * (exp (ν * (t - s)) * (1 + s) ^ 4) := by
      refine intervalIntegral.integral_mono_on ht ?_ (by apply Continuous.intervalIntegrable; fun_prop) ?_
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht]
        exact ContinuousOn.mul (by fun_prop) hRc
      · intro s hs
        have := mul_le_mul_of_nonneg_left (hR s hs) (exp_pos (ν * (t - s))).le
        linarith
    rw [intervalIntegral.integral_const_mul] at hmono
    have hpoly := hCb ν t hbν ht
    have hK1 : 1 ≤ K + 1 := by linarith
    calc M * (∫ s in (0)..t, exp (ν * (t - s)) * R s)
        ≤ M * (C * ρ ^ 6 * (Cb * exp (ν * t))) := by
          refine mul_le_mul_of_nonneg_left (hmono.trans ?_) hM
          exact mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = M * C * Cb / C₀ * 1 * (C₀ * ρ ^ 6) * exp (ν * t) := by field_simp
      _ ≤ M * C * Cb / C₀ * (K + 1) * (C₀ * ρ ^ 6) * exp (ν * t) := by gcongr
  have hEt : 0 ≤ E₀ * exp (σ * t) := by positivity
  have hrest : 0 ≤ (K + 1) * (C₀ * ρ ^ 6) * exp (ν * t) := by positivity
  calc Zt ≤ _ := hZ
    _ ≤ M * (K + 1) * (C₀ * ρ ^ 6) * exp (ν * t) + A1 * (E₀ * exp (σ * t)) +
        M * C * Cb / C₀ * (K + 1) * (C₀ * ρ ^ 6) * exp (ν * t) := by linarith
    _ = A1 * (E₀ * exp (σ * t)) + A2 * ((K + 1) * (C₀ * ρ ^ 6) * exp (ν * t)) := by
        simp only [A2]; ring
    _ ≤ (A1 + A2) * (E₀ * exp (σ * t)) + (A1 + A2) * ((K + 1) * (C₀ * ρ ^ 6) * exp (ν * t)) := by
        nlinarith
    _ = _ := by ring

/-! ### Exact change of ancestor weights (Lemma `re:lem:reset`) -/

/-- `Z_k = max_{j<k} h^{-(k-j)} q_j`, with an empty maximum equal to zero. -/
noncomputable def ancestorMax (h : ℝ) (q : ℕ → ℝ) (k : ℕ) : ℝ :=
  ⨆ j : Fin k, (h ^ (k - (j : ℕ)))⁻¹ * q j

lemma le_ancestorMax (h : ℝ) (q : ℕ → ℝ) {k : ℕ} (j : Fin k) :
    (h ^ (k - (j : ℕ)))⁻¹ * q j ≤ ancestorMax h q k :=
  le_ciSup (f := fun j : Fin k => (h ^ (k - (j : ℕ)))⁻¹ * q j) (Set.finite_range _).bddAbove j

lemma ancestorMax_nonneg {h : ℝ} (hh : 0 < h) {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j) (k : ℕ) :
    0 ≤ ancestorMax h q k :=
  Real.iSup_nonneg fun j => mul_nonneg (inv_nonneg.mpr (pow_nonneg hh.le _)) (hq j)

/-- **Lemma (`re:lem:reset`).** Changing the current index from `k` to `k - 1` with the same
coordinates `q_j ≥ 0` gives `Z_{k-1} ≤ h Z_k`. -/
theorem ancestorMax_pred_le {h : ℝ} (hh : 0 < h) {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j) {k : ℕ}
    (hk : 1 ≤ k) : ancestorMax h q (k - 1) ≤ h * ancestorMax h q k := by
  apply Real.iSup_le _ (mul_nonneg hh.le (ancestorMax_nonneg hh hq k))
  intro j
  have hj : (j : ℕ) < k := by omega
  have := le_ancestorMax h q (⟨j, hj⟩ : Fin k)
  have e : (h ^ (k - 1 - (j : ℕ)))⁻¹ * q j = h * ((h ^ (k - (j : ℕ)))⁻¹ * q j) := by
    have : k - (j : ℕ) = (k - 1 - (j : ℕ)) + 1 := by omega
    rw [this, pow_succ]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left this hh.le

/-- **Lemma (`re:lem:reset`), consequences.** If `Z_k ≤ L` with `L > 0` and `K = 2L`, then
`Z_{k-1} ≤ Lh < Kh`; and if `Z_k ≤ Kh` then `q_{k-1} ≤ K h²`. -/
theorem ancestorMax_reset_consequences {h : ℝ} (hh : 0 < h) {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j)
    {k : ℕ} (hk : 1 ≤ k) {L K : ℝ} :
    (0 < L → ancestorMax h q k ≤ L → K = 2 * L →
      ancestorMax h q (k - 1) ≤ L * h ∧ L * h < K * h) ∧
    (ancestorMax h q k ≤ K * h → q (k - 1) ≤ K * h ^ 2) := by
  refine ⟨fun hL hZ hK => ⟨?_, ?_⟩, fun hZ => ?_⟩
  · calc ancestorMax h q (k - 1) ≤ h * ancestorMax h q k := ancestorMax_pred_le hh hq hk
      _ ≤ h * L := mul_le_mul_of_nonneg_left hZ hh.le
      _ = L * h := mul_comm _ _
  · rw [hK]; nlinarith
  · have := le_ancestorMax h q (⟨k - 1, by omega⟩ : Fin k)
    simp only [show k - (k - 1) = 1 by omega, pow_one] at this
    have h2 := this.trans hZ
    rw [inv_mul_le_iff₀ hh] at h2
    nlinarith

end Euler2D

end
