module

public import RequestProject.Euler.Laplace

/-!
# Survival of the retarded response (Theorem `nt:thm:survival`)

Let `λ = σ + iν`, `K ≠ 0`, `ϖ ∈ ℝ`, and let `N` satisfy the hypotheses of Theorem
`nt:thm:laplace` (`LaplaceHyp`). Fix `0 < b < 1` with `F_b = F(b(λ + iϖ)) ≠ 0` and let
`Y(s) = K e^{bλs} ∫_{-∞}^s e^{-b(λ+iϖ)t} N(t) dt` (`retardedSol`). For every `B ≥ 0` and
`ε > 0` (the paper takes `0 < ε < 1/2`) one can choose a finite `s₀ ≥ 0` such that every (mild) solution of
`W' = bλW + f` on `[s₀, S]` with `|f(s)| ≤ B(1+s)^d` and `|W(s₀) - Y(s₀)| ≤ ε|Y(s₀)|`
satisfies `|W(s)| ≥ (1 - 2ε)|Y(s₀)| e^{bσ(s-s₀)}`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Asymptotics

namespace Euler2D

/-- `(1+u)^d e^{-au} → 0` as `u → ∞`, for `a > 0`. -/
lemma tendsto_onePlus_rpow_mul_exp_neg (d : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u : ℝ => (1 + u) ^ d * Real.exp (-a * u)) atTop (𝓝 0) := by
  have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero d a ha).comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have := h0.mul_const (Real.exp a)
  rw [zero_mul] at this
  refine this.congr fun u => ?_
  simp only [Function.comp, id, mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- Polynomial growth is dominated by any exponential on `[0, ∞)`. -/
lemma exists_rpow_le_exp {d a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → (1 + u) ^ d ≤ C * Real.exp (a * u) := by
  set g : ℝ → ℝ := fun u => (1 + u) ^ d * Real.exp (-a * u) with hg
  have h1 : Tendsto g atTop (𝓝 0) := tendsto_onePlus_rpow_mul_exp_neg d ha
  obtain ⟨U, hU⟩ := eventually_atTop.mp (h1.eventually (ge_mem_nhds zero_lt_one))
  have hcont : ContinuousOn g (Icc 0 U) := by
    apply ContinuousOn.mul _ (by fun_prop)
    exact ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl (by linarith [hu.1])
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max 1 M, by positivity, fun u hu => ?_⟩
  have hgu : g u ≤ max 1 M := by
    rcases le_total u U with h | h
    · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM u ⟨hu, h⟩).trans (le_max_right _ _))
    · exact (hU u h).trans (le_max_left _ _)
  have : (1 + u) ^ d = g u * Real.exp (a * u) := by
    simp only [hg, mul_assoc, ← Real.exp_add]; simp
  rw [this]
  exact mul_le_mul_of_nonneg_right hgu (Real.exp_pos _).le

/-- The elementary integral `∫_{s₀}^{s} e^{-a(t-s₀)} dt ≤ 1/a`. -/
lemma integral_exp_neg_le {a s₀ s : ℝ} (ha : 0 < a) :
    ∫ t in s₀..s, Real.exp (-a * (t - s₀)) ≤ 1 / a := by
  have hderiv : ∀ t ∈ uIcc s₀ s,
      HasDerivAt (fun t => -Real.exp (-a * (t - s₀)) / a) (Real.exp (-a * (t - s₀))) t := by
    intro t _
    have h1 : HasDerivAt (fun t => -a * (t - s₀)) (-a) t := by
      simpa using ((hasDerivAt_id t).sub_const s₀).const_mul (-a)
    have := (h1.exp.neg).div_const a
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have : 0 < Real.exp (-a * (s - s₀)) := Real.exp_pos _
  simp only [sub_self, mul_zero, Real.exp_zero]
  rw [← sub_div, div_le_div_iff_of_pos_right ha]
  linarith

/-- `(1+t)^d ≤ (1+s₀)^d (1+(t-s₀))^d` for `0 ≤ s₀ ≤ t`, `d ≥ 0`. -/
lemma onePlus_rpow_split {d s₀ t : ℝ} (hd : 0 ≤ d) (hs₀ : 0 ≤ s₀) (ht : s₀ ≤ t) :
    (1 + t) ^ d ≤ (1 + s₀) ^ d * (1 + (t - s₀)) ^ d := by
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  exact Real.rpow_le_rpow (by linarith) (by nlinarith) hd

/-- Variation of constants: the forcing contributes at most `B (1+s₀)^d C (2/a)` to
`e^{-c(s-s₀)} W(s) - W(s₀)`, uniformly in `s ≥ s₀`. -/
lemma forcing_integral_bound {a d B C s₀ s : ℝ} {c : ℂ} (hc : c.re = a) (ha : 0 < a)
    (hd : 0 ≤ d) (hB : 0 ≤ B) (hs₀ : 0 ≤ s₀) (hs : s₀ ≤ s) {f : ℝ → ℂ}
    (hC : ∀ u : ℝ, 0 ≤ u → (1 + u) ^ d ≤ C * Real.exp (a / 2 * u))
    (hf : ∀ t ∈ Icc s₀ s, ‖f t‖ ≤ B * (1 + t) ^ d) :
    ‖∫ t in s₀..s, Complex.exp (c * (s₀ - t)) * f t‖ ≤ B * (1 + s₀) ^ d * C * (2 / a) := by
  have ha2 : 0 < a / 2 := by positivity
  calc ‖∫ t in s₀..s, Complex.exp (c * (s₀ - t)) * f t‖
      ≤ ∫ t in s₀..s, B * (1 + s₀) ^ d * C * Real.exp (-(a / 2) * (t - s₀)) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hs (Eventually.of_forall ?_)
          (by apply Continuous.intervalIntegrable; fun_prop)
        intro t ht
        have ht' : t ∈ Icc s₀ s := Ioc_subset_Icc_self ht
        rw [norm_mul, Complex.norm_exp]
        have hre : (c * (↑s₀ - ↑t)).re = a * (s₀ - t) := by
          simp [Complex.mul_re, hc]
        rw [hre]
        have h1 := hf t ht'
        have h2 := onePlus_rpow_split hd hs₀ ht'.1
        have h3 := hC (t - s₀) (by linarith [ht'.1])
        have hp : 0 ≤ (1 + s₀) ^ d := Real.rpow_nonneg (by linarith) _
        have hft : ‖f t‖ ≤ B * (1 + s₀) ^ d * C * Real.exp (a / 2 * (t - s₀)) := by
          calc ‖f t‖ ≤ B * (1 + t) ^ d := h1
            _ ≤ B * ((1 + s₀) ^ d * (1 + (t - s₀)) ^ d) := mul_le_mul_of_nonneg_left h2 hB
            _ ≤ B * ((1 + s₀) ^ d * (C * Real.exp (a / 2 * (t - s₀)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hp) hB
            _ = _ := by ring
        calc Real.exp (a * (s₀ - t)) * ‖f t‖
            ≤ Real.exp (a * (s₀ - t)) * (B * (1 + s₀) ^ d * C * Real.exp (a / 2 * (t - s₀))) :=
              mul_le_mul_of_nonneg_left hft (Real.exp_pos _).le
          _ = B * (1 + s₀) ^ d * C * (Real.exp (a * (s₀ - t)) * Real.exp (a / 2 * (t - s₀))) := by
              ring
          _ = _ := by rw [← Real.exp_add]; congr 2; ring
    _ = B * (1 + s₀) ^ d * C * ∫ t in s₀..s, Real.exp (-(a / 2) * (t - s₀)) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ B * (1 + s₀) ^ d * C * (1 / (a / 2)) := by
        have hC0 : 0 ≤ C := by
          have := hC 0 le_rfl
          simp at this
          by_contra h
          push_neg at h
          linarith [Real.exp_pos 0, mul_neg_of_neg_of_pos h (Real.exp_pos 0)]
        have hp : 0 ≤ (1 + s₀) ^ d := Real.rpow_nonneg (by linarith) _
        exact mul_le_mul_of_nonneg_left (integral_exp_neg_le ha2) (by positivity)
    _ = B * (1 + s₀) ^ d * C * (2 / a) := by congr 1; field_simp

/-- **Theorem (`nt:thm:survival`).** With `λ = σ + iν`, `c = bλ`, `z = b(λ + iϖ)` and
`Y = retardedSol c z K N`, for every `B ≥ 0` and `ε > 0` there is `s₀ ≥ 0` such that
`Y(s₀) ≠ 0` and every mild solution `W` of `W' = cW + f` on `[s₀, S]` with
`‖f(s)‖ ≤ B(1+s)^d` and `‖W(s₀) - Y(s₀)‖ ≤ ε‖Y(s₀)‖` satisfies
`‖W(s)‖ ≥ (1 - 2ε)‖Y(s₀)‖ e^{bσ(s-s₀)}` for `s ∈ [s₀, S]`. -/
theorem survival {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ} (hN : LaplaceHyp σ ν δ d κ N)
    {K : ℂ} (hK : K ≠ 0) (ϖ : ℝ) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hF : bilateral N ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) ≠ 0)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧
      retardedSol ((b : ℂ) * (σ + ν * Complex.I))
        ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) K N s₀ ≠ 0 ∧
      ∀ (S : ℝ) (W f : ℝ → ℂ),
        (∀ s ∈ Icc s₀ S, ‖f s‖ ≤ B * (1 + s) ^ d) →
        (∀ s ∈ Icc s₀ S, W s = Complex.exp ((b : ℂ) * (σ + ν * Complex.I) * (s - s₀)) * W s₀ +
          ∫ t in s₀..s, Complex.exp ((b : ℂ) * (σ + ν * Complex.I) * (s - t)) * f t) →
        ‖W s₀ - retardedSol ((b : ℂ) * (σ + ν * Complex.I))
            ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) K N s₀‖ ≤
          ε * ‖retardedSol ((b : ℂ) * (σ + ν * Complex.I))
            ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) K N s₀‖ →
        ∀ s ∈ Icc s₀ S,
          (1 - 2 * ε) * ‖retardedSol ((b : ℂ) * (σ + ν * Complex.I))
              ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) K N s₀‖ *
            Real.exp (b * σ * (s - s₀)) ≤ ‖W s‖ := by
  set c : ℂ := (b : ℂ) * (σ + ν * Complex.I) with hcdef
  set z : ℂ := (b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I) with hzdef
  set Y := retardedSol c z K N with hYdef
  have hσ := hN.sigma_pos
  have hd := hN.d_nonneg
  set a : ℝ := b * σ with hadef
  have ha : 0 < a := mul_pos hb0 hσ
  have hcre : c.re = a := by simp [hcdef, hadef]
  have hzre : z.re = a := by simp [hzdef, hadef]
  have hz0 : 0 < z.re := hzre ▸ ha
  have hz1 : z.re < σ := by rw [hzre]; nlinarith
  obtain ⟨-, -, hlim⟩ := retardedSol_spec hN.expWindow hz0 hz1 c K
  set L : ℂ := K * bilateral N z with hLdef
  have hL : 0 < ‖L‖ := norm_pos_iff.mpr (mul_ne_zero hK hF)
  have hnormexp : ∀ s : ℝ, ‖Complex.exp (-c * s)‖ = Real.exp (-a * s) := by
    intro s; rw [Complex.norm_exp]; simp [Complex.mul_re, hcre]
  have ev1 : ∀ᶠ s : ℝ in atTop, ‖L‖ / 2 < ‖Complex.exp (-c * s) * Y s‖ :=
    (hlim.norm).eventually (lt_mem_nhds (half_lt_self hL))
  obtain ⟨C, hCpos, hC⟩ := exists_rpow_le_exp (d := d) (half_pos ha)
  have ev2 : ∀ᶠ s : ℝ in atTop, B * (1 + s) ^ d * C * (2 / a) ≤ ε * (‖L‖ / 2) * Real.exp (a * s) := by
    have ht := (tendsto_onePlus_rpow_mul_exp_neg d ha).const_mul (B * C * (2 / a))
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε * (‖L‖ / 2)))]
      with s hs
    have he : Real.exp (-a * s) * Real.exp (a * s) = 1 := by
      rw [← Real.exp_add]; simp
    calc B * (1 + s) ^ d * C * (2 / a)
        = B * C * (2 / a) * ((1 + s) ^ d * Real.exp (-a * s)) * Real.exp (a * s) := by
          rw [mul_assoc _ _ (Real.exp (a * s)), mul_assoc _ (Real.exp _) _, he]; ring
      _ ≤ ε * (‖L‖ / 2) * Real.exp (a * s) :=
          mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
  obtain ⟨s₀, ⟨h1, h2⟩, hs₀⟩ := ((ev1.and ev2).and (eventually_ge_atTop 0)).exists
  have hYs₀ : ‖L‖ / 2 * Real.exp (a * s₀) < ‖Y s₀‖ := by
    rw [norm_mul (Complex.exp _), hnormexp] at h1
    have he : Real.exp (a * s₀) * Real.exp (-a * s₀) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖L‖ / 2 * Real.exp (a * s₀) < Real.exp (-a * s₀) * ‖Y s₀‖ * Real.exp (a * s₀) :=
          mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      _ = ‖Y s₀‖ := by rw [mul_comm, ← mul_assoc, he, one_mul]
  have hYpos : 0 < ‖Y s₀‖ := lt_trans (by positivity) hYs₀
  refine ⟨s₀, hs₀, norm_pos_iff.mp hYpos, ?_⟩
  intro S W f hf hmild hW s hs
  set I : ℂ := ∫ t in s₀..s, Complex.exp (c * (s₀ - t)) * f t with hIdef
  have hI : ‖I‖ ≤ ε * ‖Y s₀‖ := by
    have := forcing_integral_bound hcre ha hd hB hs₀ hs.1 hC
      (fun t ht => hf t ⟨ht.1, ht.2.trans hs.2⟩)
    refine this.trans (h2.trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hYs₀.le hε.le
  have hWs : W s = Complex.exp (c * (s - s₀)) * (W s₀ + I) := by
    rw [hmild s hs, mul_add, hIdef, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring
  have hnorm2 : ‖Complex.exp (c * (s - s₀))‖ = Real.exp (b * σ * (s - s₀)) := by
    rw [Complex.norm_exp]; simp [Complex.mul_re, hcre, hadef]
  rw [hWs, norm_mul, hnorm2, mul_comm _ (Real.exp _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have htri : ‖Y s₀‖ ≤ ‖W s₀ + I‖ + ‖W s₀ - Y s₀‖ + ‖I‖ := by
    have : Y s₀ = (W s₀ + I) - (W s₀ - Y s₀) - I := by ring
    calc ‖Y s₀‖ = ‖(W s₀ + I) - (W s₀ - Y s₀) - I‖ := by rw [← this]
      _ ≤ ‖(W s₀ + I) - (W s₀ - Y s₀)‖ + ‖I‖ := norm_sub_le _ _
      _ ≤ ‖W s₀ + I‖ + ‖W s₀ - Y s₀‖ + ‖I‖ := by gcongr; exact norm_sub_le _ _
  linarith

/-- **Lemma (Large-time growing response, `re:lem:asymptotic`).** With `λ = σ + iν`,
`c = bλ`, `z = b(λ + iϖ)`, `0 < b < 1` and `F_b = F(z)`, the retarded response
`Y(s) = K e^{cs} ∫_{-∞}^s e^{-zt} N(t) dt` satisfies `Y(s) = K F_b e^{cs} + O((1+s)^d)` as
`s → +∞`, and, if `K F_b ≠ 0`, `|Y(s)| ≥ ½ |K F_b| e^{bσs}` for all sufficiently large `s`.
(The paper's case is `λ = λ_*`, `ϖ = 2`, `d = 4`, `K = K_*`.) -/
theorem growing_response_asymptotics {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (hN : LaplaceHyp σ ν δ d κ N) (K : ℂ) (ϖ : ℝ) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∃ C : ℝ, ∀ s : ℝ, 0 ≤ s →
      ‖retardedSol ((b : ℂ) * (σ + ν * Complex.I))
          ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) K N s -
        K * bilateral N ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) *
          Complex.exp ((b : ℂ) * (σ + ν * Complex.I) * s)‖ ≤ C * (1 + s) ^ d) ∧
    (K * bilateral N ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) ≠ 0 →
      ∀ᶠ s in atTop, ‖K * bilateral N ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I))‖ / 2 *
          Real.exp (b * σ * s) ≤
        ‖retardedSol ((b : ℂ) * (σ + ν * Complex.I))
          ((b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I)) K N s‖) := by
  set c : ℂ := (b : ℂ) * (σ + ν * Complex.I) with hcdef
  set z : ℂ := (b : ℂ) * ((σ + ν * Complex.I) + ϖ * Complex.I) with hzdef
  have hσ := hN.sigma_pos
  have hd := hN.d_nonneg
  set a : ℝ := b * σ with hadef
  have ha : 0 < a := mul_pos hb0 hσ
  have hcre : c.re = a := by simp [hcdef, hadef]
  have hzre : z.re = a := by simp [hzdef, hadef]
  have hz0 : 0 < z.re := hzre ▸ ha
  have hz1 : z.re < σ := by rw [hzre]; nlinarith
  have hg := hN.expWindow.integrable_exp hz0 hz1
  have hnormc : ∀ s : ℝ, ‖Complex.exp (c * s)‖ = Real.exp (a * s) := by
    intro s; rw [Complex.norm_exp]; simp [Complex.mul_re, hcre]
  refine ⟨?_, ?_⟩
  · obtain ⟨C0, hC0⟩ := hN.top
    obtain ⟨C1, hC1pos, hC1⟩ := exists_rpow_le_exp (d := d) (half_pos ha)
    refine ⟨‖K‖ * (max C0 0 * C1 * (2 / a)), fun s hs => ?_⟩
    have hsplit : ∫ t in Iic s, Complex.exp (-z * t) * N t =
        bilateral N z - ∫ t in Ioi s, Complex.exp (-z * t) * N t := by
      rw [bilateral, ← intervalIntegral.integral_Iic_add_Ioi hg.integrableOn hg.integrableOn]; ring
    have hdiff : retardedSol c z K N s - K * bilateral N z * Complex.exp (c * s) =
        -(K * Complex.exp (c * s) * ∫ t in Ioi s, Complex.exp (-z * t) * N t) := by
      simp only [retardedSol]; rw [hsplit]; ring
    have htail : ‖∫ t in Ioi s, Complex.exp (-z * t) * N t‖ ≤
        max C0 0 * C1 * (1 + s) ^ d * Real.exp (-(a / 2) * s) * (Real.exp (-(a / 2) * s) / (a / 2)) := by
      have hint : IntegrableOn (fun t => max C0 0 * C1 * (1 + s) ^ d * Real.exp (-(a / 2) * s) *
          Real.exp (-(a / 2) * t)) (Ioi s) :=
        (exp_neg_integrableOn_Ioi s (half_pos ha)).const_mul _
      calc ‖∫ t in Ioi s, Complex.exp (-z * t) * N t‖
          ≤ ∫ t in Ioi s, max C0 0 * C1 * (1 + s) ^ d * Real.exp (-(a / 2) * s) *
              Real.exp (-(a / 2) * t) := by
            refine norm_integral_le_of_norm_le hint ?_
            rw [ae_restrict_iff' measurableSet_Ioi]
            refine Eventually.of_forall fun t ht => ?_
            have ht' : s < t := ht
            rw [norm_mul, Complex.norm_exp]
            have hre : (-z * (t : ℂ)).re = -a * t := by simp [Complex.mul_re, hzre]
            rw [hre]
            have hNt : ‖N t‖ ≤ max C0 0 * (1 + t) ^ d :=
              (hC0 t (by linarith)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Real.rpow_nonneg (by linarith) _))
            have hsplit' := onePlus_rpow_split hd hs ht'.le
            have h1 := hC1 (t - s) (by linarith)
            have hps : 0 ≤ (1 + s) ^ d := Real.rpow_nonneg (by linarith) _
            have hM0 : 0 ≤ max C0 0 := le_max_right _ _
            calc Real.exp (-a * t) * ‖N t‖
                ≤ Real.exp (-a * t) * (max C0 0 * ((1 + s) ^ d * (C1 * Real.exp (a / 2 * (t - s))))) := by
                  refine mul_le_mul_of_nonneg_left (hNt.trans ?_) (Real.exp_pos _).le
                  refine mul_le_mul_of_nonneg_left (hsplit'.trans ?_) hM0
                  exact mul_le_mul_of_nonneg_left h1 hps
              _ = max C0 0 * C1 * (1 + s) ^ d *
                  (Real.exp (-a * t) * Real.exp (a / 2 * (t - s))) := by ring
              _ = max C0 0 * C1 * (1 + s) ^ d * Real.exp (-(a / 2) * s) * Real.exp (-(a / 2) * t) := by
                  rw [mul_assoc _ (Real.exp (-(a / 2) * s)), ← Real.exp_add, ← Real.exp_add]
                  congr 2; ring
        _ = max C0 0 * C1 * (1 + s) ^ d * Real.exp (-(a / 2) * s) *
              (Real.exp (-(a / 2) * s) / (a / 2)) := by
            rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
            congr 1; field_simp
    rw [hdiff, norm_neg, norm_mul, norm_mul, hnormc]
    have hexp : Real.exp (a * s) * (Real.exp (-(a / 2) * s) * Real.exp (-(a / 2) * s)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; simp; ring_nf
    calc ‖K‖ * Real.exp (a * s) * ‖∫ t in Ioi s, Complex.exp (-z * t) * N t‖
        ≤ ‖K‖ * Real.exp (a * s) * (max C0 0 * C1 * (1 + s) ^ d * Real.exp (-(a / 2) * s) *
            (Real.exp (-(a / 2) * s) / (a / 2))) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = ‖K‖ * (max C0 0 * C1 * (2 / a)) * (1 + s) ^ d *
            (Real.exp (a * s) * (Real.exp (-(a / 2) * s) * Real.exp (-(a / 2) * s))) := by
          field_simp
      _ = ‖K‖ * (max C0 0 * C1 * (2 / a)) * (1 + s) ^ d := by rw [hexp, mul_one]
  · intro hKF
    obtain ⟨-, -, hlim⟩ := retardedSol_spec hN.expWindow hz0 hz1 c K
    have hL : 0 < ‖K * bilateral N z‖ := norm_pos_iff.mpr hKF
    have ev : ∀ᶠ s : ℝ in atTop, ‖K * bilateral N z‖ / 2 < ‖Complex.exp (-c * s) * retardedSol c z K N s‖ :=
      (hlim.norm).eventually (lt_mem_nhds (half_lt_self hL))
    filter_upwards [ev] with s hs
    have hn : ‖Complex.exp (-c * s)‖ = Real.exp (-a * s) := by
      rw [Complex.norm_exp]; simp [Complex.mul_re, hcre]
    rw [norm_mul (Complex.exp _), hn] at hs
    have he : Real.exp (a * s) * Real.exp (-a * s) = 1 := by rw [← Real.exp_add]; simp
    calc ‖K * bilateral N z‖ / 2 * Real.exp (b * σ * s)
        ≤ Real.exp (-a * s) * ‖retardedSol c z K N s‖ * Real.exp (a * s) :=
          mul_le_mul_of_nonneg_right hs.le (Real.exp_pos _).le
      _ = ‖retardedSol c z K N s‖ := by rw [mul_comm, ← mul_assoc, he, one_mul]

end Euler2D

end
