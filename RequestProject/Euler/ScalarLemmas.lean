module

public import Mathlib

/-!
# Scalar lemmas of the paper

* Lemma `cs:lem:dini` (upper-derivative comparison),
* Lemma *Summed stage durations* (Section `part:cs`),
* Lemma `cp:lem:times` (uniform outer exit times), algebraic core,
* Lemma `ca:lem:gap` (uniform weighted spectral gap),
* Lemma `ca:lem:gronwall` (scalar convolution inequality).
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Euler2D

/-! ### Upper-derivative comparison -/

/-- **Lemma (Upper-derivative comparison).** Let `y, g` be continuous on `[0,T]`. If the upper
right Dini derivative satisfies `D⁺y(t) = limsup_{h↓0} (y(t+h) - y(t))/h ≤ g(t)` for every
`t < T` (stated as: for every `r > g(t)`, eventually for small `h > 0` the difference quotient
is `< r`), then `y(t) ≤ y(0) + ∫₀ᵗ g` on `[0,T]`. -/
theorem dini_comparison {y g : ℝ → ℝ} {T : ℝ} (hy : ContinuousOn y (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (hD : ∀ t ∈ Ico 0 T, ∀ r > g t, ∀ᶠ h in 𝓝[>] (0 : ℝ), (y (t + h) - y t) / h < r) :
    ∀ t ∈ Icc 0 T, y t ≤ y 0 + ∫ s in (0 : ℝ)..t, g s := by
  rcases lt_or_ge T 0 with hT | hT
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.mpr hT)
  -- continuous extension of `g` to all of `ℝ`
  set G : ℝ → ℝ := IccExtend hT (fun s : Icc 0 T => g s) with hGdef
  have hGc : Continuous G := by
    apply ContinuousOn.restrict hg |>.Icc_extend'
  have hGeq : ∀ s ∈ Icc 0 T, G s = g s := fun s hs => by
    simp [hGdef, IccExtend_of_mem _ _ hs]
  set B : ℝ → ℝ := fun t => y 0 + ∫ s in (0 : ℝ)..t, G s with hB
  have hBderiv : ∀ t, HasDerivAt B (G t) t := fun t =>
    (hGc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _
  have key : ∀ t ∈ Icc 0 T, y t ≤ B t := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hy (by simp [hB])
      (fun t _ => (hBderiv t).continuousAt.continuousWithinAt)
      (fun t _ => (hBderiv t).hasDerivWithinAt)
    intro t ht r hr
    rw [hGeq t (Ico_subset_Icc_self ht)] at hr
    have hev := hD t ht r hr
    have htend : Tendsto (fun z => z - t) (𝓝[>] t) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun z => z - t) (𝓝 t) (𝓝 (t - t)) := tendsto_id.sub_const t
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    have hev' := htend.eventually hev
    apply Eventually.frequently
    filter_upwards [hev'] with z hz
    rw [slope_def_field]
    simpa using hz
  intro t ht
  have := key t ht
  have hint : ∫ s in (0 : ℝ)..t, G s = ∫ s in (0 : ℝ)..t, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hGeq s ⟨hs.1, hs.2.trans ht.2⟩
  simpa [hB, hint] using this

/-! ### Summed stage durations -/

/-- **Lemma (Summed stage durations).** If `A_j⁻¹ = A_k⁻¹ b^{j-k}` and stage `j` has duration
at most `D/A_j`, the total duration of stages `k, …, N` is at most `D/((1-b)A_k)`, and that of
stages `k+1, …, N` is at most `D b/((1-b)A_k)`. -/
theorem summed_stage_durations {b D Ak : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hD : 0 ≤ D)
    (hAk : 0 < Ak) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), D * b ^ i / Ak ≤ D / ((1 - b) * Ak) ∧
      ∑ i ∈ Finset.range n, D * b ^ (i + 1) / Ak ≤ D * b / ((1 - b) * Ak) := by
  have hgeom : ∀ m : ℕ, ∑ i ∈ Finset.range m, b ^ i ≤ 1 / (1 - b) := by
    intro m
    have h1 : (∑ i ∈ Finset.range m, b ^ i) * (1 - b) = 1 - b ^ m := by
      rw [← neg_sub, mul_neg, geom_sum_mul]; ring
    rw [le_div_iff₀ (by linarith), h1]
    linarith [pow_nonneg hb0 m]
  constructor
  · rw [← Finset.sum_div, ← Finset.mul_sum, div_le_div_iff₀ hAk (by nlinarith)]
    have := hgeom (n + 1)
    rw [le_div_iff₀ (by linarith)] at this
    nlinarith [mul_le_mul_of_nonneg_left this hD]
  · rw [← Finset.sum_div, ← Finset.mul_sum, div_le_div_iff₀ hAk (by nlinarith)]
    have h := hgeom n
    have : ∑ i ∈ Finset.range n, b ^ (i + 1) = b * ∑ i ∈ Finset.range n, b ^ i := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this]
    rw [le_div_iff₀ (by linarith)] at h
    have := mul_le_mul_of_nonneg_left h (mul_nonneg hD hb0)
    nlinarith

/-- The scale functions used to choose `D = C log(1/ρ)`: `ρ(1 + log(1/ρ)) → 0` and
`ρ²(1 + log(1/ρ))³ → 0` as `ρ ↓ 0`. -/
theorem small_scale_limits :
    Tendsto (fun ρ : ℝ => ρ * (1 + Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ρ : ℝ => ρ ^ 2 * (1 + Real.log (1 / ρ)) ^ 3) (𝓝[>] 0) (𝓝 0) := by
  have base : ∀ r : ℝ, 0 < r →
      Tendsto (fun ρ : ℝ => ρ ^ r * (1 + Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) := by
    intro r hr
    have h1 := tendsto_log_mul_rpow_nhdsGT_zero hr
    have h2 : Tendsto (fun ρ : ℝ => ρ ^ r) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 r (Or.inr hr.le)).tendsto
      rw [Real.zero_rpow hr.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := h2.sub h1
    simp only [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    simp only [one_div, Real.log_inv]; ring
  constructor
  · refine (base 1 one_pos).congr' ?_
    filter_upwards with ρ; simp
  · have := (base (2 / 3) (by norm_num)).pow 3
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ : (0:ℝ) < ρ := hρ
    rw [mul_pow, ← Real.rpow_natCast (ρ ^ (2/3 : ℝ)), ← Real.rpow_mul hρ.le]
    norm_num

/-! ### Uniform outer exit times -/

/-- **Lemma (Uniform outer exit times), algebraic core.** With `0 ≤ b < 1`,
stage parameters `dₖ ∈ [D₋, D₊]` (`D₋ > 0`), terminal parameter `β ∈ [S - 1/2, S + 1/2]` with
`S ≥ 1/2`, and `s₀ ≥ 0`, the normalized exit time
`A₀ t₀ = b^N β + ∑_{k<N} b^k dₖ + s₀ ∑_{k<N} b^{k+1}` (with `N ≥ 1`) lies in
`[D₋, S + 1/2 + (D₊ + b s₀)/(1-b)]`, uniformly in `N`. -/
theorem exit_time_bounds {b Dm Dp S β s₀ : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hDm : 0 < Dm)
    (hS : 1 / 2 ≤ S) (hβ : β ∈ Icc (S - 1 / 2) (S + 1 / 2)) (hs₀ : 0 ≤ s₀)
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ → ℝ) (hd : ∀ k < N, d k ∈ Icc Dm Dp) :
    Dm ≤ b ^ N * β + ∑ k ∈ Finset.range N, b ^ k * d k +
        s₀ * ∑ k ∈ Finset.range N, b ^ (k + 1) ∧
      b ^ N * β + ∑ k ∈ Finset.range N, b ^ k * d k + s₀ * ∑ k ∈ Finset.range N, b ^ (k + 1) ≤
        S + 1 / 2 + (Dp + b * s₀) / (1 - b) := by
  have hβ0 : 0 ≤ β := by linarith [hβ.1]
  have hbN : 0 ≤ b ^ N := pow_nonneg hb0 N
  have hgeom : ∀ m : ℕ, ∑ i ∈ Finset.range m, b ^ i ≤ 1 / (1 - b) := by
    intro m
    have h1 : (∑ i ∈ Finset.range m, b ^ i) * (1 - b) = 1 - b ^ m := by
      rw [← neg_sub, mul_neg, geom_sum_mul]; ring
    rw [le_div_iff₀ (by linarith), h1]
    linarith [pow_nonneg hb0 m]
  have hs2 : 0 ≤ s₀ * ∑ k ∈ Finset.range N, b ^ (k + 1) :=
    mul_nonneg hs₀ (Finset.sum_nonneg fun k _ => pow_nonneg hb0 _)
  constructor
  · have h1 : Dm ≤ ∑ k ∈ Finset.range N, b ^ k * d k := by
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Finset.sum_range_succ']
      have h0 := hd 0 (by omega)
      have : 0 ≤ ∑ k ∈ Finset.range M, b ^ (k + 1) * d (k + 1) :=
        Finset.sum_nonneg fun k hk => mul_nonneg (pow_nonneg hb0 _)
          (hDm.le.trans (hd (k + 1) (by simp at hk; omega)).1)
      simp only [pow_zero, one_mul]
      linarith [h0.1]
    nlinarith
  · have hDp : 0 ≤ Dp := hDm.le.trans (hd 0 (by omega)).1 |>.trans (hd 0 (by omega)).2
    have h1 : b ^ N * β ≤ S + 1 / 2 := by
      have : b ^ N ≤ 1 := pow_le_one₀ hb0 hb1.le
      nlinarith [hβ.2]
    have h2 : ∑ k ∈ Finset.range N, b ^ k * d k ≤ Dp / (1 - b) := by
      calc ∑ k ∈ Finset.range N, b ^ k * d k ≤ ∑ k ∈ Finset.range N, b ^ k * Dp :=
            Finset.sum_le_sum fun k hk =>
              mul_le_mul_of_nonneg_left (hd k (Finset.mem_range.mp hk)).2 (pow_nonneg hb0 _)
        _ = Dp * ∑ k ∈ Finset.range N, b ^ k := by rw [Finset.mul_sum]; congr 1; ext; ring
        _ ≤ Dp * (1 / (1 - b)) := mul_le_mul_of_nonneg_left (hgeom N) hDp
        _ = Dp / (1 - b) := by ring
    have h3 : s₀ * ∑ k ∈ Finset.range N, b ^ (k + 1) ≤ b * s₀ / (1 - b) := by
      have : ∑ k ∈ Finset.range N, b ^ (k + 1) = b * ∑ k ∈ Finset.range N, b ^ k := by
        rw [Finset.mul_sum]; congr 1; ext; ring
      rw [this]
      calc s₀ * (b * ∑ k ∈ Finset.range N, b ^ k) ≤ s₀ * (b * (1 / (1 - b))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgeom N) hb0) hs₀
        _ = b * s₀ / (1 - b) := by ring
    have : (Dp + b * s₀) / (1 - b) = Dp / (1 - b) + b * s₀ / (1 - b) := add_div _ _ _
    linarith

/-! ### Uniform weighted spectral gap -/

/-- The exponent `ν` of Theorem `ca:thm:envelope`. -/
noncomputable def nuExp (b σ M Cint C₀ ζ da R : ℝ) : ℝ :=
  b * σ + M * Cint * b * (1 / (C₀ - 1) + ζ / (1 - ζ) + da + R ^ 8)

/-- **Lemma (Uniform weighted spectral gap), first part.** One can choose `C₀ > 1` with
`bσ + M C_int b/(C₀ - 1) < σ/3`. -/
theorem exists_C0_gap {b σ M Cint : ℝ} (hb0 : 0 < b) (hb : b < 1 / 4) (hσ : 0 < σ)
    (hM : 0 ≤ M) (hC : 0 ≤ Cint) :
    ∃ C₀ : ℝ, 1 < C₀ ∧ b * σ + M * Cint * b / (C₀ - 1) < σ / 3 := by
  set K := M * Cint * b
  have hK : 0 ≤ K := by positivity
  have hgap : 0 < σ / 3 - b * σ := by nlinarith
  refine ⟨1 + (K + 1) / (σ / 3 - b * σ), ?_, ?_⟩
  · have : 0 < (K + 1) / (σ / 3 - b * σ) := by positivity
    linarith
  · rw [show 1 + (K + 1) / (σ / 3 - b * σ) - 1 = (K + 1) / (σ / 3 - b * σ) by ring,
      div_div_eq_mul_div]
    have : K * (σ / 3 - b * σ) / (K + 1) < σ / 3 - b * σ := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith

/-- **Lemma (Uniform weighted spectral gap), second part.** Once `C₀` satisfies the gap
inequality and `L > 0` is fixed, with `h = C₀ρ⁶`, `ζ_ρ = C₀ρ⁸`, `R = ρ¹⁰` and `d_a = 2Lh`,
all sufficiently small `ρ > 0` satisfy `bσ ≤ ν ≤ ν̄ < σ/2` for a fixed `ν̄`. -/
theorem nu_gap {b σ M Cint C₀ L : ℝ} (hb0 : 0 < b) (hσ : 0 < σ) (hM : 0 ≤ M) (hC : 0 ≤ Cint)
    (hC₀ : 1 < C₀) (hL : 0 < L) (hgap : b * σ + M * Cint * b / (C₀ - 1) < σ / 3) :
    ∃ νbar < σ / 2, ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      b * σ ≤ nuExp b σ M Cint C₀ (C₀ * ρ ^ 8) (2 * L * (C₀ * ρ ^ 6)) (ρ ^ 10) ∧
        nuExp b σ M Cint C₀ (C₀ * ρ ^ 8) (2 * L * (C₀ * ρ ^ 6)) (ρ ^ 10) ≤ νbar := by
  refine ⟨σ / 3, by linarith, ?_⟩
  have hcont : ContinuousAt (fun ρ : ℝ =>
      nuExp b σ M Cint C₀ (C₀ * ρ ^ 8) (2 * L * (C₀ * ρ ^ 6)) (ρ ^ 10)) 0 := by
    unfold nuExp
    apply ContinuousAt.add continuousAt_const
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.add (ContinuousAt.add (ContinuousAt.add continuousAt_const _) _) (by fun_prop)
    · apply ContinuousAt.div (by fun_prop) (by fun_prop); simp
    · fun_prop
  have h0 : nuExp b σ M Cint C₀ (C₀ * 0 ^ 8) (2 * L * (C₀ * 0 ^ 6)) (0 ^ 10) =
      b * σ + M * Cint * b / (C₀ - 1) := by unfold nuExp; simp; ring
  have hev1 : ∀ᶠ ρ in 𝓝 (0 : ℝ),
      nuExp b σ M Cint C₀ (C₀ * ρ ^ 8) (2 * L * (C₀ * ρ ^ 6)) (ρ ^ 10) < σ / 3 := by
    have := hcont.eventually (gt_mem_nhds (h0 ▸ hgap))
    simpa using this
  have hev2 : ∀ᶠ ρ in 𝓝 (0 : ℝ), C₀ * ρ ^ 8 < 1 := by
    have : ContinuousAt (fun ρ : ℝ => C₀ * ρ ^ 8) 0 := by fun_prop
    exact this.eventually (gt_mem_nhds (by simp))
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
    with ρ h1 h2 h3
  refine ⟨?_, h1.le⟩
  unfold nuExp
  have hρ : 0 < ρ := h3
  have : 0 ≤ 1 / (C₀ - 1) + C₀ * ρ ^ 8 / (1 - C₀ * ρ ^ 8) + 2 * L * (C₀ * ρ ^ 6) +
      (ρ ^ 10) ^ 8 := by
    have : 0 < 1 - C₀ * ρ ^ 8 := by linarith
    have : 0 < C₀ - 1 := by linarith
    have : 0 < C₀ := by linarith
    positivity
  have : 0 ≤ M * Cint * b := by positivity
  nlinarith

/-! ### Scalar convolution (weighted Gronwall) inequality -/

/-- **Lemma (Scalar convolution inequality, `ca:lem:gronwall`).** If `d ≥ 0` and for all
`t ≥ 0`
`Z(t) ≤ A e^{ct} + ∫₀ᵗ e^{c(t-s)} (d Z(s) + g(s)) ds`,
then `Z(t) ≤ A e^{(c+d)t} + ∫₀ᵗ e^{(c+d)(t-s)} g(s) ds` for all `t ≥ 0`.

Formalization note: the paper takes `g` locally integrable; here `g` (like `Z`) is assumed
continuous. The sign conditions `Z, g, A ≥ 0` of the paper are not needed. -/
theorem scalar_convolution_gronwall {Z g : ℝ → ℝ} (hZ : Continuous Z) (hg : Continuous g)
    {A c d : ℝ} (hd : 0 ≤ d)
    (h : ∀ t, 0 ≤ t → Z t ≤ A * exp (c * t) + ∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s))
    {t : ℝ} (ht : 0 ≤ t) :
    Z t ≤ A * exp ((c + d) * t) + ∫ s in (0)..t, exp ((c + d) * (t - s)) * g s := by
  set z : ℝ → ℝ := fun s => exp (-c * s) * Z s
  set f : ℝ → ℝ := fun s => exp (-c * s) * g s
  have hz : Continuous z := by fun_prop
  have hf : Continuous f := by fun_prop
  set v : ℝ → ℝ := fun t => A + ∫ s in (0)..t, (d * z s + f s)
  have hzv : ∀ t, 0 ≤ t → z t ≤ v t := by
    intro t ht
    have h1 := h t ht
    have h2 : exp (-c * t) * (∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s)) =
        ∫ s in (0)..t, (d * z s + f s) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [z, f]
      have : exp (-c * t) * exp (c * (t - s)) = exp (-c * s) := by
        rw [← exp_add]; ring_nf
      rw [← mul_assoc, this]; ring
    have h3 : exp (-c * t) * (A * exp (c * t)) = A := by
      rw [mul_left_comm, ← exp_add]; simp
    have hpos : 0 < exp (-c * t) := exp_pos _
    calc z t = exp (-c * t) * Z t := rfl
      _ ≤ exp (-c * t) * (A * exp (c * t) + ∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s)) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = v t := by rw [mul_add, h3, h2]
  have hv : ∀ t, HasDerivAt v (d * z t + f t) t := fun t => by
    have := intervalIntegral.integral_hasDerivAt_right ((hz.const_smul d).add hf |>.intervalIntegrable 0 t)
      (((hz.const_smul d).add hf).stronglyMeasurableAtFilter _ _) ((hz.const_smul d).add hf).continuousAt
    simpa [v] using this.const_add A
  set W : ℝ → ℝ := fun t => exp (-d * t) * v t - ∫ s in (0)..t, exp (-d * s) * f s
  have hW : ∀ t, HasDerivAt W (exp (-d * t) * (d * z t + f t) + (-d * exp (-d * t)) * v t
      - exp (-d * t) * f t) t := fun t => by
    have he : HasDerivAt (fun t => exp (-d * t)) (-d * exp (-d * t)) t := by
      have := ((hasDerivAt_id t).const_mul (-d)).exp
      simpa [mul_comm] using this
    have hI := intervalIntegral.integral_hasDerivAt_right
      ((by fun_prop : Continuous fun s => exp (-d * s) * f s).intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun s => exp (-d * s) * f s).stronglyMeasurableAtFilter _ _)
      (by fun_prop : Continuous fun s => exp (-d * s) * f s).continuousAt
    have := (he.mul (hv t)).sub hI
    convert this using 1; ring
  have hWanti : AntitoneOn W (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.2 fun t => (hW t).continuousAt).continuousOn
    · exact fun t _ => (hW t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hW t).deriv]
      have := hzv t (le_of_lt ht)
      have hpos : 0 < exp (-d * t) := exp_pos _
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hd hpos.le)]
  have hW0 : W 0 = A := by simp [W, v]
  have hWt : W t ≤ A := hW0 ▸ hWanti (self_mem_Ici) ht ht
  -- `v t ≤ A e^{dt} + ∫ e^{d(t-s)} f`
  have hvt : v t ≤ A * exp (d * t) + ∫ s in (0)..t, exp (d * (t - s)) * f s := by
    have e1 : (∫ s in (0)..t, exp (d * (t - s)) * f s) =
        exp (d * t) * ∫ s in (0)..t, exp (-d * s) * f s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [show d * (t - s) = d * t + -d * s by ring, exp_add]; ring
    have hWt' : exp (-d * t) * v t ≤ A + ∫ s in (0)..t, exp (-d * s) * f s := by
      simp only [W] at hWt; linarith
    have := mul_le_mul_of_nonneg_left hWt' (exp_pos (d * t)).le
    rw [← mul_assoc, ← exp_add, show d * t + -d * t = 0 by ring, exp_zero, one_mul] at this
    rw [e1]; linarith
  have hZt : Z t = exp (c * t) * z t := by
    simp only [z]; rw [← mul_assoc, ← exp_add]; simp
  have e2 : (∫ s in (0)..t, exp ((c + d) * (t - s)) * g s) =
      exp (c * t) * ∫ s in (0)..t, exp (d * (t - s)) * f s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [f]
    rw [show exp (c * t) * (exp (d * (t - s)) * (exp (-c * s) * g s)) =
      (exp (c * t) * exp (d * (t - s)) * exp (-c * s)) * g s by ring, ← exp_add, ← exp_add]
    ring_nf
  rw [hZt, e2, show (c + d) * t = c * t + d * t by ring, exp_add]
  have := mul_le_mul_of_nonneg_left ((hzv t ht).trans hvt) (exp_pos (c * t)).le
  linarith

end Euler2D

end
