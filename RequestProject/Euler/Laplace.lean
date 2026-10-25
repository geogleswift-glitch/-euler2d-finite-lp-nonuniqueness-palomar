module

public import Mathlib

/-!
# The bilateral transform and a finite dominance time

Formalization of Section `part:nt` (*A nonzero fourth-moment response*), first part:

* Theorem `nt:thm:laplace`: the bilateral transform `F(z) = ∫_ℝ e^{-zs} N(s) ds` of a profile with
  leading exponential behaviour `κ e^{(σ+iν)s}` at `-∞` and polynomial growth at `+∞` is
  holomorphic on `0 < Re z < σ`, is not identically zero, and its zeros on a ray
  `z = b(σ + iβ)` do not accumulate in `0 < b < 1`;
* the lemma *Translation and phase invariance*;
* Lemma `nt:lem:retarded-normalization` (uniqueness of the retarded solution), and the
  existence/limit statement behind Proposition `nt:prop:transfer`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Asymptotics

namespace Euler2D

/-- A locally integrable profile `M` that is `O(e^{αs})` at `-∞` and `O(e^{εs})` at `+∞` for
every `ε > 0`; its bilateral transform converges on `0 < Re z < α`. -/
def ExpWindow (α : ℝ) (M : ℝ → ℂ) : Prop :=
  LocallyIntegrable M ∧ M =O[atBot] (fun s => Real.exp (α * s)) ∧
    ∀ ε > 0, M =O[atTop] (fun s => Real.exp (ε * s))

lemma abs_pow_isBigO_atTop (k : ℕ) {β : ℝ} (hβ : 0 < β) :
    (fun s : ℝ => |s| ^ k) =O[atTop] (fun s => Real.exp (β * s)) := by
  refine (isLittleO_pow_exp_pos_mul_atTop k hβ).isBigO.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 0] with s hs
  rw [abs_of_nonneg hs]

lemma abs_pow_isBigO_atBot (k : ℕ) {β : ℝ} (hβ : 0 < β) :
    (fun s : ℝ => |s| ^ k) =O[atBot] (fun s => Real.exp (-β * s)) := by
  have := (isLittleO_pow_exp_pos_mul_atTop k hβ).isBigO.comp_tendsto tendsto_neg_atBot_atTop
  refine this.congr' ?_ ?_
  · filter_upwards [eventually_le_atBot 0] with s hs
    simp [abs_of_nonpos hs]
  · filter_upwards with s; simp

lemma integrableAtFilter_exp_atBot {a : ℝ} (ha : 0 < a) :
    IntegrableAtFilter (fun s => Real.exp (a * s)) atBot volume :=
  ⟨Iic 0, Iic_mem_atBot 0, integrableOn_exp_mul_Iic ha 0⟩

lemma integrableAtFilter_exp_atTop {a : ℝ} (ha : 0 < a) :
    IntegrableAtFilter (fun s => Real.exp (-a * s)) atTop volume :=
  ⟨Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 ha⟩

lemma ExpWindow.integrable_weighted {α : ℝ} {M : ℝ → ℂ} (hM : ExpWindow α M) (k : ℕ) {c : ℝ}
    (hc0 : 0 < c) (hcα : c < α) :
    Integrable (fun s => |s| ^ k * Real.exp (-c * s) * ‖M s‖) := by
  obtain ⟨hloc, hbot, htop⟩ := hM
  have hl : LocallyIntegrable (fun s => |s| ^ k * Real.exp (-c * s) * ‖M s‖) := by
    rw [← locallyIntegrableOn_univ] at hloc ⊢
    exact hloc.norm.continuousOn_mul (by fun_prop) isClosed_univ.isLocallyClosed
  apply hl.integrable_of_isBigO_atBot_atTop (g := fun s => Real.exp (((α - c) / 2) * s))
    (g' := fun s => Real.exp (-(c / 4) * s))
  · have h1 := abs_pow_isBigO_atBot k (β := (α - c) / 2) (by linarith)
    have h2 := (isBigO_refl (fun s => Real.exp (-c * s)) atBot).mul hbot.norm_left
    have h3 := h1.mul h2
    refine (h3.congr_left fun s => by ring).trans (IsBigO.of_bound 1 ?_)
    filter_upwards with s
    simp only [Real.norm_eq_abs, Real.abs_exp, one_mul, ← Real.exp_add]
    apply le_of_eq; congr 1; ring
  · exact integrableAtFilter_exp_atBot (by linarith)
  · have h1 := abs_pow_isBigO_atTop k (β := c / 4) (by linarith)
    have h2 := (isBigO_refl (fun s => Real.exp (-c * s)) atTop).mul
      (htop (c / 2) (by linarith)).norm_left
    have h3 := h1.mul h2
    refine (h3.congr_left fun s => by ring).trans (IsBigO.of_bound 1 ?_)
    filter_upwards with s
    simp only [Real.norm_eq_abs, Real.abs_exp, one_mul, ← Real.exp_add]
    apply le_of_eq; congr 1; ring
  · exact integrableAtFilter_exp_atTop (by linarith)

/-- The bilateral (two-sided Laplace) transform `F(z) = ∫_ℝ e^{-zs} M(s) ds`. -/
noncomputable def bilateral (M : ℝ → ℂ) (z : ℂ) : ℂ := ∫ s : ℝ, Complex.exp (-z * s) * M s

lemma norm_cexp_neg_mul (z : ℂ) (s : ℝ) :
    ‖Complex.exp (-z * s)‖ = Real.exp (-z.re * s) := by
  rw [Complex.norm_exp]; simp

lemma ExpWindow.integrable_exp {α : ℝ} {M : ℝ → ℂ} (hM : ExpWindow α M) {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < α) :
    Integrable (fun s : ℝ => Complex.exp (-z * s) * M s) := by
  refine (hM.integrable_weighted 0 h0 h1).mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hM.1.aestronglyMeasurable
  · filter_upwards with s
    rw [norm_mul, norm_cexp_neg_mul]; simp

lemma exp_le_two_sided {x c v s : ℝ} (hx : |x - c| < v) :
    Real.exp (-x * s) ≤ Real.exp (-(c - v) * s) + Real.exp (-(c + v) * s) := by
  rw [abs_lt] at hx
  rcases le_total 0 s with hs | hs
  · have : Real.exp (-x * s) ≤ Real.exp (-(c - v) * s) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (-(c + v) * s)]
  · have : Real.exp (-x * s) ≤ Real.exp (-(c + v) * s) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (-(c - v) * s)]

lemma ExpWindow.hasDerivAt_bilateral {α : ℝ} {M : ℝ → ℂ} (hM : ExpWindow α M) {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < α) :
    HasDerivAt (bilateral M) (∫ s : ℝ, (-(s : ℂ)) * Complex.exp (-z * s) * M s) z := by
  obtain ⟨v, hv0, hv1, hv2⟩ : ∃ v : ℝ, 0 < v ∧ v < z.re ∧ v < α - z.re := by
    have hm : 0 < min z.re (α - z.re) := lt_min h0 (by linarith)
    refine ⟨min z.re (α - z.re) / 2, by positivity, ?_, ?_⟩ <;>
    · have := min_le_left z.re (α - z.re); have := min_le_right z.re (α - z.re)
      linarith
  set bound : ℝ → ℝ := fun s => |s| ^ 1 * Real.exp (-(z.re - v) * s) * ‖M s‖ +
    |s| ^ 1 * Real.exp (-(z.re + v) * s) * ‖M s‖
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun s : ℝ => Complex.exp (-w * s) * M s) :=
    fun w => (Continuous.aestronglyMeasurable (by fun_prop)).mul hM.1.aestronglyMeasurable
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w : ℂ => fun s : ℝ => Complex.exp (-w * s) * M s)
    (F' := fun w : ℂ => fun s : ℝ => (-(s : ℂ)) * Complex.exp (-w * s) * M s)
    (x₀ := z) (bound := bound) (Metric.ball_mem_nhds z hv0)
    (Eventually.of_forall fun w => hmeas w) (hM.integrable_exp h0 h1)
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul hM.1.aestronglyMeasurable) ?_ ?_ ?_
  · exact main.2
  · filter_upwards with s w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have hre : |w.re - z.re| < v := by
      rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans_lt hw
    rw [norm_mul, norm_mul, norm_cexp_neg_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have := exp_le_two_sided (s := s) hre
    have hM0 := norm_nonneg (M s)
    simp only [bound, pow_one]
    nlinarith [abs_nonneg s, mul_le_mul_of_nonneg_left this (mul_nonneg (abs_nonneg s) hM0)]
  · exact (hM.integrable_weighted 1 (by linarith) (by linarith)).add
      (hM.integrable_weighted 1 (by linarith) (by linarith))
  · filter_upwards with s w _
    show HasDerivAt (fun w : ℂ => Complex.exp (-w * s) * M s) _ w
    have : HasDerivAt (fun w : ℂ => Complex.exp (-w * s)) (Complex.exp (-w * s) * (-(s : ℂ))) w := by
      have h := ((hasDerivAt_id w).neg.mul_const (s : ℂ)).cexp
      simpa using h
    convert this.mul_const (M s) using 1
    ring

lemma ExpWindow.differentiableOn_bilateral {α : ℝ} {M : ℝ → ℂ} (hM : ExpWindow α M) :
    DifferentiableOn ℂ (bilateral M) {z : ℂ | 0 < z.re ∧ z.re < α} := fun _ hz =>
  (hM.hasDerivAt_bilateral hz.1 hz.2).differentiableAt.differentiableWithinAt


/-- Hypotheses of Theorem `nt:thm:laplace` on the profile `N`. -/
structure LaplaceHyp (σ ν δ d : ℝ) (κ : ℂ) (N : ℝ → ℂ) : Prop where
  sigma_pos : 0 < σ
  delta_pos : 0 < δ
  d_nonneg : 0 ≤ d
  kappa_ne : κ ≠ 0
  locInt : LocallyIntegrable N
  bot : (fun s : ℝ => N s - κ * Complex.exp ((σ + ν * Complex.I) * s)) =O[atBot]
    (fun s => Real.exp ((σ + δ) * s))
  top : ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → ‖N s‖ ≤ C * (1 + s) ^ d

lemma onePlus_rpow_isBigO {d ε : ℝ} (hε : 0 < ε) :
    (fun s : ℝ => (1 + s) ^ d) =O[atTop] (fun s => Real.exp (ε * s)) := by
  have h := (isLittleO_rpow_exp_pos_mul_atTop d hε).isBigO.comp_tendsto
    (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  refine h.trans ?_
  refine IsBigO.of_bound (Real.exp ε) ?_
  filter_upwards with s
  simp only [Function.comp, id, Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add]
  apply le_of_eq; congr 1; ring

lemma LaplaceHyp.top_isBigO {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ} (h : LaplaceHyp σ ν δ d κ N)
    {ε : ℝ} (hε : 0 < ε) : N =O[atTop] (fun s => Real.exp (ε * s)) := by
  obtain ⟨C, hC⟩ := h.top
  refine IsBigO.trans ?_ (onePlus_rpow_isBigO (d := d) hε)
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 0] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hC s hs

lemma exp_lead_isBigO (σ ν α : ℝ) (hα : α ≤ σ) :
    (fun s : ℝ => Complex.exp ((σ + ν * Complex.I) * s)) =O[atBot]
      (fun s => Real.exp (α * s)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_le_atBot 0] with s hs
  rw [Complex.norm_exp, Real.norm_eq_abs, Real.abs_exp, one_mul]
  apply Real.exp_le_exp.mpr
  simp
  nlinarith

lemma LaplaceHyp.expWindow {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ} (h : LaplaceHyp σ ν δ d κ N) :
    ExpWindow σ N := by
  refine ⟨h.locInt, ?_, fun ε hε => h.top_isBigO hε⟩
  have h1 : (fun s : ℝ => N s - κ * Complex.exp ((σ + ν * Complex.I) * s)) =O[atBot]
      (fun s => Real.exp (σ * s)) := by
    refine h.bot.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_le_atBot 0] with s hs
    simp only [Real.norm_eq_abs, Real.abs_exp, one_mul]
    exact Real.exp_le_exp.mpr (by nlinarith [h.delta_pos])
  have h2 := (exp_lead_isBigO σ ν σ le_rfl).const_mul_left κ
  exact (h1.add h2).congr_left fun s => by ring

/-- The remainder profile `Ñ = N - 1_{(-∞,0]} κ e^{z₀ s}`. -/
noncomputable def remainderProfile (σ ν : ℝ) (κ : ℂ) (N : ℝ → ℂ) (s : ℝ) : ℂ :=
  N s - (Iic (0 : ℝ)).indicator (fun t : ℝ => κ * Complex.exp ((σ + ν * Complex.I) * t)) s

lemma LaplaceHyp.remainder_expWindow {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (h : LaplaceHyp σ ν δ d κ N) : ExpWindow (σ + δ) (remainderProfile σ ν κ N) := by
  refine ⟨?_, ?_, fun ε hε => ?_⟩
  · exact h.locInt.sub ((Continuous.locallyIntegrable (by fun_prop)).indicator measurableSet_Iic)
  · refine h.bot.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_le_atBot 0] with s hs
    simp [remainderProfile, indicator_of_mem (show s ∈ Iic (0:ℝ) from hs)]
  · refine (h.top_isBigO hε).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp [remainderProfile, indicator_of_notMem (show s ∉ Iic (0:ℝ) from not_le.mpr hs)]

/-- Decomposition `F(z) = κ/(z₀ - z) + H(z)` on `0 < Re z < σ`. -/
lemma LaplaceHyp.decomp {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ} (h : LaplaceHyp σ ν δ d κ N)
    {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < σ) :
    bilateral N z = κ / ((σ + ν * Complex.I) - z) + bilateral (remainderProfile σ ν κ N) z := by
  set z₀ : ℂ := σ + ν * Complex.I
  have hre : 0 < (z₀ - z).re := by simp [z₀]; linarith
  have hI : IntegrableOn (fun s : ℝ => κ * Complex.exp ((z₀ - z) * s)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hre 0).const_mul κ
  have hsplit : (fun s : ℝ => Complex.exp (-z * s) * N s) =
      fun s : ℝ => Complex.exp (-z * s) * remainderProfile σ ν κ N s +
        (Iic (0:ℝ)).indicator (fun s : ℝ => κ * Complex.exp ((z₀ - z) * s)) s := by
    funext s
    simp only [remainderProfile]
    by_cases hs : s ∈ Iic (0:ℝ)
    · rw [indicator_of_mem hs, indicator_of_mem hs]
      have : Complex.exp (-z * s) * (κ * Complex.exp (z₀ * s)) =
          κ * Complex.exp ((z₀ - z) * s) := by
        rw [show (z₀ - z) * (s : ℂ) = -z * s + z₀ * s by ring, Complex.exp_add]; ring
      rw [mul_sub, this]; ring
    · simp [indicator_of_notMem hs]
  unfold bilateral
  rw [hsplit, integral_add ((h.remainder_expWindow).integrable_exp h0 (by linarith [h.delta_pos]))
    (hI.integrable_indicator measurableSet_Iic), integral_indicator measurableSet_Iic,
    integral_const_mul, integral_exp_mul_complex_Iic hre 0]
  simp [z₀]
  ring


/-- The auxiliary function `G(z) = κ + (z₀ - z) H(z)`, holomorphic on `0 < Re z < σ + δ`. -/
noncomputable def auxG (σ ν : ℝ) (κ : ℂ) (N : ℝ → ℂ) (z : ℂ) : ℂ :=
  κ + ((σ + ν * Complex.I) - z) * bilateral (remainderProfile σ ν κ N) z

lemma LaplaceHyp.auxG_analytic {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (h : LaplaceHyp σ ν δ d κ N) :
    AnalyticOnNhd ℂ (auxG σ ν κ N) {z : ℂ | 0 < z.re ∧ z.re < σ + δ} := by
  apply DifferentiableOn.analyticOnNhd _ ?_
  · have := h.remainder_expWindow.differentiableOn_bilateral
    exact (differentiableOn_const _).add ((differentiableOn_const _).sub differentiableOn_id
      |>.mul this)
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)

lemma strip_isPreconnected (c : ℝ) : IsPreconnected {z : ℂ | 0 < z.re ∧ z.re < c} :=
  ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt c)).isPreconnected

lemma LaplaceHyp.auxG_eq {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ} (h : LaplaceHyp σ ν δ d κ N)
    {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < σ) :
    auxG σ ν κ N z = ((σ + ν * Complex.I) - z) * bilateral N z := by
  have hne : (σ + ν * Complex.I) - z ≠ 0 := by
    intro h'; have := congrArg Complex.re h'; simp at this; linarith
  rw [h.decomp h0 h1, auxG, mul_add, mul_div_cancel₀ _ hne]

lemma LaplaceHyp.auxG_z0 {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ} (h : LaplaceHyp σ ν δ d κ N) :
    auxG σ ν κ N (σ + ν * Complex.I) ≠ 0 := by
  simp [auxG, h.kappa_ne]

/-- If `G` vanishes frequently near a point of the strip, contradiction. -/
lemma LaplaceHyp.auxG_not_frequently_zero {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (h : LaplaceHyp σ ν δ d κ N) {w : ℂ} (hw : 0 < w.re ∧ w.re < σ + δ) :
    ¬ ∃ᶠ z in 𝓝[≠] w, auxG σ ν κ N z = 0 := by
  intro hfr
  have := h.auxG_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (strip_isPreconnected _) hw hfr
  have hz0 : (σ + ν * Complex.I : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < σ + δ} := by
    simp [h.sigma_pos, h.delta_pos]
  exact h.auxG_z0 (this hz0)

/-- **Theorem (`nt:thm:laplace`).** Under the hypotheses `LaplaceHyp`, the bilateral transform
`F(z) = ∫_ℝ e^{-zs} N(s) ds` is holomorphic on `0 < Re z < σ`, is not identically zero there,
and for every `β` its zeros on the ray `z = b(σ + iβ)` have no accumulation point in
`0 < b < 1`. -/
theorem bilateral_laplace_theorem {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (h : LaplaceHyp σ ν δ d κ N) (β : ℝ) :
    DifferentiableOn ℂ (bilateral N) {z : ℂ | 0 < z.re ∧ z.re < σ} ∧
      (∃ z : ℂ, 0 < z.re ∧ z.re < σ ∧ bilateral N z ≠ 0) ∧
      ∀ b₀ ∈ Ioo (0 : ℝ) 1,
        ¬ ∃ᶠ b : ℝ in 𝓝[≠] b₀, bilateral N ((b : ℂ) * (σ + β * Complex.I)) = 0 := by
  have hσ := h.sigma_pos
  have hδ := h.delta_pos
  refine ⟨h.expWindow.differentiableOn_bilateral, ?_, ?_⟩
  · by_contra hall
    push_neg at hall
    -- `G` vanishes on a neighbourhood of `σ/2`
    set w : ℂ := ((σ / 2 : ℝ) : ℂ)
    have hw : 0 < w.re ∧ w.re < σ + δ := by
      refine ⟨?_, ?_⟩ <;> simp [w] <;> linarith
    apply h.auxG_not_frequently_zero hw
    apply Eventually.frequently
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < σ} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem : w ∈ {z : ℂ | 0 < z.re ∧ z.re < σ} := by
      refine ⟨?_, ?_⟩ <;> simp [w] <;> linarith
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem)] with z hz
    rw [h.auxG_eq hz.1 hz.2, hall z hz.1 hz.2, mul_zero]
  · intro b₀ hb₀ hfr
    set γ : ℝ → ℂ := fun b => (b : ℂ) * (σ + β * Complex.I)
    have hγ0 : (σ + β * Complex.I : ℂ) ≠ 0 := by
      intro h'; have := congrArg Complex.re h'; simp at this; linarith
    have hγc : Continuous γ := by fun_prop
    have htend : Tendsto γ (𝓝[≠] b₀) (𝓝[≠] (γ b₀)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (hγc.tendsto b₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with b hb
        simp only [mem_compl_iff, mem_singleton_iff, γ] at hb ⊢
        intro heq
        exact hb (by exact_mod_cast mul_right_cancel₀ hγ0 heq)
    have hev : ∀ᶠ b in 𝓝[≠] b₀, b ∈ Ioo (0 : ℝ) 1 :=
      nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hb₀)
    have hfr' : ∃ᶠ b in 𝓝[≠] b₀, auxG σ ν κ N (γ b) = 0 := by
      refine (hfr.and_eventually hev).mono fun b ⟨hb, hbI⟩ => ?_
      have hre : (γ b).re = b * σ := by simp [γ]
      rw [h.auxG_eq (by rw [hre]; nlinarith [hbI.1]) (by rw [hre]; nlinarith [hbI.2]),
        show γ b = b * (σ + β * Complex.I) from rfl, hb, mul_zero]
    have hw : 0 < (γ b₀).re ∧ (γ b₀).re < σ + δ := by
      simp only [γ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im]
      simp
      constructor <;> nlinarith [hb₀.1, hb₀.2]
    exact h.auxG_not_frequently_zero hw (htend.frequently hfr')

/-- **Definition (Fixed scale ratio), existence.** There is `b ∈ (0, 1/4)` with
`F(b(σ + iβ)) ≠ 0`, because a discrete subset cannot contain an interval. -/
theorem exists_scale_ratio {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (h : LaplaceHyp σ ν δ d κ N) (β : ℝ) :
    ∃ b ∈ Ioo (0 : ℝ) (1 / 4), bilateral N ((b : ℂ) * (σ + β * Complex.I)) ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply (bilateral_laplace_theorem h β).2.2 (1 / 8) ⟨by norm_num, by norm_num⟩
  apply Eventually.frequently
  filter_upwards [nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds
    (show (1 / 8 : ℝ) ∈ Ioo (0 : ℝ) (1 / 4) by constructor <;> norm_num))] with b hb
  exact hall b hb


/-- **Lemma (Translation and phase invariance).** If `Ñ(s) = e^{iϑ} N(s - s_*)` then
`F̃(z) = e^{iϑ - z s_*} F(z)`. -/
theorem bilateral_translate (N : ℝ → ℂ) (ϑ sStar : ℝ) (z : ℂ) :
    bilateral (fun s => Complex.exp (ϑ * Complex.I) * N (s - sStar)) z =
      Complex.exp (ϑ * Complex.I - z * sStar) * bilateral N z := by
  unfold bilateral
  have : (fun s : ℝ => Complex.exp (-z * s) * (Complex.exp (ϑ * Complex.I) * N (s - sStar))) =
      fun s => (fun u : ℝ => Complex.exp (ϑ * Complex.I - z * sStar) *
        (Complex.exp (-z * u) * N u)) (s - sStar) := by
    funext s
    simp only
    rw [show Complex.exp (ϑ * Complex.I - z * sStar) * (Complex.exp (-z * ((s - sStar : ℝ) : ℂ)) *
        N (s - sStar)) = (Complex.exp (ϑ * Complex.I - z * sStar) *
          Complex.exp (-z * ((s - sStar : ℝ) : ℂ))) * N (s - sStar) by ring,
      ← Complex.exp_add]
    rw [show (ϑ : ℂ) * Complex.I - z * sStar + -z * ((s - sStar : ℝ) : ℂ) =
      -z * s + ϑ * Complex.I by push_cast; ring, Complex.exp_add]
    ring
  rw [this, integral_sub_right_eq_self (fun u : ℝ => Complex.exp (ϑ * Complex.I - z * sStar) *
    (Complex.exp (-z * u) * N u)), integral_const_mul]

/-- In particular the translated/rotated transform has the same zeros. -/
theorem bilateral_translate_zero_iff (N : ℝ → ℂ) (ϑ sStar : ℝ) (z : ℂ) :
    bilateral (fun s => Complex.exp (ϑ * Complex.I) * N (s - sStar)) z = 0 ↔
      bilateral N z = 0 := by
  rw [bilateral_translate, mul_eq_zero]
  simp [Complex.exp_ne_zero]

/-- Mild (variation-of-constants) solutions of `Y' = cY + f`, the integral form of locally
absolutely continuous solutions. -/
def IsMildSolution (c : ℂ) (f : ℝ → ℂ) (Y : ℝ → ℂ) : Prop :=
  ∀ s₀ s : ℝ, s₀ ≤ s →
    Y s = Complex.exp (c * (s - s₀)) * Y s₀ + ∫ t in s₀..s, Complex.exp (c * (s - t)) * f t

/-- **Lemma (Retarded normalization), uniqueness.** Two solutions of `Y' = cY + f` with
`e^{-cs} Y(s) → 0` as `s → -∞` coincide. -/
theorem retarded_unique {c : ℂ} {f Y₁ Y₂ : ℝ → ℂ} (h₁ : IsMildSolution c f Y₁)
    (h₂ : IsMildSolution c f Y₂)
    (n₁ : Tendsto (fun s : ℝ => Complex.exp (-c * s) * Y₁ s) atBot (𝓝 0))
    (n₂ : Tendsto (fun s : ℝ => Complex.exp (-c * s) * Y₂ s) atBot (𝓝 0)) : Y₁ = Y₂ := by
  funext s
  set D : ℝ → ℂ := fun t => Complex.exp (-c * t) * (Y₁ t - Y₂ t)
  have hconst : ∀ s₀ ≤ s, D s = D s₀ := by
    intro s₀ hs₀
    simp only [D]
    rw [h₁ s₀ s hs₀, h₂ s₀ s hs₀]
    have : Complex.exp (-c * s) * Complex.exp (c * (s - s₀)) = Complex.exp (-c * s₀) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [show Complex.exp (c * (↑s - ↑s₀)) * Y₁ s₀ + (∫ t in s₀..s, Complex.exp (c * (↑s - ↑t)) * f t)
      - (Complex.exp (c * (↑s - ↑s₀)) * Y₂ s₀ + ∫ t in s₀..s, Complex.exp (c * (↑s - ↑t)) * f t)
      = Complex.exp (c * (↑s - ↑s₀)) * (Y₁ s₀ - Y₂ s₀) by ring, ← mul_assoc, this]
  have hD : Tendsto D atBot (𝓝 0) := by
    have := n₁.sub n₂
    simp only [sub_zero] at this
    exact this.congr fun t => by simp only [D]; ring
  have hev : ∀ᶠ s₀ in atBot, D s₀ = D s := by
    filter_upwards [eventually_le_atBot s] with s₀ hs₀ using (hconst s₀ hs₀).symm
  have hlim : Tendsto D atBot (𝓝 (D s)) := tendsto_const_nhds.congr' (EventuallyEq.symm hev)
  have hzero : D s = 0 := tendsto_nhds_unique hlim hD
  simp only [D, mul_eq_zero, Complex.exp_ne_zero, false_or, sub_eq_zero] at hzero
  exact hzero


/-- The retarded solution `Y(s) = K e^{cs} ∫_{-∞}^s e^{-zt} N(t) dt`. -/
noncomputable def retardedSol (c z K : ℂ) (N : ℝ → ℂ) (s : ℝ) : ℂ :=
  K * Complex.exp (c * s) * ∫ t in Iic s, Complex.exp (-z * t) * N t

lemma tendsto_setIntegral_Iic_atTop {g : ℝ → ℂ} (hg : Integrable g) :
    Tendsto (fun s : ℝ => ∫ t in Iic s, g t) atTop (𝓝 (∫ t, g t)) := by
  simp_rw [← integral_indicator measurableSet_Iic]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖)
  · exact Eventually.of_forall fun s => hg.aestronglyMeasurable.indicator measurableSet_Iic
  · exact Eventually.of_forall fun s => Eventually.of_forall fun t =>
      norm_indicator_le_norm_self _ _
  · exact hg.norm
  · refine Eventually.of_forall fun t => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop t] with s hs
    rw [indicator_of_mem (show t ∈ Iic s from hs)]

lemma tendsto_setIntegral_Iic_atBot {g : ℝ → ℂ} (hg : Integrable g) :
    Tendsto (fun s : ℝ => ∫ t in Iic s, g t) atBot (𝓝 0) := by
  simp_rw [← integral_indicator measurableSet_Iic]
  rw [show (0 : ℂ) = ∫ t : ℝ, (0 : ℂ) by simp]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖)
  · exact Eventually.of_forall fun s => hg.aestronglyMeasurable.indicator measurableSet_Iic
  · exact Eventually.of_forall fun s => Eventually.of_forall fun t =>
      norm_indicator_le_norm_self _ _
  · exact hg.norm
  · refine Eventually.of_forall fun t => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot t] with s hs
    rw [indicator_of_notMem (show t ∉ Iic s from not_le.mpr hs)]

/-- **Lemma (Retarded normalization), existence; Proposition `nt:prop:transfer`, limit.**
For `0 < Re z < σ`, the function `Y(s) = K e^{cs} ∫_{-∞}^s e^{-zt} N(t) dt` solves
`Y' = cY + K e^{-(z-c)s} N(s)`, satisfies `e^{-cs} Y(s) → 0` as `s → -∞`, and
`e^{-cs} Y(s) → K F(z)` as `s → +∞`. -/
theorem retardedSol_spec {σ : ℝ} {N : ℝ → ℂ} (hN : ExpWindow σ N) {z : ℂ} (h0 : 0 < z.re)
    (h1 : z.re < σ) (c K : ℂ) :
    IsMildSolution c (fun t => K * Complex.exp (-(z - c) * t) * N t) (retardedSol c z K N) ∧
      Tendsto (fun s : ℝ => Complex.exp (-c * s) * retardedSol c z K N s) atBot (𝓝 0) ∧
      Tendsto (fun s : ℝ => Complex.exp (-c * s) * retardedSol c z K N s) atTop
        (𝓝 (K * bilateral N z)) := by
  have hg := hN.integrable_exp h0 h1
  have hnorm : ∀ s : ℝ, Complex.exp (-c * s) * retardedSol c z K N s =
      K * ∫ t in Iic s, Complex.exp (-z * t) * N t := by
    intro s
    simp only [retardedSol]
    rw [show Complex.exp (-c * s) * (K * Complex.exp (c * s) * ∫ t in Iic s,
        Complex.exp (-z * t) * N t) = K * (Complex.exp (-c * s) * Complex.exp (c * s)) *
        ∫ t in Iic s, Complex.exp (-z * t) * N t by ring, ← Complex.exp_add]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro s₀ s hs
    simp only [retardedSol]
    have hdiff := intervalIntegral.integral_Iic_sub_Iic (f := fun t => Complex.exp (-z * t) * N t)
      (μ := volume) hg.integrableOn hg.integrableOn (a := s₀) (b := s)
    have hI : ∫ t in s₀..s, Complex.exp (c * (s - t)) * (K * Complex.exp (-(z - c) * t) * N t) =
        K * Complex.exp (c * s) * ∫ t in s₀..s, Complex.exp (-z * t) * N t := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext t
      rw [show K * Complex.exp (c * s) * (Complex.exp (-z * t) * N t) =
        K * (Complex.exp (c * s) * Complex.exp (-z * t)) * N t by ring, ← Complex.exp_add,
        show Complex.exp (c * (s - t)) * (K * Complex.exp (-(z - c) * t) * N t) =
        K * (Complex.exp (c * (s - t)) * Complex.exp (-(z - c) * t)) * N t by ring,
        ← Complex.exp_add]
      congr 3; ring
    rw [hI, ← hdiff]
    rw [show Complex.exp (c * (↑s - ↑s₀)) * (K * Complex.exp (c * ↑s₀) *
        ∫ t in Iic s₀, Complex.exp (-z * ↑t) * N t) =
        K * (Complex.exp (c * (↑s - ↑s₀)) * Complex.exp (c * ↑s₀)) *
        ∫ t in Iic s₀, Complex.exp (-z * ↑t) * N t by ring, ← Complex.exp_add]
    rw [show c * (↑s - ↑s₀) + c * ↑s₀ = c * s by ring]
    ring
  · simp_rw [hnorm]
    simpa using (tendsto_setIntegral_Iic_atBot hg).const_mul K
  · simp_rw [hnorm]
    exact (tendsto_setIntegral_Iic_atTop hg).const_mul K

end Euler2D

end
