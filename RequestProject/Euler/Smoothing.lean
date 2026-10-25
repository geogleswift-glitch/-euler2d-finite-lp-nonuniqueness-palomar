module

public import Mathlib

/-!
# Exponentially decaying Fourier multipliers (Lemma `pc:smoothing`)

For a complete complex normed space `V` (for the paper, `V = ℂⁿ` and the `E_m` are matrices),
a `V`-valued function `f` on the circle `ℝ / 2πℤ` has Fourier coefficients
`f̂(m) = (2π)⁻¹ ∫₀^{2π} e^{-imθ} f(θ) dθ`. Given bounded operators `E_m`, the multiplier is
`(E f)(θ) = ∑_m e^{imθ} E_m f̂(m)`.

* `fourierMultiplier_contDiff`, `fourierMultiplier_iteratedDeriv_le`: if
  `‖E_m‖ ≤ w(m)` with `∑_m (1+|m|)^j w(m) < ∞` for all `j`, then `E f` is smooth and
  `‖(E f)^{(j)}‖_∞ ≤ (∑_m (1+|m|)^j w(m)) ‖f‖_∞`; in particular `E : C⁰ → C^r` is bounded for
  every finite `r`.
* `exp_decay_weight_summable`: the weights `C (1+|m|)^k a₀^{|m|}`, `0 < a₀ < 1`, qualify
  (`smoothing_multiplier`).
* `smoothing_multiplier_tail`: the truncations `E_{≤n}` (finite rank when `V` is finite
  dimensional) converge to `E` in the operator norm `C⁰ → C^r`; this is the compactness
  statement of the lemma, here in the `C⁰ → C^r` form.
* `modified_weight`: the same conclusions hold when finitely many `E_m` are changed
  arbitrarily.
* The paper states compactness on the little-Hölder space `c^{1,γ}`; here it is proved as
  operator-norm approximation by finite-rank truncations from `C⁰` into `C^r`
  (`fourierMultiplier_eq_sum_add_tail`, `smoothing_multiplier_tail`), which is the key step
  of the paper's argument. The space `c^{1,γ}` itself is not formalized.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real Complex

namespace Euler2D

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- `|e^{imθ}| = 1`. -/
lemma norm_cexp_int_mul_I (m : ℤ) (θ : ℝ) : ‖cexp ((m : ℂ) * θ * I)‖ = 1 := by
  rw [Complex.norm_exp]; simp

omit [CompleteSpace V] in
/-- `|e^{-imθ}| = 1`. -/
lemma norm_cexp_neg_int_mul_I (m : ℤ) (θ : ℝ) : ‖cexp (-((m : ℂ) * θ * I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

omit [CompleteSpace V] in
/-- Iterated derivatives of `θ ↦ e^{imθ} v`: `(im)^j e^{imθ} v`. -/
lemma iteratedDeriv_cexp_smul (m : ℤ) (v : V) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun θ : ℝ => cexp ((m : ℂ) * θ * I) • v) θ =
      (((m : ℂ) * I) ^ j * cexp ((m : ℂ) * θ * I)) • v := by
  induction j generalizing θ with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have : iteratedDeriv n (fun θ : ℝ => cexp ((m : ℂ) * θ * I) • v) =
        fun θ : ℝ => (((m : ℂ) * I) ^ n * cexp ((m : ℂ) * θ * I)) • v := funext ih
    rw [this]
    have h1 : HasDerivAt (fun θ : ℝ => cexp ((m : ℂ) * θ * I))
        (cexp ((m : ℂ) * θ * I) * ((m : ℂ) * I)) θ := by
      have h0 : HasDerivAt (fun θ : ℝ => ((m : ℂ) * θ * I)) ((m : ℂ) * I) θ := by
        have := ((Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul (m : ℂ)).mul_const I
        simpa using this
      exact h0.cexp
    have h2 := ((h1.const_mul (((m : ℂ) * I) ^ n)).smul_const v)
    rw [h2.deriv]
    congr 1
    ring

omit [CompleteSpace V] in
/-- `θ ↦ e^{imθ} v` is smooth. -/
lemma contDiff_cexp_smul (m : ℤ) (v : V) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun θ : ℝ => cexp ((m : ℂ) * θ * I) • v) := by
  have : ContDiff ℝ n (fun θ : ℝ => cexp ((m : ℂ) * θ * I)) := by
    have h : ContDiff ℝ n (fun θ : ℝ => (m : ℂ) * (θ : ℂ) * I) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const
    exact Complex.contDiff_exp.comp h
  exact this.smul contDiff_const

/-- Fourier coefficient `f̂(m) = (2π)⁻¹ ∫₀^{2π} e^{-imθ} f(θ) dθ` of a `V`-valued function. -/
noncomputable def fourierCoeffV (f : ℝ → V) (m : ℤ) : V :=
  ((2 * π)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * π, cexp (-((m : ℂ) * θ * I)) • f θ

/-- One term `e^{imθ} E_m f̂(m)` of the Fourier multiplier. -/
noncomputable def multiplierTerm (E : ℤ → V →L[ℂ] V) (f : ℝ → V) (m : ℤ) (θ : ℝ) : V :=
  cexp ((m : ℂ) * θ * I) • E m (fourierCoeffV f m)

/-- The Fourier multiplier `(E f)(θ) = ∑_m e^{imθ} E_m f̂(m)`. -/
noncomputable def fourierMultiplier (E : ℤ → V →L[ℂ] V) (f : ℝ → V) (θ : ℝ) : V :=
  ∑' m : ℤ, multiplierTerm E f m θ

omit [CompleteSpace V] in
/-- `‖f̂(m)‖ ≤ M` whenever `‖f‖ ≤ M` on `[0, 2π]`. -/
lemma norm_fourierCoeffV_le {f : ℝ → V} {M : ℝ} (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M)
    (m : ℤ) : ‖fourierCoeffV f m‖ ≤ M := by
  have hint : ‖∫ θ in (0 : ℝ)..2 * π, cexp (-((m : ℂ) * θ * I)) • f θ‖ ≤ M * |2 * π - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ
    rw [Set.uIoc_of_le (by positivity)] at hθ
    rw [norm_smul, norm_cexp_neg_int_mul_I, one_mul]
    exact hf θ ⟨hθ.1.le, hθ.2⟩
  have hpi : 0 < 2 * π := by positivity
  rw [fourierCoeffV, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpi.le)]
  rw [sub_zero, abs_of_pos hpi] at hint
  calc (2 * π)⁻¹ * ‖_‖ ≤ (2 * π)⁻¹ * (M * (2 * π)) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpi.le)
    _ = M := by field_simp

omit [CompleteSpace V] in
/-- The `j`-th derivative of the `m`-th term is at most `(1+|m|)^j w(m) M`. -/
lemma norm_iteratedFDeriv_multiplierTerm_le (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (j : ℕ) (m : ℤ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ j (multiplierTerm E f m) θ‖ ≤ (1 + |(m : ℝ)|) ^ j * w m * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf 0 ⟨le_rfl, by positivity⟩)
  have hv : ‖E m (fourierCoeffV f m)‖ ≤ w m * M :=
    (E m).le_opNorm_of_le (norm_fourierCoeffV_le hf m) |>.trans
      (mul_le_mul_of_nonneg_right (hw m) hM)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  unfold multiplierTerm
  rw [iteratedDeriv_cexp_smul, norm_smul, norm_mul, norm_cexp_int_mul_I, mul_one, norm_pow,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
  have h1 : |(m : ℝ)| ^ j ≤ (1 + |(m : ℝ)|) ^ j :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) j
  calc |(m : ℝ)| ^ j * ‖E m (fourierCoeffV f m)‖ ≤ (1 + |(m : ℝ)|) ^ j * (w m * M) :=
        mul_le_mul h1 hv (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- **Lemma `pc:smoothing`, smoothness.** If `‖E_m‖ ≤ w(m)` and every weighted sum
`∑_m (1+|m|)^j w(m)` converges, then `E f` is `C^N` for every `N` and every bounded `f`. -/
theorem fourierMultiplier_contDiff (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (hsum : ∀ j : ℕ, Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m) {N : ℕ∞} :
    ContDiff ℝ N (fourierMultiplier E f) := by
  unfold fourierMultiplier
  exact contDiff_tsum (fun m => contDiff_cexp_smul m _) (fun k _ => (hsum k).mul_right M)
    (fun k m θ _ => norm_iteratedFDeriv_multiplierTerm_le E hf hw k m θ)

/-- **Lemma `pc:smoothing`, bound `C⁰ → C^r`.** Under the same hypotheses,
`‖(E f)^{(j)}(θ)‖ ≤ (∑_m (1+|m|)^j w(m)) M` for all `j` and `θ`. -/
theorem fourierMultiplier_iteratedDeriv_le (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (hsum : ∀ j : ℕ, Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (fourierMultiplier E f) θ‖ ≤
      (∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * w m) * M := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  unfold fourierMultiplier
  rw [iteratedFDeriv_tsum_apply (N := (j : ℕ∞)) (f := fun m θ => multiplierTerm E f m θ)
    (fun m => contDiff_cexp_smul m _)
    (fun k _ => (hsum k).mul_right M)
    (fun k m θ _ => norm_iteratedFDeriv_multiplierTerm_le E hf hw k m θ) le_rfl]
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded ((hsum j).mul_right M).hasSum
    (fun m => norm_iteratedFDeriv_multiplierTerm_le E hf hw j m θ)

/-- `∑_n (1+n)^p a₀^n < ∞` for `0 ≤ a₀ < 1`. -/
lemma summable_one_add_pow_mul_geom {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : a₀ < 1) (p : ℕ) :
    Summable fun n : ℕ => (1 + (n : ℝ)) ^ p * a₀ ^ n := by
  have hs1 : Summable fun n : ℕ => a₀ ^ n := summable_geometric_of_lt_one ha₀ ha₁
  have hs2 : Summable fun n : ℕ => (n : ℝ) ^ p * a₀ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one p (by rw [Real.norm_of_nonneg ha₀]; exact ha₁)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hs1.add hs2).mul_left (2 ^ p))
  have hb : (1 + (n : ℝ)) ^ p ≤ 2 ^ p * (1 + (n : ℝ) ^ p) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have h2 : (1:ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
      have h0 : (0:ℝ) ≤ ((0:ℕ):ℝ) ^ p := by positivity
      simp only [Nat.cast_zero, add_zero, one_pow] at h0 ⊢
      nlinarith
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h
      calc (1 + (n : ℝ)) ^ p ≤ (2 * n) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
        _ = 2 ^ p * n ^ p := mul_pow _ _ _
        _ ≤ 2 ^ p * (1 + (n : ℝ) ^ p) := by nlinarith [pow_pos (two_pos : (0:ℝ) < 2) p]
  calc (1 + (n : ℝ)) ^ p * a₀ ^ n ≤ 2 ^ p * (1 + (n : ℝ) ^ p) * a₀ ^ n :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

/-- The exponentially decaying weights `C (1+|m|)^k a₀^{|m|}` have all polynomially weighted
sums finite. -/
theorem exp_decay_weight_summable {C a₀ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : a₀ < 1) (k j : ℕ) :
    Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * (C * (1 + |(m : ℝ)|) ^ k * a₀ ^ m.natAbs) := by
  have h : Summable fun n : ℕ => C * ((1 + (n : ℝ)) ^ (j + k) * a₀ ^ n) :=
    (summable_one_add_pow_mul_geom ha₀ ha₁ (j + k)).mul_left C
  apply Summable.of_nat_of_neg
  · refine h.congr (fun n => ?_)
    simp only [Int.cast_natCast, Nat.abs_cast, Int.natAbs_natCast]
    ring
  · refine h.congr (fun n => ?_)
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, Int.natAbs_neg,
      Int.natAbs_natCast]
    ring

/-- Coefficients with the block `S` removed. -/
noncomputable def tailCoeff (E : ℤ → V →L[ℂ] V) (S : Finset ℤ) (m : ℤ) : V →L[ℂ] V :=
  if m ∈ S then 0 else E m

omit [CompleteSpace V] in
/-- `‖e^{imθ} E_m f̂(m)‖ ≤ w(m) M`. -/
lemma norm_multiplierTerm_le (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (m : ℤ) (θ : ℝ) : ‖multiplierTerm E f m θ‖ ≤ w m * M := by
  have := norm_iteratedFDeriv_multiplierTerm_le E hf hw 0 m θ
  simpa using this

/-- Splitting `E f` into the finite-rank truncation `∑_{m ∈ S}` and the multiplier with the
block `S` removed. -/
theorem fourierMultiplier_eq_sum_add_tail (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (hsum : Summable w) (S : Finset ℤ) (θ : ℝ) :
    fourierMultiplier E f θ =
      ∑ m ∈ S, multiplierTerm E f m θ + fourierMultiplier (tailCoeff E S) f θ := by
  have hs : Summable fun m => multiplierTerm E f m θ :=
    Summable.of_norm_bounded (hsum.mul_right M) (fun m => norm_multiplierTerm_le E hf hw m θ)
  have h1 : ∀ m, multiplierTerm (tailCoeff E S) f m θ =
      multiplierTerm E f m θ - (if m ∈ S then multiplierTerm E f m θ else 0) := by
    intro m
    unfold multiplierTerm tailCoeff
    split_ifs <;> simp
  have hfin : Summable fun m => (if m ∈ S then multiplierTerm E f m θ else 0) :=
    summable_of_finite_support ((S.finite_toSet).subset (fun m hm => by
      by_contra h; exact hm (if_neg h)))
  have h2 : ∑' m, (if m ∈ S then multiplierTerm E f m θ else 0) = ∑ m ∈ S, multiplierTerm E f m θ := by
    rw [tsum_eq_sum (s := S) (fun m hm => if_neg hm)]
    exact Finset.sum_congr rfl (fun m hm => if_pos hm)
  unfold fourierMultiplier
  rw [tsum_congr h1, hs.tsum_sub hfin, h2]
  abel

/-- **Lemma `pc:smoothing`, compactness (in the `C⁰ → C^r` form).** The remainder after the
finite-rank truncation to a finite set `S` of frequencies has `‖(·)^{(j)}‖_∞ ≤ ε_j(S) ‖f‖_∞`,
and `ε_j(S) → 0` as `S` exhausts `ℤ`. Hence `E` is an operator-norm limit of finite-rank
operators `C⁰ → C^r` (when `V` is finite dimensional). -/
theorem smoothing_multiplier_tail (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (hsum : ∀ j : ℕ, Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m) (j : ℕ) :
    (∀ (S : Finset ℤ) (θ : ℝ), ‖iteratedDeriv j (fourierMultiplier (tailCoeff E S) f) θ‖ ≤
      (∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * (if m ∈ S then 0 else w m)) * M) ∧
    Tendsto (fun S : Finset ℤ => ∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * (if m ∈ S then 0 else w m))
      atTop (𝓝 0) := by
  have hw0 : ∀ m, 0 ≤ w m := fun m => (norm_nonneg _).trans (hw m)
  refine ⟨fun S θ => ?_, ?_⟩
  · apply fourierMultiplier_iteratedDeriv_le (tailCoeff E S) hf
    · intro m; unfold tailCoeff; split_ifs
      · simp
      · exact hw m
    · intro i
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (hsum i)
      · split_ifs
        · simp
        · exact mul_nonneg (by positivity) (hw0 m)
      · split_ifs
        · simp only [mul_zero]; exact mul_nonneg (by positivity) (hw0 m)
        · exact le_rfl
  · have := tendsto_tsum_compl_atTop_zero (fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m)
    refine this.congr (fun S => ?_)
    refine (tsum_subtype {m : ℤ | m ∉ S} (fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m)).trans
      (tsum_congr (fun m => ?_))
    by_cases hm : m ∈ S
    · simp [hm]
    · simp [hm]

/-- **Lemma `pc:smoothing`** for `‖E_m‖ ≤ C (1+|m|)^k a₀^{|m|}`, `0 ≤ a₀ < 1`: `E f` is `C^N` for
every `N`, with `‖(E f)^{(j)}‖_∞ ≤ C_j ‖f‖_∞`. -/
theorem smoothing_multiplier (E : ℤ → V →L[ℂ] V) {C a₀ : ℝ} {k : ℕ} (ha₀ : 0 ≤ a₀) (ha₁ : a₀ < 1)
    (hE : ∀ m : ℤ, ‖E m‖ ≤ C * (1 + |(m : ℝ)|) ^ k * a₀ ^ m.natAbs)
    {f : ℝ → V} {M : ℝ} (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) :
    (∀ N : ℕ∞, ContDiff ℝ N (fourierMultiplier E f)) ∧
    ∀ (j : ℕ) (θ : ℝ), ‖iteratedDeriv j (fourierMultiplier E f) θ‖ ≤
      (∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * (C * (1 + |(m : ℝ)|) ^ k * a₀ ^ m.natAbs)) * M :=
  ⟨fun _ => fourierMultiplier_contDiff E hf hE (exp_decay_weight_summable ha₀ ha₁ k),
    fourierMultiplier_iteratedDeriv_le E hf hE (exp_decay_weight_summable ha₀ ha₁ k)⟩

omit [CompleteSpace V] in
/-- **Lemma `pc:smoothing`, finitely many blocks changed.** If `E'` agrees with `E` outside a
finite set `S`, then `E'` admits a weight with the same summability, so all conclusions above
apply to `E'`. -/
theorem modified_weight (E E' : ℤ → V →L[ℂ] V) (S : Finset ℤ) (hEE' : ∀ m ∉ S, E' m = E m)
    {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (hsum : ∀ j : ℕ, Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m) :
    ∃ w' : ℤ → ℝ, (∀ m, ‖E' m‖ ≤ w' m) ∧
      ∀ j : ℕ, Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w' m := by
  refine ⟨fun m => w m + if m ∈ S then ‖E' m‖ else 0, fun m => ?_, fun j => ?_⟩
  · by_cases hm : m ∈ S
    · simp only [hm, if_true]
      linarith [(norm_nonneg _).trans (hw m)]
    · simp only [hm, if_false, add_zero, hEE' m hm]; exact hw m
  · have hfin : Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * (if m ∈ S then ‖E' m‖ else 0) :=
      summable_of_finite_support ((S.finite_toSet).subset (fun m hm => by
        by_contra h
        have h' : m ∉ S := h
        exact hm (by simp [h'])))
    exact ((hsum j).add hfin).congr (fun m => by ring)

end Euler2D
