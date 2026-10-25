module

public import RequestProject.Euler.CurlLimit

/-!
# Closure of uniformly bounded Sobolev data

Strong convergence in `L²` and uniform bounds on a velocity and its
four distributional first derivatives in `Lᵠ`, `2 ≤ q`, retain the full
`W¹,ᵠ` regularity. Each derivative may use its own weakly convergent
subsequence, since the velocity limit is already fixed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

/-- A uniform `W¹,ᵠ` bound: the velocity has `Lᵠ` norm at most `M`, and
there are distributional first derivatives with each scalar component's
`Lᵠ` norm at most `M`. Bounds use `eLpNorm`, including at exponent infinity. -/
def W1pBoundedBy (q : ENNReal) (M : ℝ) (u : R2 → R2) : Prop :=
  MemLp u q μT ∧ eLpNorm u q μT ≤ ENNReal.ofReal M ∧
    ∃ G : Fin 2 → Fin 2 → R2 → ℝ,
      (∀ i j, MemLp (G i j) q μT ∧ eLpNorm (G i j) q μT ≤ ENNReal.ofReal M) ∧
      ∀ i j, ∀ ψ : R2 → ℝ, IsScalarTest ψ →
        ∫ x in torusBox, u x j * pd i ψ x = -∫ x in torusBox, G i j x * ψ x

/-- The bounded Sobolev predicate implies the original Sobolev predicate. -/
theorem W1pBoundedBy.memW1p {q : ENNReal} {M : ℝ} {u : R2 → R2}
    (h : W1pBoundedBy q M u) : MemW1p q u := by
  obtain ⟨hu, _, G, hG, htest⟩ := h
  exact ⟨hu, G, fun i j => (hG i j).1, htest⟩

/-- One distributional first derivative retains its `Lᵠ` bound under
strong `L²` convergence of the vector field. -/
theorem weak_derivative_bound_of_tendsto {q : ENNReal} (hq : 2 ≤ q)
    {v : ℕ → L2T} {u : L2T} {M : ℝ} (i j : Fin 2)
    (hv : Tendsto v atTop (𝓝 u))
    (hw : ∀ n, ∃ w : R2 → ℝ,
      MemLp w q μT ∧ eLpNorm w q μT ≤ ENNReal.ofReal M ∧
        ∀ ψ : R2 → ℝ, IsScalarTest ψ →
          ∫ x in torusBox, v n x j * pd i ψ x = -∫ x in torusBox, w x * ψ x) :
    ∃ w : R2 → ℝ,
      MemLp w q μT ∧ eLpNorm w q μT ≤ ENNReal.ofReal M ∧
        ∀ ψ : R2 → ℝ, IsScalarTest ψ →
          ∫ x in torusBox, u x j * pd i ψ x = -∫ x in torusBox, w x * ψ x := by
  choose w hwmem hwbound hwtest using hw
  have hexp : 0 ≤ 1 / (2 : ℝ) - 1 / q.toReal := by
    by_cases ht : q = ∞
    · simp [ht]
    have hqr : (2 : ℝ) ≤ q.toReal := by
      simpa using ENNReal.toReal_mono ht hq
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hqr
    linarith
  let C : ENNReal := ENNReal.ofReal M * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μT univ))
  let W : ℕ → Lp ℝ 2 μT := fun n => ((hwmem n).mono_exponent hq).toLp (w n)
  have hWae (n : ℕ) : (W n : R2 → ℝ) =ᵐ[μT] w n :=
    ((hwmem n).mono_exponent hq).coeFn_toLp
  have hWbound (n : ℕ) : ‖W n‖ ≤ C.toReal := by
    change ‖((hwmem n).mono_exponent hq).toLp (w n)‖ ≤ C.toReal
    rw [Lp.norm_toLp]
    apply ENNReal.toReal_mono hC
    calc
      eLpNorm (w n) 2 μT ≤ eLpNorm (w n) q μT *
          μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal) := by
        simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq
          (hwmem n).aestronglyMeasurable
      _ ≤ C := mul_le_mul_left (hwbound n) _
  obtain ⟨ω, _, φ, hφ, hweak⟩ := exists_weakly_convergent_subsequence W C.toReal hWbound
  have hωbound : eLpNorm ω q μT ≤ ENNReal.ofReal M := by
    apply eLpNorm_le_of_inner_tendsto μT ((by norm_num : (1 : ENNReal) ≤ 2).trans hq)
      (fun n => ?_) hweak
    rw [eLpNorm_congr_ae (hWae (φ n))]
    exact hwbound (φ n)
  refine ⟨ω, memLp_iff.mpr (hωbound.trans_lt (by simp)), hωbound, ?_⟩
  intro ψ hψ
  have hψc : Continuous ψ := hψ.1.continuous
  have hright : Tendsto (fun n => ∫ x in torusBox, w (φ n) x * ψ x) atTop
      (𝓝 (∫ x in torusBox, ω x * ψ x)) := by
    have heq (n : ℕ) : (∫ x in torusBox, w (φ n) x * ψ x) =
        inner ℝ (W (φ n)) ((continuous_memLp_torus hψc 2).toLp ψ) := by
      rw [← scalar_test_pairing_eq_inner (W (φ n)) hψc]
      apply integral_congr_ae
      filter_upwards [hWae (φ n)] with x hx
      rw [hx]
    simp_rw [heq, scalar_test_pairing_eq_inner ω hψc]
    exact hweak _
  have hpd : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft := tendsto_integral_lin (hv.comp hφ.tendsto_atTop) hpd j
  exact tendsto_nhds_unique hleft (hright.neg.congr' (Eventually.of_forall fun n =>
    (hwtest (φ n) ψ hψ).symm))

/-- Strong `L²` limits retain a uniform velocity `Lᵠ` bound and uniform
`Lᵠ` bounds on all four distributional first derivatives. -/
theorem w1pBoundedBy_of_tendsto {q : ENNReal} (hq : 2 ≤ q)
    {v : ℕ → L2T} {u : L2T} {M : ℝ}
    (hv : Tendsto v atTop (𝓝 u)) (hU : ∀ n, W1pBoundedBy q M (v n)) :
    W1pBoundedBy q M u := by
  have hubound : eLpNorm u q μT ≤ ENNReal.ofReal M := by
    exact eLpNorm_le_of_tendstoInMeasure
      (Eventually.of_forall fun n => (hU n).2.1)
      (tendstoInMeasure_of_tendsto_Lp hv) (fun n => Lp.aestronglyMeasurable (v n))
  have hG (n : ℕ) := (hU n).2.2
  choose G hGbound hGtest using hG
  have hderiv (i j : Fin 2) : ∃ g : R2 → ℝ,
      MemLp g q μT ∧ eLpNorm g q μT ≤ ENNReal.ofReal M ∧
        ∀ ψ : R2 → ℝ, IsScalarTest ψ →
          ∫ x in torusBox, u x j * pd i ψ x = -∫ x in torusBox, g x * ψ x := by
    apply weak_derivative_bound_of_tendsto hq i j hv
    intro n
    exact ⟨G n i j, (hGbound n i j).1, (hGbound n i j).2, hGtest n i j⟩
  choose g hgmem hgbound hgtest using hderiv
  exact ⟨memLp_iff.mpr (hubound.trans_lt (by simp)),
    hubound, g, fun i j => ⟨hgmem i j, hgbound i j⟩, hgtest⟩

/-- The original `MemW1p` regularity follows from uniform bounded Sobolev
approximations and strong `L²` convergence. -/
theorem memW1p_of_tendsto_of_bounded {q : ENNReal} (hq : 2 ≤ q)
    {v : ℕ → L2T} {u : L2T} {M : ℝ}
    (hv : Tendsto v atTop (𝓝 u)) (hU : ∀ n, W1pBoundedBy q M (v n)) :
    MemW1p q u := (w1pBoundedBy_of_tendsto hq hv hU).memW1p

/-- Uniform Sobolev bounds on a family of paths are retained at every
parameter where the approximating paths converge strongly in `L²`. -/
theorem w1pBoundedBy_on_of_tendsto {ι : Type*} {s : Set ι}
    {q : ENNReal} (hq : 2 ≤ q) {M : ℝ}
    {U : ℕ → ι → L2T} {u : ι → L2T}
    (hU : ∀ n, ∀ t ∈ s, W1pBoundedBy q M (U n t))
    (hlim : ∀ t ∈ s, Tendsto (fun n => U n t) atTop (𝓝 (u t))) :
    ∀ t ∈ s, W1pBoundedBy q M (u t) := by
  intro t ht
  exact w1pBoundedBy_of_tendsto hq (hlim t ht) (fun n => hU n t ht)

/-- On the finite-measure torus, Sobolev membership passes to every
smaller Lebesgue exponent. -/
theorem MemW1p.mono_exponent {p q : ENNReal} (hpq : p ≤ q)
    {u : R2 → R2} (hu : MemW1p q u) : MemW1p p u := by
  obtain ⟨humem, G, hGmem, hGtest⟩ := hu
  exact ⟨humem.mono_exponent hpq, G, fun i j => (hGmem i j).mono_exponent hpq, hGtest⟩

/-- Bounded first derivatives provide a bounded distributional curl,
with the explicit componentwise estimate `2 * max M 0`. -/
theorem W1pBoundedBy.curl_bound {q : ENNReal} {M : ℝ} {u : L2T}
    (h : W1pBoundedBy q M u) (hq : 1 ≤ q) :
    ∃ w : R2 → ℝ, MemLp w q μT ∧ IsCurl u w ∧
      eLpNorm w q μT ≤ ENNReal.ofReal (2 * max M 0) := by
  obtain ⟨_, _, G, hG, hGtest⟩ := h
  let w : R2 → ℝ := fun x => G 0 1 x - G 1 0 x
  have hw : MemLp w q μT := (hG 0 1).1.sub (hG 1 0).1
  have hmax : 0 ≤ max M 0 := le_max_right M 0
  have hnorm : eLpNorm w q μT ≤ ENNReal.ofReal (2 * max M 0) := by
    calc
      eLpNorm w q μT ≤ eLpNorm (G 0 1) q μT + eLpNorm (G 1 0) q μT := by
        simpa only [w, Pi.sub_def] using
          eLpNorm_sub_le (f := G 0 1) (g := G 1 0) (μ := μT) hq
      _ ≤ ENNReal.ofReal (max M 0) + ENNReal.ofReal (max M 0) := by
        exact add_le_add
          ((hG 0 1).2.trans (ENNReal.ofReal_le_ofReal (le_max_left M 0)))
          ((hG 1 0).2.trans (ENNReal.ofReal_le_ofReal (le_max_left M 0)))
      _ = ENNReal.ofReal (max M 0 + max M 0) :=
        (ENNReal.ofReal_add hmax hmax).symm
      _ = ENNReal.ofReal (2 * max M 0) := by rw [two_mul]
  refine ⟨w, hw, ?_, hnorm⟩
  intro ψ hψ
  have hψc : Continuous ψ := hψ.1.continuous
  have hpd : ∀ i, Continuous (pd i ψ) := fun i =>
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have IG (i j : Fin 2) : Integrable (fun x => G i j x * ψ x) μT := by
    obtain ⟨C, hC⟩ := bound_on_box hψc
    apply ((hG i j).1.integrable hq).mul_bdd hψc.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_torusBox]
    exact Eventually.of_forall fun x hx => by
      simpa only [Real.norm_eq_abs] using hC x hx
  have Iu (i j : Fin 2) : Integrable (fun x => u x j * pd i ψ x) μT := by
    obtain ⟨C, hC⟩ := bound_on_box (hpd i)
    exact integrable_lin u j (hpd i).aestronglyMeasurable hC
  simp only [w, sub_mul]
  rw [integral_sub (IG 0 1) (IG 1 0), integral_sub (Iu 1 0) (Iu 0 1),
    hGtest 1 0 ψ hψ, hGtest 0 1 ψ hψ]
  ring

/-- Uniform bounded Sobolev regularity of a path supplies the uniform
vorticity bound used in the original Euler solution statements. -/
theorem W1pBoundedBy.curlBoundedBy {T M : ℝ} {q : ENNReal} {u : ℝ → L2T}
    (h : ∀ t ∈ Icc 0 T, W1pBoundedBy q M (u t)) (hq : 1 ≤ q) :
    CurlBoundedBy T q (2 * max M 0) u := by
  intro t ht
  obtain ⟨w, hw, hcurl, hbound⟩ := (h t ht).curl_bound hq
  exact ⟨w, hw, hcurl,
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) (le_max_right M 0)) hbound⟩

end Euler2D

end


