module

public import Mathlib

/-!
# Continuity under common transport (Lemma `bv:transport-continuity`, `L¹` case)

Let `X t : ℂ → ℂ` be a jointly continuous family of measure-preserving maps with bounded
displacement on compact time intervals. For `f ∈ L¹(ℝ²)`:

* `transport_norm_eq`: `‖f ∘ X t‖₁ = ‖f‖₁`;
* `transport_continuous_L1`: `t ↦ f ∘ X t` is continuous in `L¹`, i.e.
  `∫ |f(X t a) − f(X t₀ a)| da → 0` as `t → t₀`.

The proof is the paper's: first for continuous compactly supported `f` (uniform convergence on a
fixed compact set), then by density. Only the exponent `r = 1` is treated; the support
assertion of the lemma is not formalized.
-/

@[expose] public section

open MeasureTheory Set Metric Filter Topology

namespace Euler2D

variable {X : ℝ → ℂ → ℂ}

/-- Integrals are invariant under a measure-preserving continuous map. -/
lemma integral_comp_flow (hXc : Continuous fun p : ℝ × ℂ => X p.1 p.2)
    (hmp : ∀ t, MeasurePreserving (X t)) (t : ℝ) {g : ℂ → ℝ} (hg : AEStronglyMeasurable g) :
    ∫ a, g (X t a) = ∫ a, g a := by
  have hXt : Continuous (X t) := hXc.comp (continuous_const.prodMk continuous_id)
  have h := integral_map (μ := volume) hXt.aemeasurable
    (by rw [(hmp t).map_eq]; exact hg : AEStronglyMeasurable g (Measure.map (X t) volume))
  rw [(hmp t).map_eq] at h
  exact h.symm

/-- `‖f ∘ X t‖₁ = ‖f‖₁`. -/
theorem transport_norm_eq (hXc : Continuous fun p : ℝ × ℂ => X p.1 p.2)
    (hmp : ∀ t, MeasurePreserving (X t)) (t : ℝ) {f : ℂ → ℝ} (hf : Integrable f) :
    ∫ a, |f (X t a)| = ∫ a, |f a| :=
  integral_comp_flow hXc hmp t hf.1.norm

/-- The case of a continuous compactly supported function. -/
lemma transport_continuous_compact (hXc : Continuous fun p : ℝ × ℂ => X p.1 p.2)
    (hdisp : ∀ T, ∃ B, ∀ t ∈ Icc (-T) T, ∀ a, ‖X t a - a‖ ≤ B) {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) (t₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∫ a, |g (X t a) - g (X t₀ a)| ≤ ε := by
  obtain ⟨R, hR⟩ : ∃ R, tsupport g ⊆ closedBall 0 R :=
    hgs.isCompact.isBounded.subset_closedBall 0
  obtain ⟨B, hB⟩ := hdisp (|t₀| + 1)
  have hI : Icc (t₀ - 1) (t₀ + 1) ⊆ Icc (-(|t₀| + 1)) (|t₀| + 1) := by
    intro t ht
    exact ⟨by linarith [ht.1, neg_abs_le t₀], by linarith [ht.2, le_abs_self t₀]⟩
  set K' := closedBall (0 : ℂ) (R + B) with hK'
  have hzero : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1), ∀ a ∉ K', g (X t a) = 0 := by
    intro t ht a ha
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff] at h1
    have h2 := hB t (hI ht) a
    apply ha
    rw [mem_closedBall_zero_iff]
    calc ‖a‖ = ‖X t a - (X t a - a)‖ := by ring_nf
      _ ≤ ‖X t a‖ + ‖X t a - a‖ := norm_sub_le _ _
      _ ≤ R + B := add_le_add h1 h2
  set Kc := Icc (t₀ - 1) (t₀ + 1) ×ˢ K' with hKc
  have hKcc : IsCompact Kc := isCompact_Icc.prod (isCompact_closedBall _ _)
  set φ : ℝ × ℂ → ℝ := fun p => g (X p.1 p.2) with hφ
  have hφc : Continuous φ := hgc.comp hXc
  have huc := hKcc.uniformContinuousOn_of_continuous hφc.continuousOn
  set V := volume.real K' with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set ε' := ε / (V + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp huc ε' hε'0
  have hm : 0 < min δ 1 := lt_min hδ one_pos
  filter_upwards [Ioo_mem_nhds (show t₀ - min δ 1 < t₀ by linarith)
    (show t₀ < t₀ + min δ 1 by linarith)] with t ht
  have htI : t ∈ Icc (t₀ - 1) (t₀ + 1) :=
    ⟨by linarith [ht.1, min_le_right δ 1], by linarith [ht.2, min_le_right δ 1]⟩
  have ht0I : t₀ ∈ Icc (t₀ - 1) (t₀ + 1) := ⟨by linarith, by linarith⟩
  have hdist : dist t t₀ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_left δ 1]
  have hpt : ∀ a, |g (X t a) - g (X t₀ a)| ≤ K'.indicator (fun _ => ε') a := by
    intro a
    by_cases ha : a ∈ K'
    · rw [indicator_of_mem ha]
      have := hδ' (t, a) ⟨htI, ha⟩ (t₀, a) ⟨ht0I, ha⟩ (by
        rw [Prod.dist_eq, dist_self]; simpa using hdist)
      rw [Real.dist_eq] at this
      exact this.le
    · rw [indicator_of_notMem ha, hzero t htI a ha, hzero t₀ ht0I a ha]; simp
  have hint : Integrable (K'.indicator (fun _ : ℂ => ε')) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const measure_closedBall_lt_top.ne enorm_ne_top)
  calc ∫ a, |g (X t a) - g (X t₀ a)| ≤ ∫ a, K'.indicator (fun _ => ε') a :=
        integral_mono_of_nonneg (Eventually.of_forall fun a => abs_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = ε' * V := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]; ring
    _ ≤ ε := by
        rw [hε', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-- **Lemma `bv:transport-continuity`** (`r = 1`). -/
theorem transport_continuous_L1 (hXc : Continuous fun p : ℝ × ℂ => X p.1 p.2)
    (hmp : ∀ t, MeasurePreserving (X t))
    (hdisp : ∀ T, ∃ B, ∀ t ∈ Icc (-T) T, ∀ a, ‖X t a - a‖ ≤ B) {f : ℂ → ℝ}
    (hf : Integrable f) (t₀ : ℝ) :
    Tendsto (fun t => ∫ a, |f (X t a) - f (X t₀ a)|) (𝓝 t₀) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hgs, hfg, hgc, hgi⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le (ε := ε / 4) (by positivity)
  simp only [Real.norm_eq_abs] at hfg
  filter_upwards [transport_continuous_compact hXc hdisp hgc hgs t₀ (ε := ε / 4)
    (by positivity)] with t ht
  have hcomp : ∀ s {u : ℂ → ℝ}, Integrable u → Integrable (fun a => u (X s a)) :=
    fun s u hu => ((hmp s).integrable_comp hu.1).mpr hu
  have hfg' : Integrable (fun w => |f w - g w|) := (hf.sub hgi).abs
  have e1 : ∫ a, |f (X t a) - g (X t a)| = ∫ w, |f w - g w| :=
    integral_comp_flow hXc hmp t (g := fun w => |f w - g w|) hfg'.1
  have e3 : ∫ a, |g (X t₀ a) - f (X t₀ a)| = ∫ w, |f w - g w| := by
    simp_rw [abs_sub_comm (g _) (f _)]
    exact integral_comp_flow hXc hmp t₀ (g := fun w => |f w - g w|) hfg'.1
  have i1 : Integrable (fun a => |f (X t a) - g (X t a)|) := hcomp t hfg'
  have i2 : Integrable (fun a => |g (X t a) - g (X t₀ a)|) :=
    ((hcomp t hgi).sub (hcomp t₀ hgi)).abs
  have i3 : Integrable (fun a => |g (X t₀ a) - f (X t₀ a)|) :=
    ((hcomp t₀ hgi).sub (hcomp t₀ hf)).abs
  have i12 : Integrable (fun a => |f (X t a) - g (X t a)| + |g (X t a) - g (X t₀ a)|) :=
    i1.add i2
  have hnn : 0 ≤ ∫ a, |f (X t a) - f (X t₀ a)| := integral_nonneg fun a => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hle : ∫ a, |f (X t a) - f (X t₀ a)| ≤ ∫ a, (|f (X t a) - g (X t a)| +
      |g (X t a) - g (X t₀ a)| + |g (X t₀ a) - f (X t₀ a)|) := by
    refine integral_mono ((hcomp t hf).sub (hcomp t₀ hf)).abs (i12.add i3) fun a => ?_
    have := abs_sub_le (f (X t a)) (g (X t a)) (f (X t₀ a))
    have := abs_sub_le (g (X t a)) (g (X t₀ a)) (f (X t₀ a))
    simp only
    linarith
  rw [integral_add i12 i3, integral_add i1 i2, e1, e3] at hle
  linarith

end Euler2D
