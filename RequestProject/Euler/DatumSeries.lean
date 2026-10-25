module

public import RequestProject.Euler.CircularCell
public import RequestProject.Euler.InnerCluster

/-!
# The actual circular datum and its geometric `L^q` series

The scales are those of the paper, `A_j = A₀/b^j`, `r_j = R ρ^j`.
This file supplies the scaling and summability part of Lemma `cp:lem:datum`.
-/

@[expose] public section

open MeasureTheory Real Filter Topology

namespace Euler2D

/-- The circular vorticity label `A_j W(x/r_j)` in the datum. -/
noncomputable def datumTerm (A₀ b R ρ : ℝ) (j : ℕ) (x : R2) : ℝ :=
  ampScale A₀ b j * cellW ((radScale R ρ j)⁻¹ • x)

/-- Each circular cell belongs to every `L^p`, including `L^∞`. -/
lemma cellW_memLp (p : ENNReal) : MemLp cellW p volume := by
  unfold cellW twoInterface
  simpa only [Pi.sub_def] using
    (memLp_indicator_const (s := Metric.ball (0 : R2) cellA) (μ := volume)
      p measurableSet_ball.nullMeasurableSet (5 / 2 : ℝ)
      (Or.inr measure_ball_lt_top.ne)).sub
        (memLp_indicator_const (s := Metric.ball (0 : R2) 1) (μ := volume)
          p measurableSet_ball.nullMeasurableSet (3 / 2 : ℝ)
          (Or.inr measure_ball_lt_top.ne))

/-- Dilation by `r⁻¹` changes planar volume by `r²`. -/
lemma map_volume_inv_smul {r : ℝ} (hr : 0 < r) :
    Measure.map (fun x : R2 => r⁻¹ • x) volume = ENNReal.ofReal (r ^ 2) • volume := by
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne')]
  simp only [finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv,
    abs_of_nonneg (sq_nonneg r)]

/-- Exact planar `L^q` scaling for any scalar profile. -/
lemma eLpNorm_inv_smul {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (f : R2 → ℝ) :
    eLpNorm (fun x => f (r⁻¹ • x)) (ENNReal.ofReal q) volume =
      ENNReal.ofReal (r ^ (2 / q)) * eLpNorm f (ENNReal.ofReal q) volume := by
  let e : R2 ≃ᵐ R2 := (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))).toMeasurableEquiv
  have hmap := e.measurableEmbedding.eLpNorm_map_measure (g := f) (p := ENNReal.ofReal q)
    (μ := volume)
  change eLpNorm f (ENNReal.ofReal q) (Measure.map (fun x : R2 => r⁻¹ • x) volume) =
    eLpNorm (fun x => f (r⁻¹ • x)) (ENNReal.ofReal q) volume at hmap
  rw [← hmap, map_volume_inv_smul hr,
    eLpNorm_smul_measure_of_ne_zero
      (by positivity : ENNReal.ofReal (r ^ 2) ≠ 0) f (ENNReal.ofReal q) volume]
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le, smul_eq_mul]
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r) (inv_nonneg.mpr hq.le),
    ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  congr 1

/-- Every actual datum label belongs to every finite positive `L^q`. -/
lemma datumTerm_memLp {A₀ b R ρ q : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (_hq : 0 < q)
    (j : ℕ) : MemLp (datumTerm A₀ b R ρ j) (ENNReal.ofReal q) volume := by
  have hr : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  let e : R2 ≃ᵐ R2 :=
    (Homeomorph.smul (Units.mk0 (radScale R ρ j)⁻¹ (inv_ne_zero hr.ne'))).toMeasurableEquiv
  have hmem : MemLp cellW (ENNReal.ofReal q)
      (Measure.map (fun x : R2 => (radScale R ρ j)⁻¹ • x) volume) := by
    rw [map_volume_inv_smul hr]
    exact (cellW_memLp _).smul_measure ENNReal.ofReal_ne_top
  exact (hmem.comp_of_map e.measurable.aemeasurable).const_mul (ampScale A₀ b j)

/-- The precise coefficient in the geometric `L^q` majorant. -/
lemma datum_scale_geometric {A₀ b R ρ q : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (j : ℕ) :
    ampScale A₀ b j * radScale R ρ j ^ (2 / q) =
      (A₀ * R ^ (2 / q)) * (ρ ^ (2 / q) / b) ^ j := by
  simp only [ampScale, radScale]
  have hpow : (ρ ^ j) ^ (2 / q) = (ρ ^ (2 / q)) ^ j := by
    rw [← Real.rpow_natCast_mul hρ, mul_comm (j : ℝ), Real.rpow_mul_natCast hρ]
  rw [Real.mul_rpow hR (pow_nonneg hρ j), hpow, div_pow]
  ring


/-- Exact `L^q` norm of the genuine scaled circular label. -/
lemma eLpNorm_datumTerm {A₀ b R ρ q : ℝ} (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (j : ℕ) :
    eLpNorm (datumTerm A₀ b R ρ j) (ENNReal.ofReal q) volume =
      ENNReal.ofReal (ampScale A₀ b j * radScale R ρ j ^ (2 / q)) *
        eLpNorm cellW (ENNReal.ofReal q) volume := by
  have hAj : 0 ≤ ampScale A₀ b j := div_nonneg hA (pow_pos hb j).le
  have hrj : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  change eLpNorm ((ampScale A₀ b j) • fun x => cellW ((radScale R ρ j)⁻¹ • x)) _ _ = _
  rw [eLpNorm_const_smul, eLpNorm_inv_smul hrj hq,
    ← ofReal_norm_eq_enorm, Real.norm_of_nonneg hAj, ← mul_assoc,
    ← ENNReal.ofReal_mul hAj]

/-- The actual datum label as an element of the planar Lebesgue space. -/
noncomputable def datumTermLp {A₀ b R ρ q : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (j : ℕ) : Lp ℝ (ENNReal.ofReal q) (volume : Measure R2) :=
  (datumTerm_memLp (A₀ := A₀) (b := b) hR hρ hq j).toLp (datumTerm A₀ b R ρ j)

/-- The norm sequence is the exact geometric sequence from `cp:lem:datum`. -/
lemma norm_datumTermLp {A₀ b R ρ q : ℝ} (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (j : ℕ) :
    ‖datumTermLp (A₀ := A₀) (b := b) hR hρ hq j‖ =
      (eLpNorm cellW (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (2 / q)) * (ρ ^ (2 / q) / b) ^ j := by
  rw [datumTermLp, Lp.norm_toLp, eLpNorm_datumTerm hA hb hR hρ hq,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
      exact mul_nonneg (div_nonneg hA (pow_pos hb j).le) (Real.rpow_nonneg (mul_pos hR (pow_pos hρ j)).le _)),
    datum_scale_geometric hR.le hρ.le]
  ring

/-- The numerical majorant is summable under the paper's exact condition. -/
lemma datum_scale_summable {A₀ b R ρ q : ℝ} (hb : 0 < b) (hR : 0 ≤ R)
    (hρ : 0 ≤ ρ) (hsmall : ρ ^ (2 / q) < b) :
    Summable (fun j : ℕ => ampScale A₀ b j * radScale R ρ j ^ (2 / q)) := by
  simp_rw [datum_scale_geometric hR hρ]
  exact (summable_geometric_of_lt_one (by positivity) ((div_lt_one hb).mpr hsmall)).mul_left _

/-- Absolute `L^q` summability of the actual circular vorticity series. -/
lemma summable_norm_datumTermLp {A₀ b R ρ q : ℝ} (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (hsmall : ρ ^ (2 / q) < b) :
    Summable (fun j : ℕ => ‖datumTermLp (A₀ := A₀) (b := b) hR hρ hq j‖) := by
  simp_rw [norm_datumTermLp hA hb hR hρ hq]
  exact (summable_geometric_of_lt_one (by positivity) ((div_lt_one hb).mpr hsmall)).mul_left _

/-- Convergence in `L^q` of the actual vorticity datum. -/
lemma summable_datumTermLp {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hsmall : ρ ^ (2 / q) < b) :
    Summable (datumTermLp (A₀ := A₀) (b := b) hR hρ hq) :=
  (summable_norm_datumTermLp hA hb hR hρ hq hsmall).of_norm

/-- The infinite vorticity datum, defined by the convergent `L^q` series. -/
noncomputable def circularDatumLp {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) : Lp ℝ (ENNReal.ofReal q) (volume : Measure R2) :=
  ∑' j, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j

/-- Its genuine finite circular sums converge strongly in `L^q`. -/
lemma tendsto_sum_datumTermLp {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hsmall : ρ ^ (2 / q) < b) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
      datumTermLp (A₀ := A₀) (b := b) hR hρ hq j) atTop
        (𝓝 (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)) :=
  (summable_datumTermLp hA hb hR hρ hq hsmall).hasSum.tendsto_sum_nat



/-- One geometric majorant controls every finite family of labels, independently
of the number of labels. This applies at each time after norm-preserving transport. -/
lemma uniform_finite_label_bound {p : ENNReal} [Fact (1 ≤ p)]
    {A₀ b R ρ q C : ℝ} (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hsmall : ρ ^ (2 / q) < b)
    (f : ℕ → Lp ℝ p (volume : Measure R2))
    (hf : ∀ j, ‖f j‖ ≤ C * (ampScale A₀ b j * radScale R ρ j ^ (2 / q)))
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, f j‖ ≤
      C * (A₀ * R ^ (2 / q)) / (1 - ρ ^ (2 / q) / b) := by
  let κ : ℝ := ρ ^ (2 / q) / b
  have hκ0 : 0 ≤ κ := div_nonneg (Real.rpow_nonneg hρ _) hb.le
  have hκ1 : κ < 1 := (div_lt_one hb).mpr hsmall
  have hgeom := summable_geometric_of_lt_one hκ0 hκ1
  have hsum : ∑ j ∈ Finset.range N, κ ^ j ≤ (1 - κ)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hκ0 hκ1]
    exact hgeom.sum_le_tsum _ (fun j _ => pow_nonneg hκ0 j)
  have hD : 0 ≤ C * (A₀ * R ^ (2 / q)) := by positivity
  calc
    ‖∑ j ∈ Finset.range N, f j‖ ≤ ∑ j ∈ Finset.range N, ‖f j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, (C * (A₀ * R ^ (2 / q))) * κ ^ j := by
      refine Finset.sum_le_sum fun j _ => (hf j).trans_eq ?_
      rw [datum_scale_geometric hR hρ]
      ring
    _ = (C * (A₀ * R ^ (2 / q))) * ∑ j ∈ Finset.range N, κ ^ j := by
      rw [Finset.mul_sum]
    _ ≤ (C * (A₀ * R ^ (2 / q))) * (1 - κ)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum hD
    _ = C * (A₀ * R ^ (2 / q)) / (1 - ρ ^ (2 / q) / b) := by rfl

/-- The genuine circular partial sums have one bound independent of `N`. -/
lemma norm_sum_datumTermLp_le {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hsmall : ρ ^ (2 / q) < b) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j‖ ≤
      (eLpNorm cellW (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (2 / q)) / (1 - ρ ^ (2 / q) / b) := by
  apply uniform_finite_label_bound hA hb hR.le hρ.le ENNReal.toReal_nonneg hsmall
  intro j
  rw [norm_datumTermLp hA hb hR hρ hq, datum_scale_geometric hR.le hρ.le]
  exact le_of_eq (by ring)



/-- The exact geometric tail estimate for the actual datum series. -/
lemma norm_circularDatumLp_sub_sum_le {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hsmall : ρ ^ (2 / q) < b) (N : ℕ) :
    ‖circularDatumLp (A₀ := A₀) (b := b) hR hρ hq -
      ∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j‖ ≤
      (eLpNorm cellW (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (2 / q)) * (ρ ^ (2 / q) / b) ^ N /
          (1 - ρ ^ (2 / q) / b) := by
  let f := datumTermLp (A₀ := A₀) (b := b) hR hρ hq
  let κ : ℝ := ρ ^ (2 / q) / b
  have hκ0 : 0 ≤ κ := div_nonneg (Real.rpow_nonneg hρ.le _) hb.le
  have hκ1 : κ < 1 := (div_lt_one hb).mpr hsmall
  have hs := summable_datumTermLp hA hb hR hρ hq hsmall
  have hn := (summable_nat_add_iff N).mpr
    (summable_norm_datumTermLp hA hb hR hρ hq hsmall)
  have heq : circularDatumLp (A₀ := A₀) (b := b) hR hρ hq -
      ∑ j ∈ Finset.range N, f j = ∑' j, f (j + N) := by
    have hid := Summable.sum_add_tsum_nat_add N hs
    change ∑' j, f j - ∑ j ∈ Finset.range N, f j = _
    rw [← hid]
    abel
  rw [heq]
  calc
    ‖∑' j, f (j + N)‖ ≤ ∑' j, ‖f (j + N)‖ := norm_tsum_le_tsum_norm hn
    _ = ((eLpNorm cellW (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (2 / q)) * κ ^ N) * ∑' j : ℕ, κ ^ j := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      dsimp only [f]
      rw [norm_datumTermLp hA hb hR hρ hq, pow_add]
      dsimp only [κ]
      ring
    _ = (eLpNorm cellW (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (2 / q)) * (ρ ^ (2 / q) / b) ^ N /
          (1 - ρ ^ (2 / q) / b) := by
      rw [tsum_geometric_of_lt_one hκ0 hκ1]
      rfl

/-- The circular cell has zero circulation. -/
lemma integral_cellW : ∫ x, cellW x = 0 := by
  have hv₁ : volume (Metric.ball (0 : R2) cellA) = ENNReal.ofReal (3 * π / 5) := by
    rw [← ENNReal.ofReal_toReal (a := volume (Metric.ball (0 : R2) cellA)) measure_ball_lt_top.ne]
    change ENNReal.ofReal (volume.real (Metric.ball (0 : R2) cellA)) = _
    rw [volReal_ball cellA cellA_pos.le, cellA_sq]
    congr 1
    ring
  have hv₂ : volume (Metric.ball (0 : R2) 1) = ENNReal.ofReal π := by simp
  exact (twoInterface_integral (Metric.ball_subset_ball cellA_lt_one.le)
    measurableSet_ball measurableSet_ball hv₁ hv₂).1

/-- Every actual scaled label has zero circulation. -/
lemma integral_datumTerm {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (j : ℕ) :
    ∫ x, datumTerm A₀ b R ρ j x = 0 := by
  have hr : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  unfold datumTerm
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume cellW
    hr.le, integral_cellW]
  simp



/-- A label at scale `N` vanishes in norm when its norm has the geometric
bound used for the finite base cell. -/
lemma tendsto_zero_of_datum_scale_bound {E : Type*} [NormedAddCommGroup E]
    {A₀ b R ρ q C : ℝ} (hb : 0 < b) (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (hsmall : ρ ^ (2 / q) < b) (f : ℕ → E)
    (hf : ∀ N, ‖f N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q))) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (Real.rpow_nonneg hρ _) hb.le) ((div_lt_one hb).mpr hsmall)
  have hlim : Tendsto (fun N : ℕ =>
      (C * (A₀ * R ^ (2 / q))) * (ρ ^ (2 / q) / b) ^ N) atTop (𝓝 0) := by
    simpa using hpow.const_mul (C * (A₀ * R ^ (2 / q)))
  apply squeeze_zero (fun N => norm_nonneg (f N)) _ hlim
  intro N
  exact (hf N).trans_eq (by rw [datum_scale_geometric hR hρ]; ring)

/-- Replacing the last circular block by any uniformly controlled base cell
preserves convergence to the genuine infinite datum. -/
lemma tendsto_finite_base_datum {A₀ b R ρ q C : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hsmall : ρ ^ (2 / q) < b)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (hbase : ∀ N, ‖base N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q))) :
    Tendsto (fun N => (∑ j ∈ Finset.range N,
      datumTermLp (A₀ := A₀) (b := b) hR hρ hq j) + base N) atTop
        (𝓝 (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)) := by
  simpa using (tendsto_sum_datumTermLp hA hb hR hρ hq hsmall).add
    (tendsto_zero_of_datum_scale_bound hb hR.le hρ.le hsmall base hbase)



/-- Norm conservation under actual volume-preserving transport, followed by
the exact scaling of each circular datum label. -/
lemma eLpNorm_transportedDatumTerm {A₀ b R ρ q : ℝ} (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (j : ℕ)
    {X : R2 → R2} (hX : MeasurePreserving X volume volume) :
    eLpNorm (datumTerm A₀ b R ρ j ∘ X) (ENNReal.ofReal q) volume =
      ENNReal.ofReal (ampScale A₀ b j * radScale R ρ j ^ (2 / q)) *
        eLpNorm cellW (ENNReal.ofReal q) volume := by
  rw [eLpNorm_comp_measurePreserving (datumTerm_memLp (A₀ := A₀) (b := b) hR hρ hq j).aestronglyMeasurable hX,
    eLpNorm_datumTerm hA hb hR hρ hq]


end Euler2D

end


