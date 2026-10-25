module

public import RequestProject.Euler.FiniteInitialConvergence

/-!
# Uniform finite vorticity bounds from the common particle flow

The initial labels are the physical circular partial sum with an arbitrary
controlled base cell. Translation, restriction and an actual
measure-preserving inverse flow give a bound independent of the cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

lemma centeredPlanarLp_norm_le {p : ENNReal} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume : Measure R2)) : ‖centeredPlanarLp p f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (centeredPlanarLp_ae f)]
  have heq : eLpNorm (fun x : R2 => f (x - torusCenter)) p volume =
      eLpNorm f p volume :=
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f)
      (measurePreserving_sub_right volume torusCenter)
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq heq

def finiteBaseNormBound (A₀ b R ρ q C : ℝ) : ℝ :=
  ((eLpNorm cellW (ENNReal.ofReal q) volume).toReal / (1 - ρ ^ (2 / q) / b) + C) *
    (A₀ * R ^ (2 / q))

/-- The actual finite noncircular initial vorticities have one norm bound. -/
theorem norm_finite_base_datum_le {A₀ b R ρ q C : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hC : 0 ≤ C) (hsmall : ρ ^ (2 / q) < b)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (hbase : ∀ N, ‖base N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q)))
    (N : ℕ) :
    ‖(∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j) + base N‖ ≤
      finiteBaseNormBound A₀ b R ρ q C := by
  have hκ0 : 0 ≤ ρ ^ (2 / q) / b := by positivity
  have hκ1 : ρ ^ (2 / q) / b < 1 := (div_lt_one hb).mpr hsmall
  have hlast : ‖base N‖ ≤ C * (A₀ * R ^ (2 / q)) := by
    calc
      _ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q)) := hbase N
      _ = (C * (A₀ * R ^ (2 / q))) * (ρ ^ (2 / q) / b) ^ N := by
        rw [datum_scale_geometric hR.le hρ.le]
        ring
      _ ≤ (C * (A₀ * R ^ (2 / q))) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hκ0 hκ1.le) (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ ‖∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j‖ + ‖base N‖ :=
      norm_add_le _ _
    _ ≤ (eLpNorm cellW (ENNReal.ofReal q) volume).toReal *
          (A₀ * R ^ (2 / q)) / (1 - ρ ^ (2 / q) / b) + C * (A₀ * R ^ (2 / q)) :=
      add_le_add (norm_sum_datumTermLp_le hA hb hR hρ hq hsmall N) hlast
    _ = _ := by unfold finiteBaseNormBound; ring

/-- Embed the actual finite scalar datum into the original torus. -/
def finiteBaseTorusLp {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (N : ℕ) : Lp ℝ (ENNReal.ofReal q) μT :=
  centeredPlanarLp (ENNReal.ofReal q)
    ((∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j) + base N)

theorem norm_finiteBaseTorusLp_le {A₀ b R ρ q C : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hC : 0 ≤ C) (hsmall : ρ ^ (2 / q) < b)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (hbase : ∀ N, ‖base N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q)))
    (N : ℕ) :
    ‖finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hq base N‖ ≤
      finiteBaseNormBound A₀ b R ρ q C :=
  (centeredPlanarLp_norm_le _).trans
    (norm_finite_base_datum_le hA hb hR hρ hq hC hsmall base hbase N)

/-- Actual common measure-preserving transport yields the uniform curl
bound required by the compactness theorem, including the noncircular base. -/
theorem curlBoundedBy_of_finite_base_transport {A₀ b R ρ q C T : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hC : 0 ≤ C) (hsmall : ρ ^ (2 / q) < b)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (hbase : ∀ N, ‖base N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q)))
    (U : ℕ → ℝ → L2T) (Y : ℕ → ℝ → R2 → R2)
    (hY : ∀ N t, t ∈ Icc 0 T → MeasurePreserving (Y N t) μT μT)
    (hcurl : ∀ N t, t ∈ Icc 0 T → IsCurl (U N t)
      (fun x => finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hq base N (Y N t x))) :
    ∀ N, CurlBoundedBy T (ENNReal.ofReal q) (finiteBaseNormBound A₀ b R ρ q C) (U N) := by
  intro N t ht
  let f := finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hq base N
  refine ⟨fun x => f (Y N t x), (Lp.memLp f).comp_measurePreserving (hY N t ht),
    hcurl N t ht, ?_⟩
  change (eLpNorm ((f : R2 → ℝ) ∘ Y N t) (ENNReal.ofReal q) μT).toReal ≤ _
  rw [eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) (hY N t ht)]
  exact norm_finiteBaseTorusLp_le hA hb hR hρ hq hC hsmall base hbase N

end Euler2D

end
