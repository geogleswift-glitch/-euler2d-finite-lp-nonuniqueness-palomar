module

public import RequestProject.Euler.AnnularSupport

/-! Genuine topology of a radial domain. The angular radius is allowed
to cross the principal-argument cut: its periodic quotient, rather than
the discontinuous real argument, supplies continuity. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric

namespace Euler2D

def starDomainGauge (R : ℝ → ℝ) (z : ℂ) : ℝ := ‖z‖ / R (Complex.arg z)

@[simp] theorem starDomainGauge_zero (R : ℝ → ℝ) : starDomainGauge R 0 = 0 := by
  simp [starDomainGauge]

theorem starDomainGauge_nonneg {R : ℝ → ℝ} (hR : ∀ θ, 0 < R θ) (z : ℂ) :
    0 ≤ starDomainGauge R z := div_nonneg (norm_nonneg _) (hR _).le

theorem starDomain_eq_gauge_lt_one {R : ℝ → ℝ} (hR : ∀ θ, 0 < R θ) :
    starDomain R = {z | starDomainGauge R z < 1} := by
  ext z
  simp only [starDomain, mem_setOf_eq, starDomainGauge, div_lt_one (hR _)]

theorem continuousAt_periodic_comp_arg {R : ℝ → ℝ}
    (hR : Continuous R) (hp : Function.Periodic R (2 * Real.pi))
    {z : ℂ} (hz : z ≠ 0) : ContinuousAt (fun w => R (Complex.arg w)) z := by
  have hq : Topology.IsQuotientMap (fun θ : ℝ => (θ : Real.Angle)) :=
    isQuotientMap_quotient_mk'
  have hl : Continuous hp.lift := hq.continuous_iff.mpr hR
  exact hl.continuousAt.comp (Complex.continuousAt_arg_coe_angle hz)

theorem continuous_starDomainGauge {R : ℝ → ℝ} {a : ℝ}
    (hR : Continuous R) (hp : Function.Periodic R (2 * Real.pi))
    (ha : 0 < a) (hlo : ∀ θ, a ≤ R θ) : Continuous (starDomainGauge R) := by
  have hpos (θ : ℝ) : 0 < R θ := ha.trans_le (hlo θ)
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨a * ε, mul_pos ha hε, ?_⟩
    intro w hw
    rw [starDomainGauge_zero, dist_zero_right,
      Real.norm_eq_abs, abs_of_nonneg (starDomainGauge_nonneg hpos w)]
    change ‖w‖ / R (arg w) < ε
    apply (div_lt_iff₀ (hpos _)).mpr
    rw [dist_zero_right] at hw
    exact hw.trans_le (by nlinarith [hlo (arg w)])
  · exact continuous_norm.continuousAt.div
      (continuousAt_periodic_comp_arg hR hp hz) (hpos _).ne'

theorem isOpen_starDomain {R : ℝ → ℝ} {a : ℝ}
    (hR : Continuous R) (hp : Function.Periodic R (2 * Real.pi))
    (ha : 0 < a) (hlo : ∀ θ, a ≤ R θ) : IsOpen (starDomain R) := by
  rw [starDomain_eq_gauge_lt_one (fun θ => ha.trans_le (hlo θ))]
  exact isOpen_lt (continuous_starDomainGauge hR hp ha hlo) continuous_const

theorem starDomainGauge_real_smul {R : ℝ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (z : ℂ) : starDomainGauge R (t • z) = t * starDomainGauge R z := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    simp
  · rw [starDomainGauge, Complex.real_smul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, Complex.arg_real_mul _ ht]
    unfold starDomainGauge
    ring

theorem closure_starDomain {R : ℝ → ℝ} {a : ℝ}
    (hR : Continuous R) (hp : Function.Periodic R (2 * Real.pi))
    (ha : 0 < a) (hlo : ∀ θ, a ≤ R θ) :
    closure (starDomain R) = {z | starDomainGauge R z ≤ 1} := by
  have hpos (θ : ℝ) : 0 < R θ := ha.trans_le (hlo θ)
  have hD := starDomain_eq_gauge_lt_one hpos
  apply Subset.antisymm
  · apply closure_minimal
    · rw [hD]
      intro z hz
      exact (show starDomainGauge R z < 1 from hz).le
    · exact isClosed_le (continuous_starDomainGauge hR hp ha hlo) continuous_const
  · intro z hz
    have ht : Tendsto (fun t : ℝ => t • z) (𝓝[<] (1 : ℝ)) (𝓝 z) := by
      have hc : Continuous (fun t : ℝ => t • z) := continuous_id.smul continuous_const
      simpa only [one_smul] using (hc.continuousAt (x := 1)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    apply mem_closure_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with t ht h0
    rw [hD]
    change starDomainGauge R (t • z) < 1
    rw [starDomainGauge_real_smul h0.le]
    exact (mul_le_mul_of_nonneg_left hz h0.le).trans_lt (by simpa using ht)

theorem frontier_starDomain {R : ℝ → ℝ} {a : ℝ}
    (hR : Continuous R) (hp : Function.Periodic R (2 * Real.pi))
    (ha : 0 < a) (hlo : ∀ θ, a ≤ R θ) :
    frontier (starDomain R) = {z | starDomainGauge R z = 1} := by
  rw [frontier, (isOpen_starDomain hR hp ha hlo).interior_eq,
    closure_starDomain hR hp ha hlo,
    starDomain_eq_gauge_lt_one (fun θ => ha.trans_le (hlo θ))]
  ext z
  simp only [mem_diff, mem_setOf_eq, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem periodic_apply_eq_of_exp_mul_I_eq {R : ℝ → ℝ}
    (hp : Function.Periodic R (2 * Real.pi)) {θ φ : ℝ}
    (he : Complex.exp ((θ : ℂ) * I) = Complex.exp ((φ : ℂ) * I)) : R θ = R φ := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hreal : θ = φ + (n : ℝ) * (2 * Real.pi) := by
    have hi := congrArg Complex.im hn
    simpa [Complex.mul_im, Complex.mul_re] using hi
  rw [hreal]
  exact hp.int_mul n φ

theorem periodic_apply_arg_exp_mul_I {R : ℝ → ℝ}
    (hp : Function.Periodic R (2 * Real.pi)) (θ : ℝ) :
    R (Complex.arg (Complex.exp ((θ : ℂ) * I))) = R θ := by
  apply periodic_apply_eq_of_exp_mul_I_eq hp
  have h := Complex.norm_mul_exp_arg_mul_I (Complex.exp ((θ : ℂ) * I))
  simpa only [Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, one_mul] using h

/-- The frontier is the genuine polar graph, with no Jordan-curve input. -/
theorem frontier_starDomain_eq_range {R : ℝ → ℝ} {a : ℝ}
    (hR : Continuous R) (hp : Function.Periodic R (2 * Real.pi))
    (ha : 0 < a) (hlo : ∀ θ, a ≤ R θ) :
    frontier (starDomain R) = Set.range (fun θ : ℝ =>
      (R θ : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  have hpos (θ : ℝ) : 0 < R θ := ha.trans_le (hlo θ)
  rw [frontier_starDomain hR hp ha hlo]
  apply Subset.antisymm
  · intro z hz
    refine ⟨Complex.arg z, ?_⟩
    dsimp only
    have he : ‖z‖ = R (arg z) := (div_eq_one_iff_eq (hpos _).ne').mp hz
    rw [← he]
    exact Complex.norm_mul_exp_arg_mul_I z
  · rintro z ⟨θ, rfl⟩
    change starDomainGauge R _ = 1
    rw [starDomainGauge, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hpos θ), Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.arg_real_mul _ (hpos θ), periodic_apply_arg_exp_mul_I hp,
      div_self (hpos θ).ne']

end Euler2D
