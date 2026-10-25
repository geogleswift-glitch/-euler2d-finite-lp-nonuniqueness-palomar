module

public import Mathlib

/-!
# Interior derivatives of a harmonic function (Lemma `ib:lem:harmonic`)

The plane is identified with `ℂ`. If `h` is harmonic on `B_{4Cr}` and `|h| ≤ M` there,
then every derivative of the rescaled function `ξ ↦ h (r ξ)` on `B_{2C}` is bounded by a
constant depending only on the order and on `C`, times `M`:
`‖Dʲ (h (r ·))(ξ)‖ ≤ j! (5 / Cʲ) M` (`harmonic_interior_derivatives`).

The proof writes `h` as the real part of a holomorphic function, controls that function on a
circle by the Borel–Carathéodory theorem, and finishes with Cauchy's estimate.
-/

@[expose] public section

open Complex Metric Set Filter

namespace Euler2D

/-- Cauchy-type bound for a holomorphic function whose real part is bounded: if `Φ` is
holomorphic on `ball 0 (4C)`, `Re Φ ≤ M` there, `Φ ξ` is real and `|Φ ξ| ≤ M`, with
`|ξ| < 2C`, then `‖Φ⁽ʲ⁾(ξ)‖ ≤ j! (5M + 2ε) / Cʲ` for every `ε > 0`. -/
lemma iteratedDeriv_bound_of_re_le {Φ : ℂ → ℂ} {C M ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (hΦ : DifferentiableOn ℂ Φ (ball 0 (4 * C)))
    (hre : ∀ z ∈ ball (0 : ℂ) (4 * C), (Φ z).re ≤ M)
    {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (2 * C)) (hξim : (Φ ξ).im = 0) (hξM : |(Φ ξ).re| ≤ M)
    (j : ℕ) :
    ‖iteratedDeriv j Φ ξ‖ ≤ j.factorial * (5 * M + 2 * ε) / C ^ j := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) hξM
  have hξ' : ‖ξ‖ < 2 * C := by simpa using hξ
  -- shifted function on `ball 0 (2C)`
  set Ψ : ℂ → ℂ := fun w => Φ (ξ + w) with hΨ
  have hsub : ∀ w ∈ ball (0 : ℂ) (2 * C), ξ + w ∈ ball (0 : ℂ) (4 * C) := by
    intro w hw
    have hw' : ‖w‖ < 2 * C := by simpa using hw
    simp only [mem_ball, dist_zero_right]
    calc ‖ξ + w‖ ≤ ‖ξ‖ + ‖w‖ := norm_add_le _ _
      _ < 4 * C := by linarith
  have hΨd : DifferentiableOn ℂ Ψ (ball 0 (2 * C)) := by
    intro w hw
    have := (hΦ (ξ + w) (hsub w hw)).differentiableAt (isOpen_ball.mem_nhds (hsub w hw))
    exact (this.comp w ((differentiableAt_id).const_add ξ)).differentiableWithinAt
  have hΨre : MapsTo Ψ (ball 0 (2 * C)) {z | z.re < M + ε} := by
    intro w hw
    have := hre _ (hsub w hw)
    show (Φ (ξ + w)).re < M + ε
    linarith
  have hsphere : ∀ z ∈ sphere ξ C, ‖Φ z‖ ≤ 5 * M + 2 * ε := by
    intro z hz
    have hz' : ‖z - ξ‖ = C := by simpa [dist_eq_norm] using hz
    have hw : z - ξ ∈ ball (0 : ℂ) (2 * C) := by
      simp only [mem_ball, dist_zero_right, hz']; linarith
    have hBC := borelCaratheodory (M := M + ε) (R := 2 * C) (f := Ψ) (z := z - ξ)
      (by linarith) hΨd (by
        intro w hw
        have hlt : (Ψ w).re < M + ε := by
          simpa only [Set.mem_ofPred_eq] using hΨre hw
        simpa only [Set.mem_ofPred_eq] using hlt.le) (by linarith) hw
    have h0 : ‖Ψ 0‖ ≤ M := by
      have : Ψ 0 = ((Φ ξ).re : ℂ) := by
        apply Complex.ext <;> simp [hΨ, hξim]
      rw [this, norm_real, Real.norm_eq_abs]; exact hξM
    rw [hz'] at hBC
    have hΨz : Ψ (z - ξ) = Φ z := by simp [hΨ]
    rw [hΨz] at hBC
    have e1 : 2 * (M + ε) * C / (2 * C - C) = 2 * (M + ε) := by field_simp; ring
    have e2 : ‖Ψ 0‖ * (2 * C + C) / (2 * C - C) = 3 * ‖Ψ 0‖ := by field_simp; ring
    rw [e1, e2] at hBC
    linarith
  have hdc : DiffContOnCl ℂ Φ (ball ξ C) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hC.ne']
    apply hΦ.mono
    intro z hz
    have hz' : ‖z - ξ‖ ≤ C := by simpa [dist_eq_norm] using hz
    simp only [mem_ball, dist_zero_right]
    calc ‖z‖ = ‖(z - ξ) + ξ‖ := by ring_nf
      _ ≤ ‖z - ξ‖ + ‖ξ‖ := norm_add_le _ _
      _ < 4 * C := by linarith
  exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hC hdc hsphere

/-- **Lemma `ib:lem:harmonic`** (*Interior derivatives of a harmonic function*).
If `h` is harmonic on `B_{4Cr}` and bounded there by `M`, then for every order `j` and every
`ξ ∈ B_{2C}` the `j`-th derivative of `ξ ↦ h (r ξ)` satisfies
`‖Dʲ (h (r ·))(ξ)‖ ≤ j! · 5 / Cʲ · M`. In particular the `C^m(B_{2C})` norm of `h (r ·)` is
at most `C_{m,C} ‖h‖_{L^∞(B_{4Cr})}` with `C_{m,C} = 5 ∑_{j ≤ m} j!/Cʲ`, independent of `r`
and `h`. -/
theorem harmonic_interior_derivatives {h : ℂ → ℝ} {C r M : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hh : InnerProductSpace.HarmonicOnNhd h (ball 0 (4 * C * r)))
    (hM : ∀ z ∈ ball (0 : ℂ) (4 * C * r), |h z| ≤ M)
    {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (2 * C)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun ζ : ℂ => h (r * ζ)) ξ‖ ≤ j.factorial * 5 / C ^ j * M := by
  obtain ⟨F, hFan, hFre⟩ := harmonic_is_realOfHolomorphic hh
  have hmaps : ∀ ζ ∈ ball (0 : ℂ) (4 * C), (r : ℂ) * ζ ∈ ball (0 : ℂ) (4 * C * r) := by
    intro ζ hζ
    have : ‖ζ‖ < 4 * C := by simpa using hζ
    simp only [mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    nlinarith
  set c : ℂ := ((F (r * ξ)).im : ℂ) * I with hc
  set Φ : ℂ → ℂ := fun ζ => F (r * ζ) - c with hΦ
  have hΦan : ∀ ζ ∈ ball (0 : ℂ) (4 * C), AnalyticAt ℂ Φ ζ := by
    intro ζ hζ
    have h1 : AnalyticAt ℂ F ((r : ℂ) * ζ) := hFan _ (hmaps ζ hζ)
    have h2 : AnalyticAt ℂ (fun ζ : ℂ => (r : ℂ) * ζ) ζ := by fun_prop
    exact (h1.comp_of_eq h2 rfl).sub analyticAt_const
  have hΦd : DifferentiableOn ℂ Φ (ball 0 (4 * C)) :=
    fun ζ hζ => (hΦan ζ hζ).differentiableAt.differentiableWithinAt
  have hreΦ : ∀ ζ ∈ ball (0 : ℂ) (4 * C), (Φ ζ).re = h (r * ζ) := by
    intro ζ hζ
    have := hFre (hmaps ζ hζ)
    simp only [hΦ, hc, sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, sub_zero]
    simpa using this
  have hξ4 : ξ ∈ ball (0 : ℂ) (4 * C) := by
    have : ‖ξ‖ < 2 * C := by simpa using hξ
    simp only [mem_ball, dist_zero_right]; linarith
  have hre : ∀ z ∈ ball (0 : ℂ) (4 * C), (Φ z).re ≤ M := by
    intro z hz
    rw [hreΦ z hz]
    have := hM _ (hmaps z hz)
    exact le_trans (le_abs_self _) this
  have hξim : (Φ ξ).im = 0 := by simp [hΦ, hc]
  have hξM : |(Φ ξ).re| ≤ M := by
    rw [hreΦ ξ hξ4]; exact hM _ (hmaps ξ hξ4)
  -- bound on the complex derivative
  have hbound : ‖iteratedDeriv j Φ ξ‖ ≤ j.factorial * 5 / C ^ j * M := by
    have key : ∀ ε > 0, ‖iteratedDeriv j Φ ξ‖ ≤ j.factorial * (5 * M + 2 * ε) / C ^ j :=
      fun ε hε => iteratedDeriv_bound_of_re_le hC hε hΦd hre hξ hξim hξM j
    have hCj : 0 < C ^ j := pow_pos hC j
    have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set ε := δ * C ^ j / (4 * j.factorial) with hεdef
    have hε : 0 < ε := by positivity
    have := key ε hε
    have e : (j.factorial : ℝ) * (5 * M + 2 * ε) / C ^ j
        = j.factorial * 5 / C ^ j * M + δ / 2 := by
      rw [hεdef]; field_simp; ring
    linarith
  -- comparison of the real iterated derivative with the complex one
  have hev : (fun ζ : ℂ => h (r * ζ)) =ᶠ[nhds ξ] (reCLM ∘ Φ) := by
    filter_upwards [isOpen_ball.mem_nhds hξ4] with ζ hζ
    simp [hreΦ ζ hζ]
  have hcd : ContDiffAt ℂ j Φ ξ := (hΦan ξ hξ4).contDiffAt
  have hcdR : ContDiffAt ℝ j Φ ξ := hcd.restrict_scalars ℝ
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds,
    ContinuousLinearMap.iteratedFDeriv_comp_left _ hcdR le_rfl]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have hre1 : ‖(reCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 := by simp
  rw [← hcd.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  calc ‖(reCLM : ℂ →L[ℝ] ℝ)‖ *
        ‖((ContinuousMultilinearMap.restrictScalars ℝ) ∘ iteratedFDeriv ℂ j Φ) ξ‖
      ≤ 1 * ‖iteratedFDeriv ℂ j Φ ξ‖ := by
        gcongr
        exact (ContinuousMultilinearMap.norm_restrictScalars _).le
    _ = ‖iteratedDeriv j Φ ξ‖ := by rw [one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ ≤ _ := hbound

/-- **Lemma `ib:lem:harmonic`**, `C^m` form: there is a constant `C_{m,C}`, independent of `r`
and `h`, such that all derivatives of order `≤ m` of `h (r ·)` on `B_{2C}` are bounded by
`C_{m,C} ‖h‖_{L^∞(B_{4Cr})}`. -/
theorem harmonic_Cm_bound (m : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ K : ℝ, ∀ (h : ℂ → ℝ) (r M : ℝ), 0 < r →
      InnerProductSpace.HarmonicOnNhd h (ball 0 (4 * C * r)) →
      (∀ z ∈ ball (0 : ℂ) (4 * C * r), |h z| ≤ M) →
      ∀ ξ ∈ ball (0 : ℂ) (2 * C), ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun ζ : ℂ => h (r * ζ)) ξ‖ ≤ K * M := by
  refine ⟨∑ j ∈ Finset.range (m + 1), (j.factorial * 5 / C ^ j : ℝ), ?_⟩
  intro h r M hr hh hM ξ hξ j hj
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (4 * C * r) := mem_ball_self (by positivity)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 h0)
  refine (harmonic_interior_derivatives hC hr hh hM hξ j).trans ?_
  gcongr
  exact Finset.single_le_sum (f := fun j : ℕ => (j.factorial * 5 / C ^ j : ℝ))
    (fun i _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

end Euler2D
