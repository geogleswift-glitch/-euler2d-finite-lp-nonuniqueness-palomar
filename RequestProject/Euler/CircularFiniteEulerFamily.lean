module

public import RequestProject.Euler.CircularFiniteInitialDensity
public import RequestProject.Euler.FourfoldBoundedEulerConstruction
public import RequestProject.Euler.FiniteFlowLimit

/-! Genuine finite Euler systems for the actual ancient base. The common
vorticity bound and convergence of the initial velocities are consequences
of the construction. A uniform nonzero departure is still to be proved. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

theorem sum_datumTermLp_ae {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (N : ℕ) :
    ((∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j :
      Lp ℝ (ENNReal.ofReal q) (volume : Measure R2)) : R2 → ℝ) =ᵐ[volume]
        fun x => ∑ j ∈ Finset.range N, datumTerm A₀ b R ρ j x := by
  induction N with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, Pi.zero_def] using
      (Lp.coeFn_zero ℝ (ENNReal.ofReal q) (volume : Measure R2))
  | succ N ih =>
      rw [Finset.sum_range_succ]
      filter_upwards [Lp.coeFn_add
        (∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j)
        (datumTermLp (A₀ := A₀) (b := b) hR hρ hq N), ih,
        (datumTerm_memLp (A₀ := A₀) (b := b) hR hρ hq N).coeFn_toLp] with x ha hi ht
      change datumTermLp (A₀ := A₀) (b := b) hR hρ hq N x = datumTerm A₀ b R ρ N x at ht
      simpa only [Pi.add_apply, hi, ht, Finset.sum_range_succ] using ha

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteInitialPlanarLp_ae {s A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (N : ℕ) :
    (((∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j) +
      P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ N :
        Lp ℝ (ENNReal.ofReal q) (volume : Measure R2)) : R2 → ℝ) =ᵐ[volume]
      P.finiteInitialPlanarDensity s A₀ b R ρ N := by
  filter_upwards [Lp.coeFn_add
      (∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j)
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ N),
    sum_datumTermLp_ae (A₀ := A₀) (b := b) hR hρ hq N,
    P.finiteBaseLp_ae (A₀ := A₀) (b := b) (q := q) hs hR hρ N] with x ha ht hb
  simpa only [Pi.add_apply, ht, hb, finiteInitialPlanarDensity] using ha

theorem finiteBaseTorusLp_ae_density {s A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (N : ℕ) :
    (finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hq
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) =ᵐ[μT]
      fun x => P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter) :=
  (centeredPlanarLp_ae _).trans (ae_restrict_of_ae
    ((measurePreserving_sub_right volume torusCenter).quasiMeasurePreserving.ae_eq
      (P.finiteInitialPlanarLp_ae hs hR hρ hq N)))

theorem finiteBaseCurlL2_ae_density {s A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q)
    (hqE : 2 ≤ ENNReal.ofReal q) (N : ℕ) :
    (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) =ᵐ[μT]
      fun x => P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter) :=
  (scalarLpLowerToTwo_ae hqE _).trans (P.finiteBaseTorusLp_ae_density hs hR hρ hq N)

theorem integral_finiteBaseTorusLp_zero {s A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hq : 0 < q) (N : ℕ) :
    (∫ x in torusBox, finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hq
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x) = 0 := by
  rw [integral_congr_ae (P.finiteBaseTorusLp_ae_density hs hR hρ hq N)]
  calc
    _ = ∫ x in torusBox, P.finiteInitialPeriodicDensity s A₀ b R ρ N x :=
      setIntegral_congr_fun measurableSet_torusBox (fun x hx =>
        (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx).symm)
    _ = 0 := P.integral_finiteInitialPeriodicDensity_zero hs hR hRmax hρ hρ1 N

theorem exists_finiteBase_fourfoldEuler {s A₀ b R ρ q T : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hT : 0 ≤ T) (N : ℕ) :
    ∃ S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S ∧ IsWeakEulerSolution T
        (biotSavartL2 (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N))
        (particleVelocity (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
          S.backward S.backward_area) := by
  let f := finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
    (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N
  have hf := P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_torusBox] with x hfx hx
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx).trans hfx.symm
  have hmean : (∫ x in torusBox, f x) = 0 :=
    (integral_congr_ae (scalarLpLowerToTwo_ae hqE _)).trans
      (P.integral_finiteBaseTorusLp_zero hs hR hRmax hρ hρ1 hq N)
  have hB : ∀ᵐ x ∂μT, ‖f x‖ ≤ finiteInitialDensityBound A₀ b N := by
    filter_upwards [hf] with x hx
    rw [hx]
    exact P.norm_finiteInitialPlanarDensity_le hs N _
  exact exists_fourfoldBoundedVorticity_weakEuler f hwf
    (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
    (P.finiteInitialPeriodicDensity_quarterTurn hs N) hT hmean
    (finiteInitialDensityBound_nonneg A₀ b N) hB

theorem exists_finiteEulerFamily {s A₀ b R ρ q T : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 < q) (hq2 : 2 ≤ q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hsmall : ρ ^ (2 / q) < b) (hT : 0 ≤ T) :
    ∃ S : ∀ N, BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      (∀ N, IsFourfoldBoundedEulerParticleSystem (S N)) ∧
      (∀ N, IsWeakEulerSolution T
        (biotSavartL2 (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N))
        (particleVelocity (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
          (S N).backward (S N).backward_area)) ∧
      (∀ N, CurlBoundedBy T (ENNReal.ofReal q)
        (finiteBaseNormBound A₀ b R ρ q
          (eLpNorm (circularPhasePatchPlanarVorticity (P.ancient s)) (ENNReal.ofReal q) volume).toReal)
        (particleVelocity (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
          (S N).backward (S N).backward_area)) ∧
      Tendsto (fun N => biotSavartL2
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)) atTop
        (𝓝 (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ)) := by
  choose S hS hweak using fun N => P.exists_finiteBase_fourfoldEuler
    (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 hq hqE hT N
  refine ⟨S, hS, hweak, ?_, ?_⟩
  · intro N t ht
    have hc := curlBoundedBy_particleVelocity hqE
      (finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hq
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
      (P.integral_finiteBaseTorusLp_zero hs hR hRmax hρ hρ1 hq N)
      (S N).backward (S N).backward_area T
    obtain ⟨w, hw, hc, hn⟩ := hc t ht
    refine ⟨w, hw, hc, hn.trans ?_⟩
    exact norm_finiteBaseTorusLp_le hA hb hR hρ hq ENNReal.toReal_nonneg hsmall _
      (fun k => (P.norm_finiteBaseLp hs hA hb hR hρ hq k).le) N
  · exact tendsto_biotSavartL2_finite_base hA hb hR (by linarith) hρ hρ1 hq hq2 hqE hsmall _
      (fun N => (P.norm_finiteBaseLp hs hA hb hR hρ hq N).le)

end CircularMaterialTransferProfile

end Euler2D

end
