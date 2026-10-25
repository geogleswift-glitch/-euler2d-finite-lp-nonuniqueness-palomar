module

public import RequestProject.Euler.LagrangianEuler
public import RequestProject.Euler.BiotSavartDatum
public import RequestProject.Euler.FiniteTransportBounds
public import RequestProject.Euler.DepartureTest
public import RequestProject.Euler.LimitAssembly

/-!
# The limit proposition from finite particle flows and a fixed moment test

The datum, the finite initial velocities, their convergence, the weak
momentum equations, uniform curl bounds and compactness are all supplied
by proved constructions. The remaining inputs concern the actual finite
particle flows and their uniformly nonzero fixed-test moment at an
interior time. Existence of those flows and moments is not postulated.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace Euler2D

lemma finiteBaseCurlL2_eq_lower {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2)) (N : ℕ) :
    finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE base N =
      scalarLpLowerToTwo hqE (finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hq base N) := rfl

def finiteParticleVelocity {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (Y : ℕ → ℝ → R2 → R2) (hY : ∀ N t, TorusAreaPreserving (Y N t)) : ℕ → ℝ → L2T :=
  fun N => particleVelocity (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE base N)
    (Y N) (hY N)

/-- The original limit conclusion from genuine finite particle systems.
The fixed-test moment input is a property of those systems; it has not
been assumed as an axiom or shown to be satisfiable here. -/
theorem limit_solution_of_finite_particle_flows
    {T A₀ b R ρ p q C a btime δ : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hT : 0 < T) (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hqpos : 0 < q) (hq : 2 ≤ q)
    (hqE : 2 ≤ ENNReal.ofReal q) (hp : 1 < p) (hpq : p ≤ q)
    (hC : 0 ≤ C) (hsmall : ρ ^ (2 / q) < b)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (hbase : ∀ N, ‖base N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q)))
    (hcirculation : ∀ N, (∫ x in torusBox,
      finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hqpos base N x) = 0)
    (X Y v : ℕ → ℝ → R2 → R2)
    (hY : ∀ N t, TorusAreaPreserving (Y N t))
    (hYc : ∀ N, Continuous (Function.uncurry (Y N)))
    (hXc : ∀ N, Continuous (Function.uncurry (X N)))
    (hvc : ∀ N, Continuous (Function.uncurry (v N)))
    (hvper : ∀ N t, IsTorusPeriodic (v N t))
    (hXmp : ∀ N t, t ∈ Icc 0 T → TorusAreaPreserving (X N t))
    (hinv : ∀ N t, t ∈ Icc 0 T →
      ∀ᵐ x ∂μT, torusWrap (Y N t (torusWrap (X N t x))) = x)
    (hinit : ∀ N x, x ∈ torusBox → X N 0 x = x)
    (hflow : ∀ N x, x ∈ torusBox → ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => X N s x) (v N t (X N t x)) t)
    (hrep : ∀ N t, t ∈ Icc 0 T →
      finiteParticleVelocity (A₀ := A₀) (b := b) hR hρ hqpos hqE base Y hY N t =ᵐ[μT] v N t)
    (ha : 0 < a) (hbtime : btime < T) (times : ℕ → ℝ)
    (htimes : ∀ N, times N ∈ Icc a btime)
    (Ψ : R2 → ℂ) (hΨ : ContDiff ℝ ∞ Ψ) (hΨper : IsTorusPeriodic Ψ) (hδ : 0 < δ)
    (hmoment : ∀ N, δ ≤ ‖∫ x in torusBox,
      ((particleCurlL2
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hqpos hqE base N)
          (Y N) (hY N) (times N) -
        centeredPlaneToTorusL2 hqE (circularDatumLp (A₀ := A₀) (b := b) hR hρ hqpos)) x : ℂ) * Ψ x‖) :
    ∃ u₀ : L2T, (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧
      MemW1p (ENNReal.ofReal p) u₀ ∧ IsStationary u₀ ∧
        ∃ u : ℝ → L2T, IsWeakEulerSolution T u₀ u ∧ CurlBounded T (ENNReal.ofReal p) u ∧
          ∃ tstar ∈ Ioo 0 T, u tstar ≠ u₀ := by
  let datum := velocityDatumL2 (A₀ := A₀) (b := b) hR hρ
  let f (N : ℕ) := finiteBaseTorusLp (A₀ := A₀) (b := b) hR hρ hqpos base N
  let g (N : ℕ) := finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hqpos hqE base N
  let U := finiteParticleVelocity (A₀ := A₀) (b := b) hR hρ hqpos hqE base Y hY
  let z := centeredPlaneToTorusL2 hqE (circularDatumLp (A₀ := A₀) (b := b) hR hρ hqpos)
  have hprop := physical_datum_properties hA hb hR hR1 hρ hρ1 hq hpq hsmall
  have hmeang (N : ℕ) : (∫ x in torusBox, g N x) = 0 :=
    (integral_congr_ae (scalarLpLowerToTwo_ae hqE (f N))).trans (hcirculation N)
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hUinitial (N : ℕ) : U N 0 = biotSavartL2 (g N) := by
    change biotSavartL2 (particleCurlL2 (g N) (Y N) (hY N) 0) = _
    rw [particleCurlL2_initial (g N) (hY N) (hinit N) (hinv N 0 hzero)]
  have hweak (N : ℕ) : IsWeakEulerSolution T (biotSavartL2 (g N)) (U N) := by
    rw [← hUinitial N]
    exact weakEuler_of_biotSavart_particle_flow hT.le (g N) (hmeang N) (hY N) (hYc N)
      (hXc N) (hvc N) (hvper N) (hXmp N) (hinv N) (hinit N) (hflow N) (hrep N)
  have hcurl (N : ℕ) : CurlBoundedBy T (ENNReal.ofReal q)
      (finiteBaseNormBound A₀ b R ρ q C) (U N) := by
    have hc := curlBoundedBy_particleVelocity hqE (f N) (hcirculation N) (Y N) (hY N) T
    intro t ht
    obtain ⟨w, hw, hc, hn⟩ := hc t ht
    exact ⟨w, hw, hc, hn.trans (norm_finiteBaseTorusLp_le hA hb hR hρ hqpos hC hsmall base hbase N)⟩
  have hcurlz : IsCurl datum z := by
    exact (isCurl_velocityDatumL2 hA hb hR hR1 hρ hρ1 hqpos hq hsmall).congr_ae
      (EventuallyEq.refl _ _) (centeredPlaneToTorusL2_ae hqE _).symm
  have hdep (N : ℕ) : 0 < complexCurlTestBound hΨ ∧
      δ / complexCurlTestBound hΨ ≤ ‖U N (times N) - datum‖ := by
    exact velocity_departure_of_complex_curl_test
      (isCurl_biotSavartL2 _ ((integral_particleCurlL2 (g N) (Y N) (hY N) (times N)).trans (hmeang N)))
      hcurlz hΨ hΨper hδ (hmoment N)
  have hpE : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  apply limit_solution_of_finite_solutions hT hpE ENNReal.ofReal_ne_top
  exact
    { datum := datum
      mean_zero := hprop.1
      divergence_free := hprop.2.1
      sobolev := hprop.2.2.1
      stationary := hprop.2.2.2.1
      q := ENNReal.ofReal q
      two_le_q := hqE
      p_le_q := ENNReal.ofReal_le_ofReal hpq
      initial := fun N => biotSavartL2 (g N)
      initial_limit := tendsto_biotSavartL2_finite_base hA hb hR hR1 hρ hρ1 hqpos hq hqE hsmall base hbase
      solutions := U
      weak_solutions := hweak
      curl_bound := finiteBaseNormBound A₀ b R ρ q C
      uniform_curl := hcurl
      a := a
      b := btime
      a_pos := ha
      b_lt := hbtime
      departure := δ / complexCurlTestBound hΨ
      departure_pos := div_pos hδ (hdep 0).1
      departure_time := times
      departure_time_mem := htimes
      uniform_departure := fun N => (hdep N).2 }

end Euler2D

end
