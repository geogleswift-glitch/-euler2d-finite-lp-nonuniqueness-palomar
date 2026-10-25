module

public import RequestProject.Euler.CircularActualDepartingEulerFamily
public import RequestProject.Euler.LimitAssemblyZeroEndpoint

/-! Completion of the original limit proposition using the actual
departing Euler family, the original stationary datum, genuine uniform
curl bounds on those SAME systems, and the proved compactness theorem. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 10000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem circular_actual_limit_solution {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 < p) :
    ∃ u₀ : L2T, (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧ MemW1p (ENNReal.ofReal p) u₀ ∧
      IsStationary u₀ ∧
      ∃ u : ℝ → L2T, IsWeakEulerSolution T u₀ u ∧ CurlBounded T (ENNReal.ofReal p) u ∧
        ∃ tstar ∈ Ioo 0 T, u tstar ≠ u₀ := by
  classical
  let q := max p 2
  have hq2 : 2 ≤ q := le_max_right _ _
  have hpq : p ≤ q := le_max_left _ _
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hq2
  have hqE : (2 : ENNReal) ≤ ENNReal.ofReal q := by
    calc
      (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq2
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨(by norm_num : (1 : ENNReal) ≤ 2).trans hqE⟩
  obtain ⟨P, b, hb, hbquarter, hfamily⟩ :=
    exists_circular_actual_departing_Euler_family hγ hγ1 hq hqE hq2 hT
  obtain ⟨n, _, hs, cA, hcA, heventual⟩ := hfamily 0
  let s := -(n : ℝ) * (period + period)
  obtain ⟨ξ, hξ, hdata⟩ := ((eventually_ge_atTop (0 : ℝ)).and heventual).exists
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  have hR : 0 < R := pow_pos hρ 10
  let A₀ := cA * (1 + ξ)
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hbR : 0 < (b : ℝ) := hb
  dsimp only [CircularMaterialTransferProfile.HasActualRootVelocityDepartureFamilyAt] at hdata
  obtain ⟨hρhalf, hsmall, ε, hε, hsolutions⟩ := hdata
  have hρone : ρ ≤ 1 := hρhalf.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρone (by decide : (1 : ℕ) ≤ 10)
  have hRmax : R ≤ 1 / 2 := hRρ.trans hρhalf
  have hR1 : R ≤ 1 := hRmax.trans (by norm_num)
  let f (N : ℕ) := finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
    (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N
  choose S hFour hWeak hArea τ hτ hdeparture using fun N : ℕ => hsolutions (N + 1) (Nat.succ_pos N)
  let initial : ℕ → L2T := fun N => biotSavartL2 (f (N + 1))
  let U : ℕ → ℝ → L2T := fun N => particleVelocity (f (N + 1)) (S N).backward (S N).backward_area
  let datum := velocityDatumL2 (A₀ := A₀) (b := (b : ℝ)) hR hρ
  have hU (N : ℕ) : IsWeakEulerSolution T (initial N) (U N) := hWeak N
  have hbase (N : ℕ) : ‖P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ N‖ ≤
      (eLpNorm (circularPhasePatchPlanarVorticity (P.ancient s)) (ENNReal.ofReal q) volume).toReal *
        (ampScale A₀ b N * radScale R ρ N ^ (2 / q)) :=
    (P.norm_finiteBaseLp hs hA.le hbR hR hρ hq N).le
  have hinitAll := tendsto_biotSavartL2_finite_base hA.le hbR hR hR1 hρ hρone hq hq2 hqE hsmall
    (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) hbase
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hinit : Tendsto initial atTop (𝓝 datum) := hinitAll.comp hshift
  let C := finiteBaseNormBound A₀ b R ρ q
    (eLpNorm (circularPhasePatchPlanarVorticity (P.ancient s)) (ENNReal.ofReal q) volume).toReal
  have hcurl (N : ℕ) : CurlBoundedBy T (ENNReal.ofReal q) C (U N) := by
    have hc := curlBoundedBy_particleVelocity hqE
      (finiteBaseTorusLp (A₀ := A₀) (b := (b : ℝ)) hR hρ hq
        (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (q := q) hs hR hρ) (N + 1))
      (P.integral_finiteBaseTorusLp_zero hs hR hRmax hρ hρone hq (N + 1))
      (S N).backward (S N).backward_area T
    intro t ht
    obtain ⟨w, hw, hcw, hn⟩ := hc t ht
    refine ⟨w, hw, hcw, hn.trans ?_⟩
    exact norm_finiteBaseTorusLp_le hA.le hbR hR hρ hq ENNReal.toReal_nonneg hsmall _ hbase (N + 1)
  have hτclosed (N : ℕ) : τ N ∈ Icc (0 : ℝ) (T / 2) := ⟨(hτ N).1.le, (hτ N).2.le⟩
  obtain ⟨u, hu, hcu, tstar, htstar, hgap, hne⟩ :=
    weak_limit_with_departure_of_uniform_curl_zero_endpoint hT (by linarith : T / 2 < T) hε
      hU hinit hqE hcurl τ hτclosed hdeparture
  have hprop := physical_datum_properties hA.le hbR hR hR1 hρ hρone hq2 hpq hsmall
  have hcurlp : CurlBounded T (ENNReal.ofReal p) u :=
    curlBounded_mono_exponent (ENNReal.one_le_ofReal.mpr hp.le) ENNReal.ofReal_ne_top
      (ENNReal.ofReal_le_ofReal hpq) ⟨C, hcu⟩
  exact ⟨datum, hprop.1, hprop.2.1, hprop.2.2.1, hprop.2.2.2.1,
    u, hu, hcurlp, tstar, htstar, hne⟩

end Euler2D

end
