module

public import RequestProject.Euler.TorusTransport
public import RequestProject.Euler.FourierRegularization
public import RequestProject.Euler.CurlLimit

/-!
# Strong continuity of actual transported scalar `L²` classes

An arbitrary fundamental-domain representative is extended by `torusWrap`.
Smooth periodic Fourier polynomials approximate it in the actual `L²`
space. Area preservation retains the approximation error exactly, while
the lifted continuous trajectories give strong continuity for each
polynomial. Their uniform limit is the transported `L²` path.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace Euler2D

/-- Jointly continuous scalar representatives give an actually strongly
continuous scalar `L²` path. Compactness is needed only in space. -/
lemma continuous_scalarL2_of_continuous_rep
    {W : ℝ → Lp ℝ 2 μT} {f : ℝ → R2 → ℝ}
    (hf : Continuous (Function.uncurry f))
    (hae : ∀ t, (W t : R2 → ℝ) =ᵐ[μT] f t) : Continuous W := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := measureUnivNNReal μT ^ (2 : ENNReal).toReal⁻¹
  let η : ℝ := ε / (C + 1)
  have hC : 0 ≤ C := by positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hclose := uniform_close hf t hη
  have hsmall : C * η < ε := by
    dsimp only [η]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  filter_upwards [hclose] with s hs
  have hbound : ∀ᵐ x ∂μT, ‖(W s - W t) x‖ ≤ η := by
    filter_upwards [Lp.coeFn_sub (W s) (W t), hae s, hae t,
      ae_restrict_mem measurableSet_torusBox] with x hsub hxs hxt hx
    rw [hsub]
    change ‖W s x - W t x‖ ≤ η
    rw [hxs, hxt, Real.norm_eq_abs]
    exact hs x hx
  rw [dist_eq_norm]
  exact (Lp.norm_le_of_ae_bound hη.le hbound).trans_lt hsmall

/-- Canonical scalar `L²` classes for a continuous lifted scalar family. -/
def continuousScalarL2 (f : ℝ → R2 → ℝ)
    (hf : Continuous (Function.uncurry f)) (t : ℝ) : Lp ℝ 2 μT :=
  (continuous_memLp_torus
    (hf.comp (continuous_const.prodMk continuous_id)) 2).toLp (f t)

lemma continuousScalarL2_ae (f : ℝ → R2 → ℝ)
    (hf : Continuous (Function.uncurry f)) (t : ℝ) :
    (continuousScalarL2 f hf t : R2 → ℝ) =ᵐ[μT] f t :=
  (continuous_memLp_torus (hf.comp (continuous_const.prodMk continuous_id)) 2).coeFn_toLp

lemma continuous_continuousScalarL2 (f : ℝ → R2 → ℝ)
    (hf : Continuous (Function.uncurry f)) : Continuous (continuousScalarL2 f hf) :=
  continuous_scalarL2_of_continuous_rep hf (continuousScalarL2_ae f hf)

/-- The actual transported class, with the discontinuous wrapping map
used exactly where the fundamental-domain representative requires it. -/
def torusTransportL2 (w₀ : Lp ℝ 2 μT) (Y : R2 → R2)
    (hY : TorusAreaPreserving Y) : Lp ℝ 2 μT :=
  Lp.compMeasurePreserving (torusWrap ∘ Y) hY w₀

lemma torusTransportL2_ae (w₀ : Lp ℝ 2 μT) (Y : R2 → R2)
    (hY : TorusAreaPreserving Y) :
    (torusTransportL2 w₀ Y hY : R2 → ℝ) =ᵐ[μT] fun x => w₀ (torusWrap (Y x)) :=
  Lp.coeFn_compMeasurePreserving w₀ hY

lemma torusTransportL2_dist (w₀ z₀ : Lp ℝ 2 μT) (Y : R2 → R2)
    (hY : TorusAreaPreserving Y) :
    dist (torusTransportL2 w₀ Y hY) (torusTransportL2 z₀ Y hY) = dist w₀ z₀ :=
  (Lp.isometry_compMeasurePreserving hY).dist_eq w₀ z₀

/-- For a genuinely smooth periodic scalar, transport by the wrapped map
equals the canonical class of composition with the continuous lift. -/
lemma continuousScalarL2_eq_torusTransportL2
    {p : R2 → ℝ} (hp : IsScalarTest p) {Y : ℝ → R2 → R2}
    (hY : Continuous (Function.uncurry Y)) (t : ℝ)
    (hMP : TorusAreaPreserving (Y t)) :
    continuousScalarL2 (fun s x => p (Y s x)) (hp.1.continuous.comp hY) t =
      torusTransportL2 ((continuous_memLp_torus hp.1.continuous 2).toLp p) (Y t) hMP := by
  apply Lp.ext
  have hpull := hMP.quasiMeasurePreserving.ae_eq_comp
    (continuous_memLp_torus hp.1.continuous 2).coeFn_toLp
  filter_upwards [continuousScalarL2_ae (fun s x => p (Y s x))
    (hp.1.continuous.comp hY) t,
    torusTransportL2_ae ((continuous_memLp_torus hp.1.continuous 2).toLp p) (Y t) hMP,
    hpull] with x hx hy hz
  rw [hx, hy]
  change p (Y t x) = ((continuous_memLp_torus hp.1.continuous 2).toLp p)
    (torusWrap (Y t x))
  simp only [Function.comp_apply] at hz
  rw [hz]
  exact (hp.2.eq_torusWrap (Y t x)).symm

/-- Arbitrary scalar `L²` transport is strongly continuous on every set
where the wrapped lifted maps actually preserve area. No periodicity is
assumed of the arbitrary initial `Lp` representative. -/
theorem continuousOn_torusTransport {s : Set ℝ} (w₀ : Lp ℝ 2 μT)
    {Y : ℝ → R2 → R2} {W : ℝ → Lp ℝ 2 μT}
    (hY : Continuous (Function.uncurry Y))
    (hMP : ∀ t ∈ s, TorusAreaPreserving (Y t))
    (hae : ∀ t ∈ s, (W t : R2 → ℝ) =ᵐ[μT] fun x => w₀ (torusWrap (Y t x))) :
    ContinuousOn W s := by
  let p (N : ℕ) : R2 → ℝ := boxScalarFourierPolynomial N (boxVorticity w₀ (Lp.memLp w₀))
  have hp (N : ℕ) : IsScalarTest (p N) := isScalarTest_boxScalarFourierPolynomial N _
  let P (N : ℕ) : Lp ℝ 2 μT := (continuous_memLp_torus (hp N).1.continuous 2).toLp (p N)
  have hP : Tendsto P atTop (𝓝 w₀) := by
    have hself : (Lp.memLp w₀).toLp (w₀ : R2 → ℝ) = w₀ := by
      apply Lp.ext
      exact (Lp.memLp w₀).coeFn_toLp
    have hrep (N : ℕ) : P N = boxRealPart
        (boxScalarFourierTrunc N (boxVorticity w₀ (Lp.memLp w₀))) := by
      apply Lp.ext
      exact (continuous_memLp_torus (hp N).1.continuous 2).coeFn_toLp.trans
        ((coeFn_boxRealPart _).trans (coeFn_boxScalarFourierTrunc_re N _)).symm
    change Tendsto (fun N => P N) atTop (𝓝 w₀)
    simp_rw [hrep]
    simpa only [hself] using tendsto_boxRealPart_scalarTrunc w₀ (Lp.memLp w₀)
  let Q (N : ℕ) : ℝ → Lp ℝ 2 μT :=
    continuousScalarL2 (fun t x => p N (Y t x)) ((hp N).1.continuous.comp hY)
  have hQ (N : ℕ) : Continuous (Q N) :=
    continuous_continuousScalarL2 (fun t x => p N (Y t x)) ((hp N).1.continuous.comp hY)
  have hW (t : ℝ) (ht : t ∈ s) : W t = torusTransportL2 w₀ (Y t) (hMP t ht) := by
    apply Lp.ext
    exact (hae t ht).trans (torusTransportL2_ae w₀ (Y t) (hMP t ht)).symm
  have herror (N : ℕ) (t : ℝ) (ht : t ∈ s) : dist (Q N t) (W t) = dist (P N) w₀ := by
    rw [hW t ht]
    change dist (continuousScalarL2 (fun r x => p N (Y r x))
      ((hp N).1.continuous.comp hY) t) _ = _
    rw [continuousScalarL2_eq_torusTransportL2 (hp N) hY t (hMP t ht)]
    exact torusTransportL2_dist _ _ _ _
  have hunif : TendstoUniformlyOn Q W atTop s := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hnear : ∀ᶠ N in atTop, dist (P N) w₀ < ε :=
      (Metric.tendsto_nhds.mp hP) ε hε
    filter_upwards [hnear] with N hN t ht
    rw [dist_comm, herror N t ht]
    exact hN
  exact hunif.continuousOn
    ((Eventually.of_forall fun N => (hQ N).continuousOn : ∀ᶠ N in atTop, ContinuousOn (Q N) s).frequently)

theorem continuous_torusTransportL2 (w₀ : Lp ℝ 2 μT) {Y : ℝ → R2 → R2}
    (hY : Continuous (Function.uncurry Y)) (hMP : ∀ t, TorusAreaPreserving (Y t)) :
    Continuous (fun t => torusTransportL2 w₀ (Y t) (hMP t)) := by
  apply continuousOn_univ.mp
  exact continuousOn_torusTransport w₀ hY (fun t _ => hMP t)
    (fun t _ => torusTransportL2_ae w₀ (Y t) (hMP t))

/-- A global representative path when area preservation is available only
on the requested time set. Its values outside that set are chosen as zero. -/
def torusTransportL2On (w₀ : Lp ℝ 2 μT) (Y : ℝ → R2 → R2)
    (s : Set ℝ) (hMP : ∀ t ∈ s, TorusAreaPreserving (Y t)) (t : ℝ) : Lp ℝ 2 μT := by
  classical
  exact if ht : t ∈ s then torusTransportL2 w₀ (Y t) (hMP t ht) else 0

lemma torusTransportL2On_ae (w₀ : Lp ℝ 2 μT) (Y : ℝ → R2 → R2)
    (s : Set ℝ) (hMP : ∀ t ∈ s, TorusAreaPreserving (Y t)) {t : ℝ} (ht : t ∈ s) :
    (torusTransportL2On w₀ Y s hMP t : R2 → ℝ) =ᵐ[μT] fun x => w₀ (torusWrap (Y t x)) := by
  simp only [torusTransportL2On, dif_pos ht]
  exact torusTransportL2_ae _ _ _

theorem continuousOn_torusTransportL2On (w₀ : Lp ℝ 2 μT) {Y : ℝ → R2 → R2}
    (hY : Continuous (Function.uncurry Y)) (s : Set ℝ)
    (hMP : ∀ t ∈ s, TorusAreaPreserving (Y t)) :
    ContinuousOn (torusTransportL2On w₀ Y s hMP) s :=
  continuousOn_torusTransport w₀ hY hMP (fun _ ht => torusTransportL2On_ae _ _ _ _ ht)

end Euler2D

end
