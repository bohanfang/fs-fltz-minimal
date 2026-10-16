import FsFltz.Geometry.TailoringCotangentEndpointRetainedPotential
import FsFltz.Geometry.TailoringCotangentEndpointCore
import FsFltz.Geometry.PotentialAmbientMarking
import FsFltz.Geometry.PotentialPathRoundedMarking

/-!
# The native marking and homogeneous boundary of the same retained potential

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 626–643,
`prop:endpoint`, lines 1922–1959, and `sec:assembly`, lines 2091–2191.
The strict marking is constructed from the actual embedded full sublevel,
its native complete flow and negative absorption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff Manifold

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance retainedEndpointNativeCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance retainedEndpointNativeSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- Every sufficiently high full level is literally homogeneous, with the
same gradient and a strict native outward inequality on the entire end. -/
theorem RetainedLegendrePotential.exists_endpoint_level_threshold
    {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
    (D : RetainedLegendrePotential φEnd φ)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A ≥ A₀,
      {y : LGSpace n | φ y.1 = A} = {y : LGSpace n | φEnd y.1 = A} ∧
      (∀ u, φ u = A → coordinateGradient φ u = coordinateGradient φEnd u) ∧
      ∀ y : LGSpace n, A ≤ φ y.1 →
        0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
          ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) D.radius).exists_bound_of_continuousOn
    (D.smooth.continuous.comp e.continuous).continuousOn
  obtain ⟨BEnd, hBEnd⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) D.radius).exists_bound_of_continuousOn
    (D.end_c1.continuous.comp e.continuous).continuousOn
  obtain ⟨Aout, hAout, hout⟩ := ToricInput.coefficientPath_potential_ambient_outward
    D.smooth hstrong.smooth hstrong.homogeneous D.lower_pos D.upper_pos
    D.hessian_lower D.hessian_upper D.radius_pos D.end_eq I
  let A₀ := max Aout (max B BEnd + 1)
  have hA₀ : 0 < A₀ := hAout.trans_le (le_max_left _ _)
  have hBlt : B < A₀ := by dsimp [A₀]; linarith [le_max_left B BEnd, le_max_right Aout (max B BEnd + 1)]
  have hBEndlt : BEnd < A₀ := by dsimp [A₀]; linarith [le_max_right B BEnd, le_max_right Aout (max B BEnd + 1)]
  have houtside (u : RealSpace n) (hu : A₀ ≤ φ u) : D.radius < ‖e.symm u‖ := by
    by_contra hn
    have hm : e.symm u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) D.radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_not_gt hn
    have hb := (Real.le_norm_self _).trans (hB _ hm)
    change φ (e (e.symm u)) ≤ B at hb
    rw [e.apply_symm_apply] at hb
    linarith
  have houtsideEnd (u : RealSpace n) (hu : A₀ ≤ φEnd u) : D.radius < ‖e.symm u‖ := by
    by_contra hn
    have hm : e.symm u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) D.radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_not_gt hn
    have hb := (Real.le_norm_self _).trans (hBEnd _ hm)
    change φEnd (e (e.symm u)) ≤ BEnd at hb
    rw [e.apply_symm_apply] at hb
    linarith
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA
  refine ⟨?_, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      change φEnd y.1 = A
      rw [← D.end_eq y.1 (houtside y.1 (hy.symm ▸ hA)).le]
      exact hy
    · intro hy
      change φ y.1 = A
      rw [D.end_eq y.1 (houtsideEnd y.1 (hy.symm ▸ hA)).le]
      exact hy
  · intro u hu
    have hn := houtside u (hu.symm ▸ hA)
    have he : φ =ᶠ[𝓝 u] φEnd := by
      filter_upwards [continuous_const.continuousAt.eventually_lt
        (continuous_norm.comp e.symm.continuous).continuousAt hn] with v hv
      exact D.end_eq v hv.le
    ext j
    exact congrArg (fun L : RealSpace n →L[ℝ] ℝ => L (Pi.single j 1)) he.fderiv_eq
  · intro y hy
    have h := hout 0 (by simp) 0 (by simp) y ((le_max_left _ _).trans (hA.trans hy))
    simpa only [ToricInput.alongCoefficientPath_zero, SmoothManifold.rankTwoPrimitive,
      zero_smul, add_zero] using h

/-- Native completeness, strict end outwardness and the full sublevel image
construct the K=0 marking of every chosen retained completion. -/
theorem RetainedLegendrePotential.exists_native_zero_marking
    {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
    (D : RetainedLegendrePotential φEnd φ)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    (A : ℝ)
    (hout : ∀ y : LGSpace n, A ≤ φ y.1 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y))
    (P : WitnessedPair n) (hP : P.ambientDomain.domain.carrier.Nonempty)
    (j : P.ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (himage : j.map '' P.ambientDomain.domain.carrier = {y | φ y.1 ≤ A})
    (hprimitive : ∀ x ∈ P.ambientDomain.domain.carrier,
      P.ambientDomain.liouville.primitive x =
        P.ambientDomain.domain.extension.pullback (lgManifold n) j.map (lambdaPotentialForm φ) x) :
    ∃ q : P.ambientManifold.SmoothEquiv (lgManifold n),
      P.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
        P.ambientCompletion.ambient.primitive ∧
      ∀ x ∈ P.ambientDomain.domain.carrier,
        q (P.ambientCompletion.inclusion.map x) = j.map x := by
  let Pzero : CompletePrimitive (lgManifold n) (lambdaPotentialForm φ) := by
    have h := potential_W_ambientCompletePrimitive D.smooth D.end_c1 hstrong.smooth
      hstrong.homogeneous D.lower_pos D.upper_pos D.hessian_lower D.hessian_upper
      D.radius_pos D.end_eq I (K := 0) (by simp)
    simpa only [SmoothManifold.rankTwoPrimitive, zero_smul, add_zero] using h
  let X := Pzero.toCompleteLiouvilleManifold
  have hX : X.primitive = lambdaPotentialForm φ := rfl
  let ρ : LGSpace n → ℝ := fun y => φ y.1 - A
  have hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_potentialValue D.smooth).sub contMDiff_const
  have hder (y : LGSpace n) (v : (lgManifold n).Tangent y) :
      (lgManifold n).scalarDerivative ρ y v =
        (lgManifold n).scalarDerivative (fun z => φ z.1) y v := by
    unfold SmoothManifold.scalarDerivative
    change mfderiv _ _ ((fun z : LGSpace n => φ z.1) - fun _ => A) y v = _
    erw [mfderiv_sub ((contMDiff_potentialValue D.smooth).mdifferentiable (by simp) y)
      mdifferentiableAt_const, mfderiv_const, sub_zero]
    rfl
  have hc (B : ℝ) : IsCompact {y : LGSpace n | φ y.1 ≤ B} :=
    isCompact_potential_sublevel D.smooth D.end_c1 hstrong.smooth hstrong.homogeneous
      D.lower_pos D.hessian_lower D.radius_pos D.end_eq B
  have ho : ∀ y : X.manifold.Point, ρ y = 0 →
      0 < X.manifold.scalarDerivative ρ y (X.manifold.liouvilleVector X.primitive y) := by
    intro y hy
    change 0 < (lgManifold n).scalarDerivative ρ y
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y)
    rw [hder]
    exact hout y (sub_eq_zero.mp hy).ge
  have ha : ∀ y : X.manifold.Point, ∃ T : ℝ, 0 ≤ T ∧
      ρ (X.completeFlow.flow (-T) y) ≤ 0 := by
    intro y
    obtain ⟨T, hT, hle⟩ := X.completeFlow.exists_nonneg_time_scalar_le
      (fun z : LGSpace n => φ z.1) (contMDiff_potentialValue D.smooth)
      X.smooth_field hc A
      (fun z hz => by
        rw [X.field_eq_liouvilleVector, hX]
        exact hout z hz) y
    exact ⟨T, hT, sub_nonpos.mpr hle⟩
  obtain ⟨m⟩ := P.ambientCompletion.exists_inclusionMarking_of_embedded_absorbing_sublevel
    hP X ρ hρ (by
      change IsCompact {y : LGSpace n | ρ y ≤ 0}
      simpa only [ρ, sub_nonpos] using hc A) ho ha j
    (by
      change j.map '' P.ambientDomain.domain.carrier = {y : LGSpace n | ρ y ≤ 0}
      refine himage.trans ?_
      ext y
      change φ y.1 ≤ A ↔ φ y.1 - A ≤ 0
      exact sub_nonpos.symm)
    (by
      change ∀ x ∈ P.ambientDomain.domain.carrier,
        P.ambientDomain.liouville.primitive x =
          P.ambientDomain.domain.extension.pullback (lgManifold n) j.map (lambdaPotentialForm φ) x
      exact hprimitive)
  refine ⟨m.equiv, ?_, ?_⟩
  · exact m.primitive
  · intro x hx
    exact m.inclusion ⟨x, hx⟩

/-- The same selected analytic potential and the actual native full sublevel
produce the strict cotangent step, exact witness, and entire FLTZ link. -/
theorem RetainedLegendrePotential.exists_literal_cotangentEndpoint
    {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
    (D : RetainedLegendrePotential φEnd φ)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    {A : ℝ} (hA : 0 < A)
    (hlevelEq : {y : LGSpace n | φ y.1 = A} = {y : LGSpace n | φEnd y.1 = A})
    (hgradient : ∀ u, φ u = A → coordinateGradient φ u = coordinateGradient φEnd u)
    (hout : ∀ y : LGSpace n, A ≤ φ y.1 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y))
    (P : WitnessedPair n) (hP : P.ambientDomain.domain.carrier.Nonempty)
    (j : P.ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (himage : j.map '' P.ambientDomain.domain.carrier = {y | φ y.1 ≤ A})
    (hprimitive : ∀ x ∈ P.ambientDomain.domain.carrier,
      P.ambientDomain.liouville.primitive x =
        P.ambientDomain.domain.extension.pullback (lgManifold n) j.map (lambdaPotentialForm φ) x)
    (hboundary : range (j.comp P.ambientDomain.domain.boundaryInclusion).map =
      {y | φ y.1 = A})
    (hcore : (j.comp P.ambientDomain.domain.boundaryInclusion).map '' P.embeddedCore =
      tailoringLegendreConic I φEnd ∩ range (j.comp P.ambientDomain.domain.boundaryInclusion).map) :
    ∃ q : P.ambientManifold.SmoothEquiv (lgManifold n),
      P.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
        P.ambientCompletion.ambient.primitive ∧
      (∀ x ∈ P.ambientDomain.domain.carrier, q (P.ambientCompletion.inclusion.map x) = j.map x) ∧
      ∃ E : CotangentPairData n, ∃ J : CompletionIdentification P E.pair,
        (∀ y, E.marking (J.ambientEquiv y) = ((q y).2, coordinateGradient φ (q y).1)) ∧
        E.pair.ribbonDomain = P.ribbonDomain ∧
        HEq E.pair.ribbonCompletion P.ribbonCompletion ∧
        HEq J.ribbonEquiv.map (id : P.ribbonDomain.domain.extension.Point →
          P.ribbonDomain.domain.extension.Point) ∧ J.scale = 1 ∧
        (∀ x, E.boundaryCoordinates (J.boundaryEquiv x) =
          tailoringRadialProjection φEnd ((j.comp P.ambientDomain.domain.boundaryInclusion).map x)) ∧
        (∀ x, E.pair.witness (J.boundaryEquiv x) =
          Real.sqrt (realSquaredNorm (coordinateGradient φEnd
            ((j.comp P.ambientDomain.domain.boundaryInclusion).map x).1)) * P.witness x) ∧
        E.embeddedCore = fltzLink I := by
  obtain ⟨q, hq, hcompact⟩ := D.exists_native_zero_marking hstrong A hout P hP j himage hprimitive
  let i := (j.comp P.ambientDomain.domain.boundaryInclusion).map
  have hb : ∀ x, q (P.ambientCompletion.inclusion.map
      (P.ambientDomain.domain.boundaryInclusion.map x)) = i x := by
    intro x
    exact hcompact _ (P.ambientDomain.domain.boundaryInclusion_mem_carrier x)
  have hg : ∀ x, coordinateGradient φ (i x).1 = coordinateGradient φEnd (i x).1 := by
    intro x
    apply hgradient
    have hm : i x ∈ range i := mem_range_self x
    rw [hboundary] at hm
    exact hm
  have hl : range i = {y : LGSpace n | φEnd y.1 = A} := hboundary.trans hlevelEq
  refine ⟨q, hq, hcompact, ?_⟩
  exact exists_literal_cotangentEndpoint_of_samePotential hstrong D.endGradient
    D.endGradient_eq D.endGradient_zero (hstrong.positive D.end_c1) hA D.smooth
    D.gradient D.gradient_eq D.inverse_smooth P i q hq hb hg hcore hl

end FsFltz
