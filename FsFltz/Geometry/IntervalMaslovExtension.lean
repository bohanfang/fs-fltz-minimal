import FsFltz.Geometry.IntervalCanonicalBundle
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Recovering a Maslov family from local scalar extensions

Source: `geoemtric-part-fsf.tex`, smooth extension convention, lines 119–122;
`def:maslov`, lines 212–232; `g:chain`, lines 407–413;
`sec:lean`, lines 794–814.

The input section lives only over the prescribed interval. Its coframe
coefficients admit genuine local C∞ extensions across the interval endpoints.
Reconstruction in open coframes and a partition of unity produce one ordinary
tensor family with every interval value fixed. The supplied almost complex
family needs no complex or symplectically compatible extension off the interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct BigOperators
open Set Filter Bundle

namespace FsFltz.Geometry

/-- Local coframes depend only on the extending complex field, independently
of a Maslov section or its nonvanishing. -/
theorem exists_intervalCanonicalChart_of_smooth {n : ℕ}
    {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
    (hJ : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun z => almostComplexInChart M a (J z.1) z.2))
    (hJsq : ∀ t ∈ parameterInterval, ∀ x v, J t x (J t x v) = -v)
    (p : Parameter × M.Point) :
    ∃ c : IntervalCanonicalChart M J, intervalParameterInclusion M p ∈ c.domain := by
  let a := p.2
  let e := chartAt (Model (2 * n)) a
  have hp : (p.1.val, e a) ∈ parameterInterval ×ˢ e.target :=
    ⟨p.1.property, e.map_source (mem_chart_source _ a)⟩
  obtain ⟨U, hUo, hslab, hs⟩ := hJ a
  let W := U ∩ (univ ×ˢ e.target)
  have hWo : IsOpen W := hUo.inter (isOpen_univ.prod e.open_target)
  obtain ⟨C₀, V, hVW, hVo, hpV, hC, hinv, hCJ⟩ :=
    exists_smooth_local_prescribedComplexCoframe hWo
      (show (p.1.val, e a) ∈ W from ⟨hslab hp, mem_univ _, hp.2⟩) hp
      (hs.mono inter_subset_left)
      (fun z hz => almostComplexInChart_sq M a (J z.1)
        (hJsq z.1 hz.2.1) z.2 hz.2.2)
  let C := fun q : ℝ × Model (2 * n) =>
    projectedComplexCoframe C₀ (almostComplexInChart M a (J q.1) q.2)
  refine ⟨⟨intrinsicParameterChartDomain M a V,
    isOpen_intrinsicParameterChartDomain M a hVo, localVerticalCoframe M a C,
    isSmoothVerticalCoframeOn_local M a hC, ?_, ?_⟩, ?_⟩
  · intro q hq
    exact (hinv _ hq.2).comp (chartTangentMap_isInvertible M a q.2 hq.1.2)
  · intro q hq ht v
    exact localCanonicalCoframe_intertwines M a (J q.1) (fun y => C (q.1, y))
      q.2 hq.1.2 (hCJ _ ⟨hq.2, ⟨ht, e.map_source hq.1.2⟩⟩) v
  · exact ⟨⟨mem_univ _, mem_chart_source _ a⟩, hpV⟩

/-- The native interval tensor-square bundle is constructed from the
extending complex field alone. No nonvanishing section or Maslov family
is an input to its coframe atlas or topology. -/
def intervalCanonicalTensorSquareVectorPrebundleOfSmooth {n : ℕ}
    {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
    (hJ : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun z => almostComplexInChart M a (J z.1) z.2))
    (hJsq : ∀ t ∈ parameterInterval, ∀ x v, J t x (J t x v) = -v) :
    VectorPrebundle ℝ ℂ
      (fun p : Parameter × M.Point => CanonicalTensorSquare (J p.1.val p.2)) :=
  intervalCanonicalTensorSquareVectorPrebundleOfCharts
    (fun p => (exists_intervalCanonicalChart_of_smooth hJ hJsq p).choose)
    (fun p => (exists_intervalCanonicalChart_of_smooth hJ hJsq p).choose_spec)

instance intervalCanonicalTensorSquareVectorPrebundleOfSmooth_isContMDiff {n : ℕ}
    {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
    (hJ : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun z => almostComplexInChart M a (J z.1) z.2))
    (hJsq : ∀ t ∈ parameterInterval, ∀ x v, J t x (J t x v) = -v) :
    (intervalCanonicalTensorSquareVectorPrebundleOfSmooth hJ hJsq).IsContMDiff
      ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))) ∞ := by
  unfold intervalCanonicalTensorSquareVectorPrebundleOfSmooth
  infer_instance

namespace IsSmoothVerticalSquaredTensorOn

variable {n : ℕ} {M : SmoothManifold (2 * n)}

/-- Scalar multiplication preserves the smoothness of the actual vertical
tensor, including its tangent transition maps. -/
theorem smul {U : Set (ℝ × M.Point)} (hU : IsOpen U)
    {s : (ℝ × M.Point) → SquaredCanonicalTensor n}
    (hs : IsSmoothVerticalSquaredTensorOn M s U)
    {q : (ℝ × M.Point) → ℂ}
    (hq : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞ q U) :
    IsSmoothVerticalSquaredTensorOn M (fun p => q p • s p) U := by
  intro b
  let e := chartAt (Model (2 * n)) b
  let D := intrinsicParameterCoordinateDomain M b U
  have hD : IsOpen D := isOpen_intrinsicParameterCoordinateDomain M b hU
  have hscalar : ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) => q (p.1, e.symm p.2)) D := by
    intro p hp
    have he : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ e.symm p.2 :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
        (e.open_target.mem_nhds hp.1.2)
    have hmap : ContMDiffAt 𝓘(ℝ, ℝ × Model (2 * n))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞
        (fun p : ℝ × Model (2 * n) => (p.1, e.symm p.2)) p :=
      contDiff_fst.contMDiff.contMDiffAt.prodMk
        (he.comp p contDiff_snd.contMDiff.contMDiffAt)
    exact ((hq.contMDiffAt (hU.mem_nhds hp.2)).comp p hmap).contDiffAt.contDiffWithinAt
  apply (hscalar.smul (hs b)).congr
  intro p _
  ext v
  rfl

/-- A fixed-chart expression of a smooth tensor is a native smooth map on
the overlap with that chart's source. -/
theorem contMDiffAt_chartExpression {U : Set (ℝ × M.Point)} (hU : IsOpen U)
    {s : (ℝ × M.Point) → SquaredCanonicalTensor n}
    (hs : IsSmoothVerticalSquaredTensorOn M s U)
    (b : M.Point) {x : ℝ × M.Point} (hx : x ∈ U)
    (hxb : x.2 ∈ (chartAt (Model (2 * n)) b).source) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, SquaredCanonicalTensor n) ∞
      (fun z : ℝ × M.Point =>
        squaredTensorInChart M b (fun y => s (z.1, y))
          (chartAt (Model (2 * n)) b z.2)) x := by
  let e := chartAt (Model (2 * n)) b
  let C := fun p : ℝ × Model (2 * n) =>
    squaredTensorInChart M b (fun y => s (p.1, y)) p.2
  have hpx : (x.1, e x.2) ∈ intrinsicParameterCoordinateDomain M b U := by
    refine ⟨⟨mem_univ _, e.map_source hxb⟩, ?_⟩
    change (x.1, e.symm (e x.2)) ∈ U
    rwa [e.left_inv hxb]
  have hsC : ContMDiffAt 𝓘(ℝ, ℝ × Model (2 * n))
      𝓘(ℝ, SquaredCanonicalTensor n) ∞ C (x.1, e x.2) :=
    contMDiffAt_iff_contDiffAt.mpr ((hs b).contDiffAt
      ((isOpen_intrinsicParameterCoordinateDomain M b hU).mem_nhds hpx))
  have he : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ e x.2 :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
      (e.open_source.mem_nhds hxb)
  exact hsC.comp x (contMDiffAt_fst.prodMk_space (he.comp x contMDiffAt_snd))

end IsSmoothVerticalSquaredTensorOn

/-- A smooth scalar coordinate function defines a native smooth map on
the corresponding open parameter–spatial chart domain. -/
theorem contMDiffOn_localParameterCoordinates {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : SmoothManifold d) (a : M.Point)
    {V : Set (ℝ × Model d)} (hV : IsOpen V)
    {q : (ℝ × Model d) → F} (hq : ContDiffOn ℝ ∞ q V) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M.Point => q (p.1, chartAt (Model d) a p.2))
      (intrinsicParameterChartDomain M a V) := by
  intro p hp
  have hqM := contMDiffAt_iff_contDiffAt.mpr (hq.contDiffAt (hV.mem_nhds hp.2))
  have he : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
      (chartAt (Model d) a) p.2 :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := a)).contMDiffAt
      ((chartAt (Model d) a).open_source.mem_nhds hp.1.2)
  exact (hqM.comp p (contMDiffAt_fst.prodMk_space
    (he.comp p contMDiffAt_snd))).contMDiffWithinAt

/-- A smooth partition glues actual tensor fields. Smoothness is checked
after each spatial tangent transition, rather than in the discontinuous
pointwise tangent-coordinate presentation. -/
theorem smoothVerticalSquaredTensor_partition {n : ℕ} {M : SmoothManifold (2 * n)}
    {ι : Type*} {A : Set (ℝ × M.Point)}
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) (ℝ × M.Point) A)
    (U : ι → Set (ℝ × M.Point)) (hU : ∀ i, IsOpen (U i))
    (hρU : ρ.IsSubordinate U)
    (s : ι → (ℝ × M.Point) → SquaredCanonicalTensor n)
    (hs : ∀ i, IsSmoothVerticalSquaredTensorOn M (s i) (U i)) :
    IsSmoothVerticalSquaredTensorOn M (fun x => ∑ᶠ i, ρ i x • s i x) univ := by
  intro b p hp
  let e := chartAt (Model (2 * n)) b
  let x : ℝ × M.Point := (p.1, e.symm p.2)
  have hpx : p.2 ∈ e.target := hp.1.2
  have hxb : x.2 ∈ e.source := e.map_target hpx
  let g := fun i (z : ℝ × M.Point) =>
    squaredTensorInChart M b (fun y => s i (z.1, y)) (e z.2)
  have hg : ∀ i, x ∈ tsupport (ρ i) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, SquaredCanonicalTensor n) ∞ (g i) x := by
    intro i hi
    exact (hs i).contMDiffAt_chartExpression (hU i) b (hρU i hi) hxb
  have hsum := ρ.contMDiffAt_finsum hg
  have he : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ e.symm p.2 :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
      (e.open_target.mem_nhds hpx)
  have hmap : ContMDiffAt 𝓘(ℝ, ℝ × Model (2 * n))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × Model (2 * n) => (p.1, e.symm p.2)) p :=
    contDiff_fst.contMDiff.contMDiffAt.prodMk
      (he.comp p contDiff_snd.contMDiff.contMDiffAt)
  apply ((hsum.comp p hmap).contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(isOpen_univ.prod e.open_target).mem_nhds
    (show p ∈ univ ×ˢ e.target from ⟨mem_univ _, hpx⟩)] with q hq
  let z : ℝ × M.Point := (q.1, e.symm q.2)
  let L : SquaredCanonicalTensor n →L[ℝ] SquaredCanonicalTensor n :=
    ContinuousMultilinearMap.compContinuousLinearMapL
    (F := ℂ) (fun _ : Sum (Fin n) (Fin n) => M.inverseChartTangentMap b q.2)
  have hfin : (Function.support (fun i => ρ i z • s i z)).Finite :=
    (ρ.locallyFinite.point_finite z).subset (by
      intro i hi
      change ρ i z ≠ 0
      intro hz
      apply hi
      change ρ i z • s i z = 0
      rw [hz]
      exact zero_smul ℝ (s i z))
  have hcomm := L.toLinearMap.toAddMonoidHom.map_finsum hfin
  change L (∑ᶠ i, ρ i z • s i z) = ∑ᶠ i, L (ρ i z • s i z) at hcomm
  symm
  change (∑ᶠ i, ρ i z • g i z) = L (∑ᶠ i, ρ i z • s i z)
  rw [hcomm]
  apply finsum_congr
  intro i
  dsimp only [g, squaredTensorInChart, z, L, SmoothManifold.inverseChartTangentMap]
  rw [e.right_inv hq.2]
  ext v
  rfl

/-- Local ordinary tensor extensions on a closed set glue to a single
smooth actual tensor on the whole parameter–spatial ambient manifold.
Agreement is preserved because all active local sections have the same
prescribed value, and the partition sums to one on that set. -/
theorem exists_smoothVerticalSquaredTensorExtension_of_local {n : ℕ}
    {M : SmoothManifold (2 * n)} {A : Set (ℝ × M.Point)} (hA : IsClosed A)
    (s : (ℝ × M.Point) → SquaredCanonicalTensor n)
    (hloc : ∀ x ∈ A, ∃ U : Set (ℝ × M.Point), IsOpen U ∧ x ∈ U ∧
      ∃ q : (ℝ × M.Point) → SquaredCanonicalTensor n,
        IsSmoothVerticalSquaredTensorOn M q U ∧ EqOn q s (U ∩ A)) :
    ∃ q : (ℝ × M.Point) → SquaredCanonicalTensor n,
      IsSmoothVerticalSquaredTensorOn M q univ ∧ EqOn q s A := by
  classical
  let I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))
  let : LocallyCompactSpace M.Point := ChartedSpace.locallyCompactSpace (Model (2 * n)) M.Point
  choose U hU hxU q hq heq using fun x : A => hloc x x.property
  have hcover : A ⊆ ⋃ x : A, U x := fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (hxU ⟨x, hx⟩)
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hA U hU hcover
  refine ⟨fun x => ∑ᶠ i, ρ i x • q i x,
    smoothVerticalSquaredTensor_partition ρ U hU hρ q hq, ?_⟩
  intro x hx
  have hterms : ∀ i, ρ i x • q i x = ρ i x • s x := by
    intro i
    by_cases hi : ρ i x = 0
    · rw [hi]
      exact (zero_smul ℝ (q i x)).trans (zero_smul ℝ (s x)).symm
    · rw [heq i ⟨hρ i (subset_closure (Function.mem_support.mpr hi)), hx⟩]
  simp_rw [hterms]
  rw [← finsum_smul (fun i => ρ i x) (s x), ρ.sum_eq_one hx]
  exact one_smul ℝ (s x)

/-- The source's extension convention in native line coordinates. At each
interval point, one scalar C∞ function on a genuine open neighborhood
extends the section's coframe coefficient. This is stronger information
than bare boundary-manifold `ContMDiff ∞` and is explicit source data.

The input is an arbitrary interval-indexed tensor-square section; neither
an encoded tensor extension nor a pre-existing Maslov family is supplied. -/
def HasLocalSmoothIntervalTensorCoefficients {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (s : (p : Parameter × M.Point) → CanonicalTensorSquare (J p.1.val p.2)) : Prop :=
  ∀ p : Parameter × M.Point,
    ∃ c : IntervalCanonicalChart M J,
      ∃ U : Set (ℝ × M.Point), IsOpen U ∧ U ⊆ c.domain ∧
        intervalParameterInclusion M p ∈ U ∧
        ∃ q : (ℝ × M.Point) → ℂ,
          ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞ q U ∧
          ∀ z : Parameter × M.Point, intervalParameterInclusion M z ∈ U →
            q (intervalParameterInclusion M z) = c.tensorCoordinateLinearMap z (s z)

namespace MaslovFamily

set_option maxHeartbeats 800000 in
/-- The encoded extension convention produces genuine local scalar
extension witnesses for any interval section with its prescribed tensor
image. The chosen coframe atlas is independent of that section. -/
theorem localSmoothIntervalTensorCoefficients {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (f : MaslovFamily M eta)
    (s : (p : Parameter × M.Point) → CanonicalTensorSquare (f.J p.1.val p.2))
    (heq : ∀ p, f.tensor p.1.val p.2 =
      (canonicalSquareMap (f.J p.1.val p.2) (s p)).val) :
    HasLocalSmoothIntervalTensorCoefficients M f.J s := by
  intro p
  let b := p.2
  let e := chartAt (Model (2 * n)) b
  let c := f.intervalCanonicalChartAt p
  obtain ⟨S, hSo, hSsub, hsS⟩ := f.smoothSection b
  let D := intrinsicParameterCoordinateDomain M b c.domain
  let W := D ∩ S
  have hWo : IsOpen W := (isOpen_intrinsicParameterCoordinateDomain M b c.isOpen_domain).inter hSo
  let C : (ℝ × Model (2 * n)) → Model (2 * n) →L[ℝ] TangentCoordinates n := fun z =>
    (c.coframe (z.1, e.symm z.2)).comp (M.inverseChartTangentMap b z.2)
  let Q := fun z : ℝ × Model (2 * n) =>
    squaredCoframeCoefficient (C z) (squaredTensorInChart M b (f.tensor z.1) z.2)
  have hinv : ∀ z ∈ W, (C z).IsInvertible := by
    intro z hz
    exact (c.invertible_coframe _ hz.1.2).comp
      (inverseChartTangentMap_isInvertible M b z.2 hz.1.1.2)
  have hQ : ContDiffOn ℝ ∞ Q W :=
    contDiffOn_squaredCoframeCoefficient
      ((c.smooth_coframe b).mono inter_subset_left) hinv (hsS.mono inter_subset_right)
  let U := intrinsicParameterChartDomain M b W
  have hUc : U ⊆ c.domain := by
    intro z hz
    have hc := hz.2.1.2
    change (z.1, e.symm (e z.2)) ∈ c.domain at hc
    rwa [e.left_inv hz.1.2] at hc
  have hpU : intervalParameterInclusion M p ∈ U := by
    refine ⟨⟨mem_univ _, mem_chart_source _ b⟩, ?_⟩
    refine ⟨⟨⟨mem_univ _, e.map_source (mem_chart_source _ b)⟩, ?_⟩,
      hSsub ⟨p.1.property, e.map_source (mem_chart_source _ b)⟩⟩
    change (p.1.val, e.symm (e b)) ∈ c.domain
    rw [e.left_inv (mem_chart_source _ b)]
    exact f.mem_intervalCanonicalChartAt_domain p
  refine ⟨c, U, isOpen_intrinsicParameterChartDomain M b hWo, hUc, hpU,
    fun z => Q (z.1, e z.2), contMDiffOn_localParameterCoordinates M b hWo hQ, ?_⟩
  intro z hz
  have hzb : z.2 ∈ e.source := hz.1.2
  let L : Model (2 * n) →L[ℝ] Model (2 * n) := M.inverseChartTangentMap b (e z.2)
  have hL : L.IsInvertible := inverseChartTangentMap_isInvertible M b (e z.2) (e.map_source hzb)
  change squaredCoframeCoefficient ((c.coframe (z.1.val, e.symm (e z.2))).comp L)
    ((f.tensor z.1.val (e.symm (e z.2))).compContinuousLinearMap (fun _ => L)) = _
  rw [e.left_inv hzb]
  calc
    _ = squaredCoframeCoefficient (c.coframe (z.1.val, z.2)) (f.tensor z.1.val z.2) :=
      squaredCoframeCoefficient_comp _ L hL _
    _ = c.tensorCoordinateLinearMap z (s z) := by
      rw [heq z]
      exact c.coefficient_squareMap z (s z)

end MaslovFamily

/-- Scalar extension witnesses reconstruct one smooth actual tensor
family independently of regularity of the supplied complex field away
from the interval. Every prescribed interval tensor is preserved. -/
theorem exists_smoothIntervalTensorExtension_of_localScalarExtensions {n : ℕ}
    {M : SmoothManifold (2 * n)}
    {J : ℝ → AlmostComplexField M}
    (s : (p : Parameter × M.Point) → CanonicalTensorSquare (J p.1.val p.2))
    (hs : HasLocalSmoothIntervalTensorCoefficients M J s) :
    ∃ q : (ℝ × M.Point) → SquaredCanonicalTensor n,
      IsSmoothVerticalSquaredTensorOn M q univ ∧
      ∀ p : Parameter × M.Point,
        q (p.1.val, p.2) = (canonicalSquareMap (J p.1.val p.2) (s p)).val := by
  classical
  let A : Set (ℝ × M.Point) := {x | x.1 ∈ parameterInterval}
  let T : (ℝ × M.Point) → SquaredCanonicalTensor n := fun x =>
    if ht : x.1 ∈ parameterInterval then
      (canonicalSquareMap (J x.1 x.2) (s (⟨x.1, ht⟩, x.2))).val else 0
  have hA : IsClosed A := isClosed_Icc.preimage continuous_fst
  have hlocal : ∀ x ∈ A, ∃ U : Set (ℝ × M.Point), IsOpen U ∧ x ∈ U ∧
      ∃ q : (ℝ × M.Point) → SquaredCanonicalTensor n,
        IsSmoothVerticalSquaredTensorOn M q U ∧ EqOn q T (U ∩ A) := by
    intro x hx
    let p : Parameter × M.Point := (⟨x.1, hx⟩, x.2)
    obtain ⟨c, U, hUo, hUc, hpU, q, hq, heq⟩ := hs p
    have hgen : IsSmoothVerticalSquaredTensorOn M c.squaredGenerator U :=
      fun b => (c.smooth_squaredGenerator b).mono (fun z hz => ⟨hz.1, hUc hz.2⟩)
    refine ⟨U, hUo, hpU, fun z => q z • c.squaredGenerator z,
      hgen.smul hUo hq, ?_⟩
    intro z hz
    let w : Parameter × M.Point := (⟨z.1, hz.2⟩, z.2)
    have hw : intervalParameterInclusion M w ∈ U := hz.1
    have hr := c.reconstruction (hUc hw) (canonicalSquareMap (J z.1 z.2) (s w))
    rw [c.coefficient_squareMap] at hr
    change q (intervalParameterInclusion M w) •
      c.squaredGenerator (intervalParameterInclusion M w) = T z
    rw [heq w hw]
    dsimp only [T]
    rw [dite_eq_left (show z.1 ∈ parameterInterval from hz.2)]
    exact hr.symm
  obtain ⟨q, hq, heq⟩ := exists_smoothVerticalSquaredTensorExtension_of_local hA T hlocal
  have hagree : ∀ p : Parameter × M.Point,
      q (p.1.val, p.2) = (canonicalSquareMap (J p.1.val p.2) (s p)).val := by
    intro p
    have h := heq (show (p.1.val, p.2) ∈ A from p.1.property)
    dsimp only [T] at h
    rw [dite_eq_left (show p.1.val ∈ parameterInterval from p.1.property)] at h
    exact h
  exact ⟨q, hq, hagree⟩

/-- Reconstruct and glue the interval section's scalar extensions. The
result is a Maslov family on the original prescribed varying two-form,
with its original complex structure at every time and every original
interval tensor value. No target-section regularity is assumed. -/
theorem exists_maslovFamily_of_localScalarExtensions {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    {J : ℝ → AlmostComplexField M}
    (hcompatible : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M (eta t) (J t))
    (hJ : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun z => almostComplexInChart M a (J z.1) z.2))
    (s : (p : Parameter × M.Point) → CanonicalTensorSquare (J p.1.val p.2))
    (hnz : ∀ p, s p ≠ 0)
    (hs : HasLocalSmoothIntervalTensorCoefficients M J s) :
    ∃ f : MaslovFamily M eta, f.J = J ∧
      ∀ p : Parameter × M.Point,
        f.tensor p.1.val p.2 = (canonicalSquareMap (J p.1.val p.2) (s p)).val := by
  obtain ⟨q, hq, hagree⟩ := exists_smoothIntervalTensorExtension_of_localScalarExtensions s hs
  let f : MaslovFamily M eta :=
    { J := J
      tensor := fun t x => q (t, x)
      compatible := hcompatible
      canonical := by
        intro t ht x
        rw [hagree (⟨t, ht⟩, x)]
        exact (canonicalSquareMap (J t x) (s (⟨t, ht⟩, x))).property
      nowhereZero := by
        intro t ht x hz
        apply hnz (⟨t, ht⟩, x)
        apply (canonicalSquareMap_bijective (J t x) ((hcompatible t ht).2.1 x)).1
        apply Subtype.ext
        simpa only [map_zero, Submodule.coe_zero, hagree (⟨t, ht⟩, x)] using hz
      smoothJ := hJ
      smoothSection := by
        intro a
        refine ⟨univ ×ˢ (chartAt (Model (2 * n)) a).target,
          isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target,
          fun p hp => ⟨mem_univ _, hp.2⟩, ?_⟩
        simpa [intrinsicParameterCoordinateDomain, parameterSpatialCoordinates] using hq a }
  exact ⟨f, rfl, hagree⟩

/-- Exact correspondence under the source's genuine scalar extension
convention. Arbitrary interval sections are recovered at all parameter
values, without reparametrizing the geometric family. -/
theorem localScalarExtensions_iff_maslovFamily {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    {J : ℝ → AlmostComplexField M}
    (hcompatible : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M (eta t) (J t))
    (hJ : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun z => almostComplexInChart M a (J z.1) z.2))
    (s : (p : Parameter × M.Point) → CanonicalTensorSquare (J p.1.val p.2))
    (hnz : ∀ p, s p ≠ 0) :
    HasLocalSmoothIntervalTensorCoefficients M J s ↔
      ∃ f : MaslovFamily M eta, f.J = J ∧
        ∀ p : Parameter × M.Point,
          f.tensor p.1.val p.2 = (canonicalSquareMap (J p.1.val p.2) (s p)).val := by
  constructor
  · exact exists_maslovFamily_of_localScalarExtensions hcompatible hJ s hnz
  · rintro ⟨f, rfl, heq⟩
    exact f.localSmoothIntervalTensorCoefficients s heq

end FsFltz.Geometry
