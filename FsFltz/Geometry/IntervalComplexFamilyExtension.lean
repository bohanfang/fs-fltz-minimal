import FsFltz.Geometry.IntervalMaslovExtension

/-!
# Gluing genuine local extensions of the interval complex field

Source: `geoemtric-part-fsf.tex`, lines 119–122; `def:maslov`, lines 212–232;
`sec:lean`, lines 794–814. Local endomorphism extensions glue linearly on the
ambient parameter–spatial manifold. Only the prescribed interval values must
be complex and compatible. The constructed extension preserves all those
values and imposes no complex-structure equation outside the interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators TensorProduct
open Set Filter Bundle

namespace FsFltz.Geometry

/-- Genuine smoothness of an endomorphism field on an open ambient
parameter domain, using the actual spatial tangent conjugations. -/
def IsSmoothVerticalEndomorphismOn {d : ℕ} (M : SmoothManifold d)
    (K : (ℝ × M.Point) → Model d →L[ℝ] Model d) (U : Set (ℝ × M.Point)) : Prop :=
  ∀ b, ContDiffOn ℝ ∞ (fun p : ℝ × Model d =>
    almostComplexInChart M b (fun x => K (p.1, x)) p.2)
      (intrinsicParameterCoordinateDomain M b U)

namespace IsSmoothVerticalEndomorphismOn

/-- A fixed-chart endomorphism expression is smooth on the chart overlap. -/
theorem contMDiffAt_chartExpression {d : ℕ} {M : SmoothManifold d}
    {U : Set (ℝ × M.Point)} (hU : IsOpen U)
    {K : (ℝ × M.Point) → Model d →L[ℝ] Model d}
    (hK : IsSmoothVerticalEndomorphismOn M K U)
    (b : M.Point) {x : ℝ × M.Point} (hx : x ∈ U)
    (hxb : x.2 ∈ (chartAt (Model d) b).source) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d →L[ℝ] Model d) ∞
      (fun z : ℝ × M.Point =>
        almostComplexInChart M b (fun y => K (z.1, y)) (chartAt (Model d) b z.2)) x := by
  let e := chartAt (Model d) b
  let C := fun p : ℝ × Model d => almostComplexInChart M b (fun y => K (p.1, y)) p.2
  have hpx : (x.1, e x.2) ∈ intrinsicParameterCoordinateDomain M b U := by
    refine ⟨⟨mem_univ _, e.map_source hxb⟩, ?_⟩
    change (x.1, e.symm (e x.2)) ∈ U
    rwa [e.left_inv hxb]
  have hC : ContMDiffAt 𝓘(ℝ, ℝ × Model d)
      𝓘(ℝ, Model d →L[ℝ] Model d) ∞ C (x.1, e x.2) :=
    contMDiffAt_iff_contDiffAt.mpr ((hK b).contDiffAt
      ((isOpen_intrinsicParameterCoordinateDomain M b hU).mem_nhds hpx))
  have he : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ e x.2 :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := b)).contMDiffAt
      (e.open_source.mem_nhds hxb)
  exact hC.comp x (contMDiffAt_fst.prodMk_space (he.comp x contMDiffAt_snd))

end IsSmoothVerticalEndomorphismOn

/-- A partition of unity glues endomorphism fields smoothly. Conjugation
by the spatial chart differential is linear in the endomorphism, so the
locally finite sum commutes with every tangent transition. -/
theorem smoothVerticalEndomorphism_partition {d : ℕ} {M : SmoothManifold d}
    {ι : Type*} {A : Set (ℝ × M.Point)}
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) (ℝ × M.Point) A)
    (U : ι → Set (ℝ × M.Point)) (hU : ∀ i, IsOpen (U i))
    (hρU : ρ.IsSubordinate U)
    (K : ι → (ℝ × M.Point) → Model d →L[ℝ] Model d)
    (hK : ∀ i, IsSmoothVerticalEndomorphismOn M (K i) (U i)) :
    IsSmoothVerticalEndomorphismOn M (fun x => ∑ᶠ i, ρ i x • K i x) univ := by
  intro b p hp
  let e := chartAt (Model d) b
  let x : ℝ × M.Point := (p.1, e.symm p.2)
  have hpx : p.2 ∈ e.target := hp.1.2
  have hxb : x.2 ∈ e.source := e.map_target hpx
  let g := fun i (z : ℝ × M.Point) =>
    almostComplexInChart M b (fun y => K i (z.1, y)) (e z.2)
  have hg : ∀ i, x ∈ tsupport (ρ i) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d))
        𝓘(ℝ, Model d →L[ℝ] Model d) ∞ (g i) x := by
    intro i hi
    exact (hK i).contMDiffAt_chartExpression (hU i) b (hρU i hi) hxb
  have hsum := ρ.contMDiffAt_finsum hg
  have he : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ e.symm p.2 :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := b)).contMDiffAt
      (e.open_target.mem_nhds hpx)
  have hmap : ContMDiffAt 𝓘(ℝ, ℝ × Model d)
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × Model d => (p.1, e.symm p.2)) p :=
    contDiff_fst.contMDiff.contMDiffAt.prodMk
      (he.comp p contDiff_snd.contMDiff.contMDiffAt)
  apply ((hsum.comp p hmap).contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(isOpen_univ.prod e.open_target).mem_nhds
    (show p ∈ univ ×ˢ e.target from ⟨mem_univ _, hpx⟩)] with q hq
  let z : ℝ × M.Point := (q.1, e.symm q.2)
  let R : Model d →L[ℝ] Model d := M.chartTangentMap b z.2
  let S : Model d →L[ℝ] Model d := M.inverseChartTangentMap b q.2
  let L : (Model d →L[ℝ] Model d) →L[ℝ] (Model d →L[ℝ] Model d) :=
    (ContinuousLinearMap.compL ℝ (Model d) (Model d) (Model d) R).comp
      ((ContinuousLinearMap.compL ℝ (Model d) (Model d) (Model d)).flip S)
  have hfin : (Function.support (fun i => ρ i z • K i z)).Finite :=
    (ρ.locallyFinite.point_finite z).subset (by
      intro i hi
      change ρ i z ≠ 0
      intro hz
      apply hi
      change ρ i z • K i z = 0
      rw [hz]
      exact zero_smul ℝ (K i z))
  have hcomm := L.toLinearMap.toAddMonoidHom.map_finsum hfin
  change L (∑ᶠ i, ρ i z • K i z) = ∑ᶠ i, L (ρ i z • K i z) at hcomm
  symm
  change (∑ᶠ i, ρ i z • g i z) = L (∑ᶠ i, ρ i z • K i z)
  rw [hcomm]
  apply finsum_congr
  intro i
  rw [L.map_smul]
  congr 1
  dsimp only [g, almostComplexInChart, z]
  rw [e.right_inv hq.2]
  rfl

/-- Genuine local extensions of an arbitrary interval endomorphism field.
The witnesses are sections of the ordinary tangent-endomorphism bundle on
open neighborhoods, with chartwise C∞ smoothness and literal interval
agreement. No global endomorphism extension is assumed. -/
def HasLocalSmoothIntervalComplexExtensions {d : ℕ}
    (M : SmoothManifold d) (J : ℝ → AlmostComplexField M) : Prop :=
  ∀ p : Parameter × M.Point,
    ∃ U : Set (ℝ × M.Point), IsOpen U ∧ intervalParameterInclusion M p ∈ U ∧
      ∃ K : (ℝ × M.Point) → Model d →L[ℝ] Model d,
        IsSmoothVerticalEndomorphismOn M K U ∧
        ∀ z : Parameter × M.Point, intervalParameterInclusion M z ∈ U →
          K (intervalParameterInclusion M z) = J z.1.val z.2

/-- Local C∞ endomorphism extensions glue to one raw almost complex
field family. Every interval endomorphism is fixed. Its complex and
compatibility equations are inherited exactly on that interval. -/
theorem exists_smoothComplexFamily_of_localExtensions {d : ℕ}
    {M : SmoothManifold d} (J : ℝ → AlmostComplexField M)
    (hJ : HasLocalSmoothIntervalComplexExtensions M J) :
    ∃ K : ℝ → AlmostComplexField M,
      (∀ a, SmoothNearInterval (chartAt (Model d) a).target
        (fun z => almostComplexInChart M a (K z.1) z.2)) ∧
      ∀ t : Parameter, K t.val = J t.val := by
  classical
  let A : Set (ℝ × M.Point) := {x | x.1 ∈ parameterInterval}
  have hA : IsClosed A := isClosed_Icc.preimage continuous_fst
  let I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)
  let : LocallyCompactSpace M.Point := ChartedSpace.locallyCompactSpace (Model d) M.Point
  choose U hU hpU K hK heq using fun p : Parameter × M.Point => hJ p
  have hcover : A ⊆ ⋃ p : Parameter × M.Point, U p := by
    intro x hx
    exact mem_iUnion_of_mem (⟨x.1, hx⟩, x.2) (hpU (⟨x.1, hx⟩, x.2))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hA U hU hcover
  let L : (ℝ × M.Point) → Model d →L[ℝ] Model d := fun x => ∑ᶠ i, ρ i x • K i x
  have hL := smoothVerticalEndomorphism_partition ρ U hU hρ K hK
  refine ⟨fun t x => L (t, x), ?_, ?_⟩
  · intro a
    refine ⟨univ ×ˢ (chartAt (Model d) a).target,
      isOpen_univ.prod (chartAt (Model d) a).open_target,
      fun p hp => ⟨mem_univ _, hp.2⟩, ?_⟩
    simpa [intrinsicParameterCoordinateDomain, parameterSpatialCoordinates] using hL a
  · intro t
    funext x
    let Jx : Model d →L[ℝ] Model d := J t.val x
    have hterms : ∀ i, ρ i (t.val, x) • K i (t.val, x) = ρ i (t.val, x) • Jx := by
      intro i
      by_cases hi : ρ i (t.val, x) = 0
      · rw [hi]
        exact (zero_smul ℝ (K i (t.val, x))).trans (zero_smul ℝ Jx).symm
      · have h : K i (t.val, x) = Jx :=
          heq i (t, x) (hρ i (subset_closure (Function.mem_support.mpr hi)))
        exact congrArg (fun Q : Model d →L[ℝ] Model d => ρ i (t.val, x) • Q) h
    change (∑ᶠ i, ρ i (t.val, x) • K i (t.val, x)) = Jx
    simp_rw [hterms]
    rw [← finsum_smul (fun i => ρ i (t.val, x)) Jx,
      ρ.sum_eq_one (show (t.val, x) ∈ A from t.property)]
    exact one_smul ℝ Jx

/-- The full source-local grading data produce one encoded Maslov family.
Local smooth endomorphism extensions supply `smoothJ`; local scalar
coefficient extensions supply the tensor family. Both independently glued
families retain every original interval value, including both endpoints.
The original two-form and parameter are unchanged. -/
theorem exists_maslovFamily_of_localExtensions {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (J : ℝ → AlmostComplexField M)
    (hcompatible : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M (eta t) (J t))
    (hJ : HasLocalSmoothIntervalComplexExtensions M J)
    (s : (p : Parameter × M.Point) → CanonicalTensorSquare (J p.1.val p.2))
    (hnz : ∀ p, s p ≠ 0)
    (hs : HasLocalSmoothIntervalTensorCoefficients M J s) :
    ∃ f : MaslovFamily M eta,
      (∀ t : Parameter, f.J t.val = J t.val) ∧
      ∀ p : Parameter × M.Point,
        f.tensor p.1.val p.2 = (canonicalSquareMap (J p.1.val p.2) (s p)).val := by
  obtain ⟨K, hK, hKJ⟩ := exists_smoothComplexFamily_of_localExtensions J hJ
  obtain ⟨q, hq, hqs⟩ := exists_smoothIntervalTensorExtension_of_localScalarExtensions s hs
  let f : MaslovFamily M eta :=
    { J := K
      tensor := fun t x => q (t, x)
      compatible := by
        intro t ht
        rw [hKJ ⟨t, ht⟩]
        exact hcompatible t ht
      canonical := by
        intro t ht x
        rw [hKJ ⟨t, ht⟩, hqs (⟨t, ht⟩, x)]
        exact (canonicalSquareMap (J t x) (s (⟨t, ht⟩, x))).property
      nowhereZero := by
        intro t ht x hz
        apply hnz (⟨t, ht⟩, x)
        apply (canonicalSquareMap_bijective (J t x) ((hcompatible t ht).2.1 x)).1
        apply Subtype.ext
        simpa only [map_zero, Submodule.coe_zero, hqs (⟨t, ht⟩, x)] using hz
      smoothJ := hK
      smoothSection := by
        intro a
        refine ⟨univ ×ˢ (chartAt (Model (2 * n)) a).target,
          isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target,
          fun p hp => ⟨mem_univ _, hp.2⟩, ?_⟩
        simpa [intrinsicParameterCoordinateDomain, parameterSpatialCoordinates] using hq a }
  exact ⟨f, hKJ, hqs⟩

end FsFltz.Geometry
