import FsFltz.Geometry.IntrinsicBundleLocalCompletionInverse
import FsFltz.Geometry.IntrinsicNativeCompletionInteriorGradingDerivative
import FsFltz.Geometry.IntrinsicNativeCompletionEndGradingDerivative

/-!
# Differential regularity of the original local inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
The real inverse germs of the original local comparison agree with its
strict slice inverse. Their spatial derivatives in the original interior
and full signed-cylinder charts are therefore invertible at retained interval
points. This is a prerequisite for transporting independently prescribed
source coframes and full canonical-square tensors. No off-base section,
smooth descended section, or geometric target conclusion is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry

/-- A smooth real spatial-coordinate germ with invertible center derivative
has a real-open neighborhood of invertible spatial derivatives. Invertibility
is checked after a fixed source tangent chart, so no continuity of the raw
pointwise tangent-coordinate presentation is assumed. -/
theorem exists_open_spatialCoordinateDerivative_isInvertible {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (N : SmoothManifold d) {R : Set (ℝ × N.Point)} (hR : IsOpen R)
    (f : ℝ × N.Point → V)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, V) ∞ f R)
    (p : ℝ × N.Point) (hp : p ∈ R)
    (hi : (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, V) (fun x => f (p.1, x)) p.2).IsInvertible) :
    ∃ U : Set (ℝ × N.Point), IsOpen U ∧ p ∈ U ∧ U ⊆ R ∧
      ∀ z ∈ U, (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, V) (fun x => f (z.1, x)) z.2).IsInvertible := by
  let c := chartAt (Model d) p.2
  let q : ℝ × Model d → ℝ × N.Point := fun z => (z.1, c.symm z.2)
  let D := intrinsicParameterCoordinateDomain N p.2 R
  have hD : IsOpen D := isOpen_intrinsicParameterCoordinateDomain N p.2 hR
  have hq : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ q D :=
    contMDiffOn_fst.prodMk
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := p.2)).comp
        contMDiffOn_snd (fun _ hz => hz.1.2))
  let g := f ∘ q
  have hgm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, V) ∞ g D :=
    hf.comp hq inter_subset_right
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgm
  have hg : ContDiffOn ℝ ∞ g D := hgm.contDiffOn
  let B : ℝ × Model d → Model d →L[ℝ] V := fun z =>
    (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ ℝ (Model d))
  have hB : ContDiffOn ℝ ∞ B D :=
    (hg.fderiv_of_isOpen (m := ∞) hD (by simp)).clm_comp contDiffOn_const
  have hforward : ∀ z ∈ D, B z =
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, V) (fun y => f (z.1, y)) (c.symm z.2)).comp
        (N.inverseChartTangentMap p.2 z.2) := by
    intro z hz
    have hd : DifferentiableAt ℝ g z :=
      (hg.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
    have hc : HasFDerivAt (fun y : Model d => (z.1, y))
        (ContinuousLinearMap.inr ℝ ℝ (Model d)) z.2 := hasFDerivAt_prodMk_right z.1 z.2
    have hsp : fderiv ℝ (fun y => g (z.1, y)) z.2 = B z :=
      (hd.hasFDerivAt.comp z.2 hc).fderiv
    have hfa : MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, V)
        (fun y => f (z.1, y)) (c.symm z.2) :=
      (((hf.contMDiffAt (hR.mem_nhds hz.2)).comp (c.symm z.2)
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp))
    have hca := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) p.2).mdifferentiableAt_symm hz.1.2
    rw [← hsp, ← mfderiv_eq_fderiv]
    exact mfderiv_comp z.2 hfa hca
  let W := D ∩ B ⁻¹' {A | A.IsInvertible}
  have hW : IsOpen W := hB.continuousOn.isOpen_inter_preimage hD
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hpD : (p.1, c p.2) ∈ D := by
    refine ⟨⟨mem_univ _, c.map_source (mem_chart_source _ _)⟩, ?_⟩
    change (p.1, c.symm (c p.2)) ∈ R
    rwa [c.left_inv (mem_chart_source _ _)]
  have hpW : (p.1, c p.2) ∈ W := by
    refine ⟨hpD, ?_⟩
    change (B (p.1, c p.2)).IsInvertible
    rw [hforward _ hpD, c.left_inv (mem_chart_source _ _)]
    exact hi.comp (inverseChartTangentMap_isInvertible N p.2 (c p.2)
      (c.map_source (mem_chart_source _ _)))
  let U := intrinsicParameterChartDomain N p.2 W
  have hUR : U ⊆ R := by
    intro z hz
    have h := hz.2.1.2
    change (z.1, c.symm (c z.2)) ∈ R at h
    rwa [c.left_inv hz.1.2] at h
  refine ⟨U, isOpen_intrinsicParameterChartDomain N p.2 hW,
    ⟨⟨mem_univ _, mem_chart_source _ _⟩, hpW⟩, hUR, ?_⟩
  intro z hz
  have hBi : (B (z.1, c z.2)).IsInvertible := hz.2.2
  have hrec : (B (z.1, c z.2)).comp (N.chartTangentMap p.2 z.2) =
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, V) (fun x => f (z.1, x)) z.2 := by
    rw [hforward (z.1, c z.2) hz.2.1, c.left_inv hz.1.2]
    have h := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) p.2).symm_comp_deriv hz.1.2
    ext v
    exact congrArg (fun A => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, V)
      (fun x => f (z.1, x)) z.2 (A v)) h
  rw [← hrec]
  exact hBi.comp (chartTangentMap_isInvertible N p.2 z.2 hz.1.2)

private theorem contMDiffOn_open_germExtension
    {E H X F G Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] (I : ModelWithCorners ℝ E H)
    [ChartedSpace H X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace Y] (J : ModelWithCorners ℝ F G)
    [ChartedSpace G Y] (U : TopologicalSpace.Opens X) (γ : U → Y)
    (hγ : ContMDiff I J ∞ γ) (η : X → Y)
    (heq : ∀ z (hz : z ∈ U), η z = γ ⟨z, hz⟩) : ContMDiffOn I J ∞ η U := by
  have hrestrict : ContMDiff I J ∞ (fun z : U => η z.val) := by
    convert hγ using 1
    funext z
    exact heq z.val z.property
  intro z hz
  exact (contMDiffAt_subtype_iff.mp (hrestrict ⟨z, hz⟩)).contMDiffWithinAt

end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

variable (F : LocalCompletionFamily P c t) (L : OriginalBundleLiouvilleLaws P)
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The total interior inverse equation recovers the same strict slice
inverse in the original completion atlas. -/
theorem ambientSourceSliceEquiv_symm_eq_interior_of_total
    (s : F.base) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (w : IntrinsicInterior.Point k M)
    (heq : (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)).val =
      totalInterior F.native.patches (s.val, w)) :
    (F.ambientSourceSliceEquiv L g s.val Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)).symm y =
        interiorIn (F.native.patches s.val) w := by
  apply sliceIn_injective F.native.patches s.val
  exact heq.trans (sliceIn_original F.native.patches s.val w.val).symm

omit [T2Space M] [SecondCountableTopology M] in
/-- The actual interior chart differential of any smooth real germ of the
retained total inverse is invertible at every interval point of that germ.
The comparison and original interior inclusion supply its inverse. -/
theorem isInvertible_ambientReferenceInverse_interiorChart_mfderiv
    (U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point)) (hU : IsOpen U)
    (γ : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicInterior.Point k M)
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (k + 1)) ∞ γ U)
    (heq : ∀ (s : F.base) y, (s.val.val, y) ∈ U →
      (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)).val =
        totalInterior F.native.patches (s.val, γ (s.val.val, y)))
    (s : F.base) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (hy : (s.val.val, y) ∈ U) (u : IntrinsicInterior.Point k M)
    (hchart : γ (s.val.val, y) ∈ (chartAt (Model (k + 1)) u).source) :
    (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (fun z => chartAt (Model (k + 1)) u (γ (s.val.val, z))) y).IsInvertible := by
  let S := F.ambientSourceSliceEquiv L g s.val Q eAs
    (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)
  have hgs : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (fun z => γ (s.val.val, z)) y :=
    ((hγ.contMDiffAt (hU.mem_nhds hy)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hUy : ∀ᶠ z in 𝓝 y, (s.val.val, z) ∈ U :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
  have hs : S.symm =ᶠ[𝓝 y]
      (interiorIn (F.native.patches s.val) ∘ fun z => γ (s.val.val, z)) := by
    filter_upwards [hUy] with z hz
    exact F.ambientSourceSliceEquiv_symm_eq_interior_of_total L g hg hbase Q hdim eAs hp hc
      s z (γ (s.val.val, z)) (heq s z hz)
  have hd := mfderiv_interiorChart_of_completionInterior_factorization F.native.width_pos
    (F.native.collar s.val) (F.native.embedding s.val) (F.native.smooth s.val)
    (F.native.boundary s.val) (F.native.inverse s.val) (F.native.zero s.val)
    Q.source.ambientManifold S (fun z => γ (s.val.val, z)) y hgs hs u hchart
  simp only [Function.comp_def] at hd
  rw [hd]
  have hci : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (chartAt (Model (k + 1)) u) (γ (s.val.val, y))).IsInvertible := by
    have hm := mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u
    apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hm.symm_comp_deriv hchart)
    have h := hm.comp_symm_deriv ((chartAt (Model (k + 1)) u).map_source hchart)
    rwa [(chartAt (Model (k + 1)) u).left_inv hchart] at h
  exact hci.comp ((isInvertible_mfderiv_completionInterior F.native.width_pos
    (F.native.collar s.val) (F.native.embedding s.val) (F.native.smooth s.val)
    (F.native.boundary s.val) (F.native.inverse s.val) (F.native.zero s.val)
    (γ (s.val.val, y))).inverse.comp (S.symm.isInvertible_mfderiv (by simp)))

local instance : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The total signed-cylinder equation recovers the actual slice inverse,
with the original band coordinate and all outward radii. -/
theorem ambientSourceSliceEquiv_symm_eq_cylinder_of_total
    (s : F.base) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (p : Band F.native.width (IntrinsicBoundary.Point k M))
    (heq : (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)).val =
      totalCylinder F.native.patches (s.val, p)) :
    (F.ambientSourceSliceEquiv L g s.val Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)).symm y =
        cylinder (F.native.patches s.val) p := by
  apply sliceIn_injective F.native.patches s.val
  exact heq.trans (sliceIn_cylinder F.native.patches s.val p).symm

omit [T2Space M] [SecondCountableTopology M] in
/-- The full boundary–radius chart differential of a real inverse germ is
invertible at retained interval points. The time-to-radius sign change and
the original full-cylinder derivative are both accounted for. -/
theorem isInvertible_ambientReferenceInverse_endChart_mfderiv
    (U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point)) (hU : IsOpen U)
    (γ : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicBoundary.Point k M × ℝ)
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ γ U)
    (heq : ∀ (s : F.base) y, (s.val.val, y) ∈ U →
      ∃ p : Band F.native.width (IntrinsicBoundary.Point k M),
        p.val = (-(γ (s.val.val, y)).2, (γ (s.val.val, y)).1) ∧
        (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)).val =
          totalCylinder F.native.patches (s.val, p))
    (s : F.base) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (hy : (s.val.val, y) ∈ U) (u : IntrinsicBoundary.Point k M × ℝ)
    (hchart : γ (s.val.val, y) ∈ (chartAt (Model k × ℝ) u).source) :
    (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
      (fun z => chartAt (Model k × ℝ) u (γ (s.val.val, z))) y).IsInvertible := by
  let S := F.ambientSourceSliceEquiv L g s.val Q eAs
    (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)
  have hgm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model k × ℝ) ∞ γ U := by rwa [modelWithCornersSelf_prod]
  have hgs : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
      (fun z => γ (s.val.val, z)) y :=
    ((hgm.contMDiffAt (hU.mem_nhds hy)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hUy : ∀ᶠ z in 𝓝 y, (s.val.val, z) ∈ U :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
  obtain ⟨p, hpcoord, hpeq⟩ := heq s y hy
  have hcoord : endBandCoordinates p = γ (s.val.val, y) := by
    dsimp only [endBandCoordinates]
    rw [hpcoord]
    simp only [neg_neg]
  have hs : ∀ᶠ z in 𝓝 y, ∃ p' : Band F.native.width (IntrinsicBoundary.Point k M),
      endBandCoordinates p' = γ (s.val.val, z) ∧ S.symm z = cylinder (F.native.patches s.val) p' := by
    filter_upwards [hUy] with z hz
    obtain ⟨p', hp'coord, hp'eq⟩ := heq s z hz
    refine ⟨p', ?_, F.ambientSourceSliceEquiv_symm_eq_cylinder_of_total
      L g hg hbase Q hdim eAs hp hc s z p' hp'eq⟩
    dsimp only [endBandCoordinates]
    rw [hp'coord]
    simp only [neg_neg]
  have hd := mfderiv_endChart_of_completionCylinder_factorization F.native.width_pos
    (F.native.collar s.val) (F.native.embedding s.val) (F.native.smooth s.val)
    (F.native.boundary s.val) (F.native.inverse s.val) (F.native.zero s.val)
    Q.source.ambientManifold S (fun z => γ (s.val.val, z)) y hgs p
    (F.ambientSourceSliceEquiv_symm_eq_cylinder_of_total L g hg hbase Q hdim eAs hp hc
      s y p hpeq) hcoord hs u hchart
  simp only [Function.comp_def] at hd
  rw [hd]
  have hci : (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
      (chartAt (Model k × ℝ) u) (γ (s.val.val, y))).IsInvertible := by
    have hm := mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u
    apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hm.symm_comp_deriv hchart)
    have h := hm.comp_symm_deriv ((chartAt (Model k × ℝ) u).map_source hchart)
    rwa [(chartAt (Model k × ℝ) u).left_inv hchart] at h
  exact hci.comp ((isInvertible_mfderiv_endBandCoordinates p).comp
    ((isInvertible_mfderiv_completionCylinder F.native.width_pos
      (F.native.collar s.val) (F.native.embedding s.val) (F.native.smooth s.val)
      (F.native.boundary s.val) (F.native.inverse s.val) (F.native.zero s.val) p).inverse.comp
        (S.symm.isInvertible_mfderiv (by simp))))

/-- The constructed real inverse germs have invertible spatial chart
derivatives on smaller genuine real-open neighborhoods. The source patch is
the original interior or the unchanged full signed cylinder, and every
interval value is the actual retained total inverse. This supplies local
differential regularity for source-coframe transport; it does not construct
or regularize a prescribed Maslov section. -/
theorem ambientReferenceInverse_has_invertible_patchGerms
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ s x, (Q.ambientPresentation s).extensionEquiv
      (eAs parameterZero (R s.val x)).val = (eAs s x).val)
    (s : F.base) (y : Q.source.ambientCompletion.ambient.manifold.Point) :
    (∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (s.val.val, y) ∈ U ∧
      ∃ γ : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicInterior.Point k M,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          𝓘(ℝ, Model (k + 1)) ∞ γ U ∧
        ∃ u : IntrinsicInterior.Point k M,
          (∀ z ∈ U, γ z ∈ (chartAt (Model (k + 1)) u).source) ∧
          (∀ z ∈ U, (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
            (fun x => chartAt (Model (k + 1)) u (γ (z.1, x))) z.2).IsInvertible) ∧
          ∀ (v : F.base) z, (v.val.val, z) ∈ U →
            (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (v, z)).val =
              totalInterior F.native.patches (v.val, γ (v.val.val, z))) ∨
    (∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (s.val.val, y) ∈ U ∧
      ∃ γ : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicBoundary.Point k M × ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ γ U ∧
        ∃ u : IntrinsicBoundary.Point k M × ℝ,
          (∀ z ∈ U, γ z ∈ (chartAt (Model k × ℝ) u).source) ∧
          (∀ z ∈ U, -(γ z).2 < F.native.width) ∧
          (∀ z ∈ U, (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
            (fun x => chartAt (Model k × ℝ) u (γ (z.1, x))) z.2).IsInvertible) ∧
          ∀ (v : F.base) z, (v.val.val, z) ∈ U →
            ∃ p : Band F.native.width (IntrinsicBoundary.Point k M),
              p.val = (-(γ (v.val.val, z)).2, (γ (v.val.val, z)).1) ∧
              (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (v, z)).val =
                totalCylinder F.native.patches (v.val, p)) := by
  classical
  have hi := F.ambientReferenceTotalInverse_realGerms L g hg hbase Q hdim eAs hp hc
    eBs hb hsquareB R hR hsquareA
  rcases hi s y with ⟨U, hpU, γ, hγ, heq⟩ | ⟨U, hpU, γ, hγ, hr, heq⟩
  · let η : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicInterior.Point k M :=
      fun z => if hz : z ∈ U then γ ⟨z, hz⟩ else γ ⟨(s.val.val, y), hpU⟩
    have hηeq : ∀ z (hz : z ∈ U), η z = γ ⟨z, hz⟩ := by
      intro z hz
      simp only [η, dite_eq_left hz]
    have hη : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model (k + 1)) ∞ η U :=
      contMDiffOn_open_germExtension _ _ U γ hγ η hηeq
    have hactual : ∀ (v : F.base) z, (v.val.val, z) ∈ U →
        (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (v, z)).val =
          totalInterior F.native.patches (v.val, η (v.val.val, z)) := by
      intro v z hz
      rw [hηeq _ hz]
      exact heq v z hz
    let u := η (s.val.val, y)
    let S := (U : Set _) ∩ η ⁻¹' (chartAt (Model (k + 1)) u).source
    have hS : IsOpen S := hη.continuousOn.isOpen_inter_preimage U.isOpen
      (chartAt (Model (k + 1)) u).open_source
    have hpS : (s.val.val, y) ∈ S := by
      refine ⟨hpU, ?_⟩
      exact mem_chart_source (Model (k + 1)) u
    let φ := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
      chartAt (Model (k + 1)) u (η z)
    have hφ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model (k + 1)) ∞ φ S :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := u)).comp
        (hη.mono inter_subset_left) inter_subset_right
    have hcenter := F.isInvertible_ambientReferenceInverse_interiorChart_mfderiv
      L g hg hbase Q hdim eAs hp hc U U.isOpen η hη hactual s y hpU u (mem_chart_source _ u)
    obtain ⟨W, hW, hpW, hWS, hderiv⟩ := exists_open_spatialCoordinateDerivative_isInvertible
      Q.source.ambientManifold hS φ hφ (s.val.val, y) hpS hcenter
    exact Or.inl ⟨W, hW, hpW, η, hη.mono (fun z hz => (hWS hz).1), u,
      (fun z hz => (hWS hz).2), hderiv, fun v z hz => hactual v z (hWS hz).1⟩
  · let η : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicBoundary.Point k M × ℝ :=
      fun z => if hz : z ∈ U then γ ⟨z, hz⟩ else γ ⟨(s.val.val, y), hpU⟩
    have hηeq : ∀ z (hz : z ∈ U), η z = γ ⟨z, hz⟩ := by
      intro z hz
      simp only [η, dite_eq_left hz]
    have hη : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
        ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ η U :=
      contMDiffOn_open_germExtension _ _ U γ hγ η hηeq
    have hactual : ∀ (v : F.base) z, (v.val.val, z) ∈ U →
        ∃ p : Band F.native.width (IntrinsicBoundary.Point k M),
          p.val = (-(η (v.val.val, z)).2, (η (v.val.val, z)).1) ∧
          (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (v, z)).val =
            totalCylinder F.native.patches (v.val, p) := by
      intro v z hz
      rw [hηeq _ hz]
      exact heq v z hz
    let u := η (s.val.val, y)
    let S := (U : Set _) ∩ η ⁻¹' (chartAt (Model k × ℝ) u).source
    have hS : IsOpen S := hη.continuousOn.isOpen_inter_preimage U.isOpen
      (chartAt (Model k × ℝ) u).open_source
    have hpS : (s.val.val, y) ∈ S := by
      refine ⟨hpU, ?_⟩
      exact mem_chart_source (Model k × ℝ) u
    let φ := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
      chartAt (Model k × ℝ) u (η z)
    have hηm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model k × ℝ) ∞ η U := by rwa [modelWithCornersSelf_prod]
    have hφ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model k × ℝ) ∞ φ S :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := u)).comp
        (hηm.mono inter_subset_left) inter_subset_right
    have hcenter := F.isInvertible_ambientReferenceInverse_endChart_mfderiv
      L g hg hbase Q hdim eAs hp hc U U.isOpen η hη hactual s y hpU u (mem_chart_source _ u)
    obtain ⟨W, hW, hpW, hWS, hderiv⟩ := exists_open_spatialCoordinateDerivative_isInvertible
      Q.source.ambientManifold hS φ hφ (s.val.val, y) hpS hcenter
    refine Or.inr ⟨W, hW, hpW, η, hη.mono (fun z hz => (hWS hz).1), u,
      (fun z hz => (hWS hz).2), ?_, hderiv, fun v z hz => hactual v z (hWS hz).1⟩
    intro z hz
    rw [hηeq z (hWS hz).1]
    exact hr ⟨z, (hWS hz).1⟩

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily
