import FsFltz.Geometry.IntrinsicLiouvilleFamilyExtension
import FsFltz.Geometry.SmoothMapFiniteExtension
import FsFltz.Geometry.Identification
import FsFltz.Geometry.CompactMapNeighborhood
import FsFltz.Geometry.NativeCompactMapTangents

/-!
# Prescribed native compact diffeomorphisms on independent presentations

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189, and
`sec:lean`, lines 803–814. Native across-boundary smoothness means actual
open coordinate germs. Source and target primitive data independently
construct their compact Liouville presentations. The prescribed native map
and inverse are retained on the whole carriers, and constant primitive
scaling is an equality of full tangent covectors, including the boundary.

This is a positive-dimensional foundation. It asserts no geometric
comparison chain, endpoint core equality, grading or full-fiber marking.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [IsManifold (𝓡∂ (k + 1)) ∞ N]

/-- Across-boundary smoothness for a native map into another native
manifold with boundary. These are original source/target chart germs;
no boundaryless presentation, extended map or global equivalence is input. -/
def IsLocallyExtendibleNativeMap (f : M → N) : Prop :=
  ∀ (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ x ∈ e.source,
    ∀ (a : OpenPartialHomeomorph N (EuclideanHalfSpace (k + 1))),
      a ∈ atlas (EuclideanHalfSpace (k + 1)) N → f x ∈ a.source →
      ∃ (U : Set (Model (k + 1))) (β : Model (k + 1) → Model (k + 1)),
        IsOpen U ∧ e.extend (𝓡∂ (k + 1)) x ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
        ∀ y ∈ e.source, e.extend (𝓡∂ (k + 1)) y ∈ U →
          β (e.extend (𝓡∂ (k + 1)) y) = a.extend (𝓡∂ (k + 1)) (f y)

/-- The concrete correspondence supplied by the native primitive producer.
The coordinate-extension field consists of actual open smooth maps with
literal carrier agreement, rather than an assumed presentation relation. -/
structure NativeLiouvillePresentation (α : Form k M 1) where
  domain : LiouvilleDomain (k + 1)
  inclusion : M → domain.domain.extension.Point
  carrierEquiv : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M domain.domain.Point ∞
  carrier_square : ∀ x, (carrierEquiv x).val = inclusion x
  smooth_inclusion : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ inclusion
  embedding : Topology.IsClosedEmbedding inclusion
  tangent_bijective : ∀ x, Function.Bijective
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) inclusion x)
  carrier_range : range inclusion = domain.domain.carrier
  primitive : (fun x => (domain.liouville.primitive (inclusion x)).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) inclusion x)) = α
  differential : (fun x =>
    (domain.domain.extension.exteriorDerivative domain.liouville.primitive (inclusion x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) inclusion x)) = exteriorDerivative α
  coordinates : HasNativeCoordinateExtensions (k := k) domain.domain.extension inclusion

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- A single native primitive supplies joint germs for its constant family.
The parameter introduces no new geometric hypothesis. -/
theorem IsLocallyExtendibleForm.constantFamily {α : Form k M 1}
    (hα : IsLocallyExtendibleForm α) :
    IsLocallyExtendibleFormFamily (fun _ : Parameter => α) := by
  intro e he t x hx
  obtain ⟨β, U, hU, hxU, hβ, heq⟩ := hα e he x hx
  obtain ⟨V, hVeq, hV, hxV⟩ :=
    mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp heq)
  let W : Set (ℝ × Model (k + 1)) := univ ×ˢ (U ∩ V)
  refine ⟨W, (fun p => β p.2), isOpen_univ.prod (hU.inter hV),
    ⟨mem_univ _, hxU, hxV⟩, ?_, ?_⟩
  · exact hβ.comp contDiff_snd.contDiffOn (fun _ hp => hp.2.1)
  · intro s y hy hyW
    exact hVeq hyW.2.2 hy

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- Source primitive, nondegeneracy and local defining-function outwardness
construct a native presentation with actual source-coordinate extensions.
The constant-family specialization retains one independently selected
spatial presentation and imposes no parameter-family premise. -/
theorem exists_nativeLiouvillePresentation
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    Nonempty (NativeLiouvillePresentation α) := by
  obtain ⟨D, i, e, L, he, hi, hemb, hbij, hrange, _, _, _, hpull,
    hderiv, _, _, _, hcoord⟩ :=
    exists_liouvilleFamily_with_native_presentation_and_coordinates
      (fun _ : Parameter => α) hα.constantFamily (fun _ => hnd) (fun _ => hout)
  exact ⟨{ domain := ⟨D, L parameterZero⟩
           inclusion := i
           carrierEquiv := e
           carrier_square := he
           smooth_inclusion := hi
           embedding := hemb
           tangent_bijective := hbij
           carrier_range := hrange
           primitive := hpull parameterZero
           differential := hderiv parameterZero
           coordinates := hcoord }⟩

namespace NativeLiouvillePresentation

/-- Restricting an extension neighborhood transports the same native
carrier, primitive, full differential and coordinate extension germs. -/
def restrict {α : Form k M 1} (P : NativeLiouvillePresentation α)
    (U : TopologicalSpace.Opens P.domain.domain.extension.Point)
    (hU : P.domain.domain.carrier ⊆ U) : NativeLiouvillePresentation α := by
  let D := P.domain.restrict U hU
  let := D.domain.halfSpaceChartedSpace
  let i : M → D.domain.extension.Point := fun x =>
    ⟨P.inclusion x, hU (P.carrier_range ▸ mem_range_self x)⟩
  let e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.domain.Point ∞ :=
    P.carrierEquiv.trans (P.domain.domain.restrictPointDiffeomorph U hU).symm
  have hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i :=
    (ContMDiff.subtypeVal_comp_iff U i).mp P.smooth_inclusion
  have hval : (Subtype.val : U → P.domain.domain.extension.Point) ∘ i = P.inclusion := rfl
  have hdi (x : M) :
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.inclusion x := by
    have hd := mfderiv_comp (f := i) (g := Subtype.val) x
      ((P.domain.domain.extension.restrictInclusion U).map.contMDiff.mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))
    rw [hval] at hd
    erw [P.domain.domain.extension.mfderiv_restrict_val U (i x)] at hd
    exact hd.symm
  refine
    { domain := D
      inclusion := i
      carrierEquiv := e
      carrier_square := ?_
      smooth_inclusion := hi
      embedding := Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal
        (hval ▸ P.embedding)
      tangent_bijective := ?_
      carrier_range := ?_
      primitive := ?_
      differential := ?_
      coordinates := ?_ }
  · intro x
    exact Subtype.ext (P.carrier_square x)
  · intro x
    rw [hdi]
    exact P.tangent_bijective x
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      change P.inclusion x ∈ P.domain.domain.carrier
      exact P.carrier_range ▸ mem_range_self x
    · intro hy
      change y.val ∈ P.domain.domain.carrier at hy
      rw [← P.carrier_range] at hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  · funext x
    change ((P.domain.domain.extension.restrict U).pullback P.domain.domain.extension
      Subtype.val P.domain.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α x
    rw [P.domain.domain.extension.pullback_restrict_val, hdi]
    exact congrFun P.primitive x
  · funext x
    change ((P.domain.domain.extension.restrict U).exteriorDerivative
      ((P.domain.domain.extension.restrict U).pullback P.domain.domain.extension Subtype.val
        P.domain.liouville.primitive) (i x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = exteriorDerivative α x
    rw [P.domain.domain.extension.exteriorDerivative_restrict U
      P.domain.liouville.primitive P.domain.liouville.smooth_primitive, hdi]
    exact congrFun P.differential x
  · intro x
    obtain ⟨a, O, R, ha, hO, hxO, hR, hag⟩ := P.coordinates x
    refine ⟨a, Subtype.val ⁻¹' O, R ∘ Subtype.val, ha,
      hO.preimage continuous_subtype_val, hxO,
      hR.comp contMDiff_subtype_val.contMDiffOn (fun _ hz => hz), ?_⟩
    intro y hy
    exact hag y hy

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
@[simp] theorem restrict_inclusion_val {α : Form k M 1} (P : NativeLiouvillePresentation α)
    (U : TopologicalSpace.Opens P.domain.domain.extension.Point)
    (hU : P.domain.domain.carrier ⊆ U) (x : M) :
    ((P.restrict U hU).inclusion x).val = P.inclusion x := rfl

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
/-- An extended native chart has an invertible full ambient differential.
The identity is derived on native points and includes boundary tangents. -/
theorem bijective_coordinate_derivative {α : Form k M 1}
    (P : NativeLiouvillePresentation α)
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (O : Set P.domain.domain.extension.Point) (hO : IsOpen O)
    (Q : P.domain.domain.extension.Point → Model (k + 1))
    (hQ : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ Q O)
    (hag : ∀ y, P.inclusion y ∈ O → y ∈ e.source ∧
      Q (P.inclusion y) = e.extend (𝓡∂ (k + 1)) y)
    (x : M) (hx : P.inclusion x ∈ O) :
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) Q (P.inclusion x)) := by
  have heq : Q ∘ P.inclusion =ᶠ[𝓝 x] e.extend (𝓡∂ (k + 1)) := by
    filter_upwards [P.smooth_inclusion.continuous.continuousAt.preimage_mem_nhds
      (hO.mem_nhds hx)] with y hy
    exact (hag y hy).2
  have hd := mfderiv_comp x
    ((hQ.contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp))
    (P.smooth_inclusion.mdifferentiableAt (by simp))
  have hchart : Function.Bijective (chartTangentMap e x) := by
    constructor
    · intro v w hvw
      exact (inverseChartTangentMap_chartTangentMap he (hag x hx).1 v).symm.trans
        ((congrArg (inverseChartTangentMap e (e.extend (𝓡∂ (k + 1)) x)) hvw).trans
          (inverseChartTangentMap_chartTangentMap he (hag x hx).1 w))
    · intro v
      have hxt : e.extend (𝓡∂ (k + 1)) x ∈ (e.extend (𝓡∂ (k + 1))).target :=
        (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using (hag x hx).1)
      refine ⟨inverseChartTangentMap e (e.extend (𝓡∂ (k + 1)) x) v, ?_⟩
      have hv := chartTangentMap_inverseChartTangentMap he hxt v
      have hi : (e.extend (𝓡∂ (k + 1))).symm (e.extend (𝓡∂ (k + 1)) x) = x :=
        (e.extend (𝓡∂ (k + 1))).left_inv
          (by simpa only [e.extend_source] using (hag x hx).1)
      rw [hi] at hv
      exact hv
  have hs : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) Q (P.inclusion x)).comp
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.inclusion x) = chartTangentMap e x :=
    hd.symm.trans heq.mfderiv_eq
  constructor
  · intro v w hvw
    obtain ⟨a, rfl⟩ := (P.tangent_bijective x).2 v
    obtain ⟨b, rfl⟩ := (P.tangent_bijective x).2 w
    apply congrArg (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.inclusion x)
    apply hchart.1
    exact (congrArg (fun T => T a) hs).symm.trans
      (hvw.trans (congrArg (fun T => T b) hs))
  · intro v
    obtain ⟨a, ha⟩ := hchart.2 v
    exact ⟨mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.inclusion x a,
      (congrArg (fun T => T a) hs).trans ha⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M] in
/-- Original native coordinate germs glue to an ambient map on a
neighborhood of the entire source carrier. Both presentations are fixed
before this construction; target coordinate inverses are derived by the
inverse function theorem from the produced full tangent correspondence. -/
theorem exists_nativeMapExtension {α : Form k M 1} {β : Form k N 1}
    (P : NativeLiouvillePresentation (k := k) α) (Q : NativeLiouvillePresentation (k := k) β)
    (f : M → N) (hf : Continuous f) (hfg : IsLocallyExtendibleNativeMap (k := k) f) :
    ∃ (W : TopologicalSpace.Opens P.domain.domain.extension.Point)
      (_hW : range P.inclusion ⊆ W) (g : W → Q.domain.domain.extension.Point),
      ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
        ∀ x (hx : P.inclusion x ∈ W), g ⟨P.inclusion x, hx⟩ = Q.inclusion (f x) := by
  classical
  let f₀ : range P.inclusion → Q.domain.domain.extension.Point :=
    fun p => Q.inclusion (f p.property.choose)
  have hfi (x : M) (hx : P.inclusion x ∈ range P.inclusion) :
      f₀ ⟨P.inclusion x, hx⟩ = Q.inclusion (f x) := by
    exact congrArg (Q.inclusion ∘ f) (P.embedding.injective hx.choose_spec)
  have hlocal : ∀ p : range P.inclusion,
      ∃ O : TopologicalSpace.Opens P.domain.domain.extension.Point, p.val ∈ O ∧
        ∃ g : O → Q.domain.domain.extension.Point,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
          ∀ y (hyO : y ∈ O) (hyA : y ∈ range P.inclusion), g ⟨y, hyO⟩ = f₀ ⟨y, hyA⟩ := by
    rintro ⟨z, x, rfl⟩
    obtain ⟨a, A, R, ha, hA, hxA, hR, hagR⟩ := Q.coordinates (f x)
    obtain ⟨q, hxq, hq⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold hA hR hxA
      (Q.bijective_coordinate_derivative a ha A hA R hR hagR (f x) hxA)
    obtain ⟨e, V, S, he, hV, hxV, hS, hagS⟩ := P.coordinates x
    obtain ⟨U, v, hU, hxU, hv, hvag⟩ :=
      hfg e he x (hagS x hxV).1 a ha (hagR (f x) hxA).1
    let B : Set M := (Q.inclusion ∘ f) ⁻¹' (A ∩ q.source)
    have hB : IsOpen B := (hA.inter q.open_source).preimage
      (Q.smooth_inclusion.continuous.comp hf)
    obtain ⟨T, hT, hTP⟩ := P.embedding.isEmbedding.isInducing.isOpen_iff.mp hB
    have hxT : P.inclusion x ∈ T := by
      change x ∈ P.inclusion ⁻¹' T
      rw [hTP]
      exact ⟨hxA, hxq⟩
    let C : Set P.domain.domain.extension.Point := V ∩ S ⁻¹' U
    have hC : IsOpen C := hS.continuousOn.isOpen_inter_preimage hV hU
    let F : P.domain.domain.extension.Point → Model (k + 1) := v ∘ S
    have hF : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ F C :=
      hv.contMDiffOn.comp (hS.mono inter_subset_left) (fun _ hz => hz.2)
    have hxC : P.inclusion x ∈ C := ⟨hxV, by
      change S (P.inclusion x) ∈ U
      rwa [(hagS x hxV).2]⟩
    have hFx : F (P.inclusion x) = q (Q.inclusion (f x)) := by
      change v (S (P.inclusion x)) = _
      rw [(hagS x hxV).2, hvag x (hagS x hxV).1 hxU]
      exact (hagR (f x) hxA).2.symm.trans (hq hxq)
    let O : TopologicalSpace.Opens P.domain.domain.extension.Point :=
      ⟨(C ∩ T) ∩ F ⁻¹' q.target,
        (hF.mono inter_subset_left).continuousOn.isOpen_inter_preimage (hC.inter hT) q.open_target⟩
    have hxO : P.inclusion x ∈ O := ⟨⟨hxC, hxT⟩, by
      change F (P.inclusion x) ∈ q.target
      rw [hFx]
      exact q.map_source hxq⟩
    have hFO : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
        (fun p : O => F p.val) := by
      intro p
      exact (hF.contMDiffAt (hC.mem_nhds p.property.1.1)).comp
        p contMDiff_subtype_val.contMDiffAt
    let g : O → Q.domain.domain.extension.Point := fun p => q.invFun (F p.val)
    have hg : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g :=
      q.contMDiffOn_invFun.comp_contMDiff hFO (fun p => p.property.2)
    refine ⟨O, hxO, g, hg, ?_⟩
    intro y hyO hyA
    obtain ⟨w, rfl⟩ := hyA
    have hwT : w ∈ B := by
      rw [← hTP]
      exact hyO.1.2
    have hwV : P.inclusion w ∈ V := hyO.1.1.1
    have hwU : e.extend (𝓡∂ (k + 1)) w ∈ U := by
      rw [← (hagS w hwV).2]
      exact hyO.1.1.2
    have hFw : F (P.inclusion w) = q (Q.inclusion (f w)) := by
      change v (S (P.inclusion w)) = _
      rw [(hagS w hwV).2, hvag w (hagS w hwV).1 hwU]
      exact (hagR (f w) hwT.1).2.symm.trans (hq hwT.2)
    change q.invFun (F (P.inclusion w)) = f₀ _
    exact (congrArg q.invFun hFw).trans ((q.left_inv hwT.2).trans (hfi w _).symm)
  have hcompact : IsCompact (range P.inclusion) := by
    simpa only [image_univ] using isCompact_univ.image P.embedding.continuous
  obtain ⟨W, hW, g, hg, heq⟩ :=
    SmoothMapExtension.exists_smoothMapExtension_of_compact hcompact f₀ hlocal
  exact ⟨W, hW, g, hg, fun x hx =>
    (heq (P.inclusion x) hx (mem_range_self x)).trans (hfi x _)⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M] in
/-- A prescribed native diffeomorphism is represented on simultaneous
open restrictions of two independently fixed presentations. The inverse
function theorem constructs the neighborhood inverse; the actual native
inverse is retained on every target carrier point. The two restrictions
also make the statement valid when the native manifolds are empty. -/
theorem exists_restrictedNativeCompactDiffeomorph
    {α : Form k M 1} {β : Form k N 1}
    (P : NativeLiouvillePresentation (k := k) α) (Q : NativeLiouvillePresentation (k := k) β)
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) :
    ∃ (W : TopologicalSpace.Opens P.domain.domain.extension.Point)
      (hW : P.domain.domain.carrier ⊆ W)
      (U : TopologicalSpace.Opens (P.domain.restrict W hW).domain.extension.Point)
      (hU : (P.domain.restrict W hW).domain.carrier ⊆ U)
      (V : TopologicalSpace.Opens Q.domain.domain.extension.Point)
      (hV : Q.domain.domain.carrier ⊆ V)
      (g : CompactDomainDiffeomorph
        ((P.domain.restrict W hW).restrict U hU).domain (Q.domain.restrict V hV).domain),
      (∀ x, g.map (((P.restrict W hW).restrict U hU).inclusion x) =
        (Q.restrict V hV).inclusion (h x)) ∧
      (∀ y, g.inverse ((Q.restrict V hV).inclusion y) =
        ((P.restrict W hW).restrict U hU).inclusion (h.symm y)) ∧
      (∀ x ∈ ((P.domain.restrict W hW).restrict U hU).domain.carrier,
        ((P.domain.restrict W hW).restrict U hU).domain.extension.pullback
          (Q.domain.restrict V hV).domain.extension g.map (Q.domain.restrict V hV).liouville.primitive x =
        c • ((P.domain.restrict W hW).restrict U hU).liouville.primitive x) := by
  obtain ⟨W, hWr, f, hf, hfeq⟩ := P.exists_nativeMapExtension Q h h.continuous hgerm
  have hW : P.domain.domain.carrier ⊆ W := P.carrier_range ▸ hWr
  let P₀ := P.restrict W hW
  have hfNative (x : M) : f (P₀.inclusion x) = Q.inclusion (h x) := hfeq x _
  have himm : ∀ z ∈ P₀.domain.domain.carrier,
      Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f z) := by
    intro z hz
    rw [← P₀.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    exact NativeCompactMap.injective_mfderiv_of_native_square
      P₀.domain.domain.extension Q.domain.domain.extension P₀.inclusion Q.inclusion
      P₀.smooth_inclusion Q.smooth_inclusion P₀.tangent_bijective Q.tangent_bijective h f
      (fun _ => hf.mdifferentiableAt (by simp)) hfNative x
  have hinj : InjOn f P₀.domain.domain.carrier := by
    intro z hz w hw hzw
    rw [← P₀.carrier_range] at hz hw
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    rw [hfNative, hfNative] at hzw
    exact congrArg P₀.inclusion (h.injective (Q.embedding.injective hzw))
  obtain ⟨U, hU, V, e, _, he⟩ :=
    P₀.domain.domain.extension.exists_smoothEquiv_neighborhood Q.domain.domain.extension
      P₀.domain.domain.carrier P₀.domain.domain.compact f univ isOpen_univ
      (subset_univ _) hf.contMDiffOn hinj himm
  have hV : Q.domain.domain.carrier ⊆ V := by
    intro y hy
    rw [← Q.carrier_range] at hy
    obtain ⟨z, rfl⟩ := hy
    let x : U := ⟨P₀.inclusion (h.symm z), hU (P₀.carrier_range ▸ mem_range_self _)⟩
    have hs : (e x).val = Q.inclusion z :=
      (he x).trans ((hfNative (h.symm z)).trans (congrArg Q.inclusion (h.apply_symm_apply z)))
    exact hs ▸ (e x).property
  let P₁ := P₀.restrict U hU
  let Q₁ := Q.restrict V hV
  have hsquare (x : M) : e (P₁.inclusion x) = Q₁.inclusion (h x) :=
    Subtype.ext ((he _).trans (hfNative x))
  have hcarrier : e '' P₁.domain.domain.carrier = Q₁.domain.domain.carrier := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← P₁.carrier_range] at hx
      obtain ⟨z, rfl⟩ := hx
      rw [hsquare]
      exact Q₁.carrier_range ▸ mem_range_self _
    · intro hy
      rw [← Q₁.carrier_range] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨P₁.inclusion (h.symm z), P₁.carrier_range ▸ mem_range_self _, ?_⟩
      exact (hsquare _).trans (congrArg Q₁.inclusion (h.apply_symm_apply z))
  let g : CompactDomainDiffeomorph P₁.domain.domain Q₁.domain.domain :=
    { map := e
      inverse := e.symm
      sourceNeighbourhood := univ
      targetNeighbourhood := univ
      open_source := isOpen_univ
      open_target := isOpen_univ
      contains_source := subset_univ _
      contains_target := subset_univ _
      smooth_map := e.contMDiff.contMDiffOn
      smooth_inverse := e.symm.contMDiff.contMDiffOn
      maps_source := fun x hx => hcarrier ▸ mem_image_of_mem e hx
      maps_target := by
        intro y hy
        rw [← hcarrier] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        simpa only [e.symm_apply_apply] using hx
      left_inverse := fun x _ => e.symm_apply_apply x
      right_inverse := fun y _ => e.apply_symm_apply y
      immersion := fun _ _ => (e.isInvertible_mfderiv (by simp)).injective }
  refine ⟨W, hW, U, hU, V, hV, g, hsquare, ?_, ?_⟩
  · intro y
    have heq := hsquare (h.symm y)
    rw [h.apply_symm_apply] at heq
    exact (congrArg e.symm heq).symm.trans (e.symm_apply_apply _)
  · intro x hx
    change x ∈ P₁.domain.domain.carrier at hx
    change P₁.domain.domain.extension.pullback Q₁.domain.domain.extension g.map
      Q₁.domain.liouville.primitive x = c • P₁.domain.liouville.primitive x
    rw [← P₁.carrier_range] at hx
    obtain ⟨z, rfl⟩ := hx
    exact NativeCompactMap.primitive_scaled_of_native_square
      P₁.domain.domain.extension Q₁.domain.domain.extension P₁.inclusion Q₁.inclusion
      P₁.smooth_inclusion Q₁.smooth_inclusion P₁.tangent_bijective h e
      (fun _ => e.contMDiff.mdifferentiableAt (by simp)) hsquare
      P₁.domain.liouville.primitive Q₁.domain.liouville.primitive α β
      (congrFun P₁.primitive) (congrFun Q₁.primitive) c hscale z

end NativeLiouvillePresentation

variable [T2Space N] [SecondCountableTopology N] [CompactSpace N]

/-- Original native Liouville data and a prescribed constant-scale native
diffeomorphism construct both representations and the actual compact map.
The source and target primitive producers are invoked independently; only
their extension neighborhoods are then restricted. Native maps, native
inverse, primitive tensors and exterior derivatives are retained through
the returned concrete presentations. No domain or map-extension certificate
is a premise. Dimension zero has its separate discrete native producer. -/
theorem exists_nativeCompactDiffeomorph
    (α : Form k M 1) (β : Form k N 1)
    (hα : IsLocallyExtendibleForm α) (hβ : IsLocallyExtendibleForm β)
    (hndα : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hndβ : ∀ y, Nondegenerate (exteriorDerivative β) y)
    (houtα : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (houtβ : ∀ x : IntrinsicBoundary.Point k N,
      ∃ (rho : N → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector β (exteriorDerivative β) x.val)))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) :
    ∃ (P : NativeLiouvillePresentation (k := k) α) (Q : NativeLiouvillePresentation (k := k) β)
      (g : CompactDomainDiffeomorph P.domain.domain Q.domain.domain),
      (∀ x, g.map (P.inclusion x) = Q.inclusion (h x)) ∧
      (∀ y, g.inverse (Q.inclusion y) = P.inclusion (h.symm y)) ∧
      (∀ x ∈ P.domain.domain.carrier,
        P.domain.domain.extension.pullback Q.domain.domain.extension g.map Q.domain.liouville.primitive x =
          c • P.domain.liouville.primitive x) := by
  obtain ⟨P⟩ := exists_nativeLiouvillePresentation α hα hndα houtα
  obtain ⟨Q⟩ := exists_nativeLiouvillePresentation β hβ hndβ houtβ
  obtain ⟨W, hW, U, hU, V, hV, g, hsquare, hinverse, hprim⟩ :=
    P.exists_restrictedNativeCompactDiffeomorph Q h hgerm c hscale
  exact ⟨(P.restrict W hW).restrict U hU, Q.restrict V hV, g, hsquare, hinverse, hprim⟩

end FsFltz.Geometry.IntrinsicLiouville
