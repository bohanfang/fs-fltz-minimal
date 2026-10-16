import FsFltz.Geometry.IntrinsicCompletionNative
import FsFltz.Geometry.IntrinsicCompletionField
import FsFltz.Geometry.CompletionMapUniqueness
import FsFltz.Geometry.IntrinsicPresentationMapExtension

/-!
# Correspondence with an independently prescribed actual completion

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and
`sec:lean`, lines 805–813. The original primitive data produce a native
inward collar. Native field transport and right ODE uniqueness identify its
points in both actual completions, giving smooth germs of the same native
identity across the compact boundary. Interior inverse-function germs and
compact smooth-map gluing produce the compact comparison; the completion
extension theorem gives its actual strict map onto the prescribed ambient.

The older source-coordinate inclusion-germ route remains available as an
independent conditional interface. The source-data marking theorem below
requires no such inclusion germs. No
toric end bound, target-specific full-fiber marking or geometric chain is
asserted here. These native results use the positive-dimensional model.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville
open SmoothManifold

variable {k : ℕ} {M : Type} [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

namespace NativeLiouvillePresentation

/-- Smooth germs of the specified original native inclusion construct a
carrier-preserving presentation equivalence on actual open neighborhoods.
The same native source and its full primitive determine the compact map;
neither a comparison map nor its inverse is an input. -/
theorem exists_presentationComparison_of_inclusionGerms
    {α : Form k M 1} (P Q : NativeLiouvillePresentation α)
    (hi : IsLocallyExtendibleTargetMap (k := k)
      Q.domain.domain.extension Q.inclusion) :
    ∃ (U : TopologicalSpace.Opens P.domain.domain.extension.Point)
      (hU : P.domain.domain.carrier ⊆ U)
      (V : TopologicalSpace.Opens (P.domain.restrict U hU).domain.extension.Point)
      (hV : (P.domain.restrict U hU).domain.carrier ⊆ V)
      (W : TopologicalSpace.Opens Q.domain.domain.extension.Point)
      (hW : Q.domain.domain.carrier ⊆ W)
      (p : DomainPresentationEquiv
        ((P.domain.restrict U hU).restrict V hV).domain
        (Q.domain.restrict W hW).domain),
      (∀ x, p.extensionEquiv (((P.restrict U hU).restrict V hV).inclusion x) =
        (Q.restrict W hW).inclusion x) ∧
      ∀ z ∈ ((P.domain.restrict U hU).restrict V hV).domain.carrier,
        ((P.domain.restrict U hU).restrict V hV).domain.extension.pullback
          (Q.domain.restrict W hW).domain.extension p.extensionEquiv
          (Q.domain.restrict W hW).liouville.primitive z =
            ((P.domain.restrict U hU).restrict V hV).liouville.primitive z := by
  obtain ⟨U, hU, J, hJ, _, _⟩ :=
    P.exists_inclusionEmbedding_into_specified_manifold
      Q.domain.domain.extension Q.domain.liouville.primitive Q.inclusion hi
      Q.embedding.injective (fun x => (Q.tangent_bijective x).1)
      (congrFun Q.primitive)
  let P₀ := P.restrict U hU
  obtain ⟨V, hV, W, e, _, he⟩ :=
    P₀.domain.domain.extension.exists_smoothEquiv_neighborhood Q.domain.domain.extension
      P₀.domain.domain.carrier P₀.domain.domain.compact J.map univ isOpen_univ
      (subset_univ _) J.map.contMDiff.contMDiffOn
      (fun _ _ _ _ h => J.embedding.injective h) (fun z _ => J.immersion z)
  have hW : Q.domain.domain.carrier ⊆ W := by
    intro z hz
    rw [← Q.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    let y : V := ⟨P₀.inclusion x, hV (P₀.carrier_range ▸ mem_range_self x)⟩
    have hy : (e y).val = Q.inclusion x := (he y).trans (hJ x)
    exact hy ▸ (e y).property
  let P₁ := P₀.restrict V hV
  let Q₁ := Q.restrict W hW
  have hsquare (x : M) : e (P₁.inclusion x) = Q₁.inclusion x :=
    Subtype.ext ((he _).trans (hJ x))
  have hcarrier : e '' P₁.domain.domain.carrier = Q₁.domain.domain.carrier := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← P₁.carrier_range] at hy
      obtain ⟨x, rfl⟩ := hy
      rw [hsquare]
      exact Q₁.carrier_range ▸ mem_range_self x
    · intro hz
      rw [← Q₁.carrier_range] at hz
      obtain ⟨x, rfl⟩ := hz
      exact ⟨P₁.inclusion x, P₁.carrier_range ▸ mem_range_self x, hsquare x⟩
  obtain ⟨b, hb⟩ := P₁.domain.domain.exists_boundaryEquiv_of_extensionEquiv
    Q₁.domain.domain e hcarrier
  let p : DomainPresentationEquiv P₁.domain.domain Q₁.domain.domain :=
    { extensionEquiv := e, carrier := hcarrier, boundaryEquiv := b, boundary_square := hb }
  refine ⟨U, hU, V, hV, W, hW, p, hsquare, ?_⟩
  intro z hz
  change z ∈ P₁.domain.domain.carrier at hz
  rw [← P₁.carrier_range] at hz
  obtain ⟨x, rfl⟩ := hz
  exact pullback_eq_of_native_comp_on_presentation P₁.domain.domain.extension
    Q₁.domain.domain.extension P₁.inclusion P₁.smooth_inclusion
    (fun x => (P₁.tangent_bijective x).2) e e.contMDiff Q₁.inclusion hsquare
    Q₁.domain.liouville.primitive P₁.domain.liouville.primitive α
    (congrFun P₁.primitive) (congrFun Q₁.primitive) x

/-- The constructed compact comparison extends onto the independently
prescribed completion. The original native inclusion, its inverse compact
formula, the actual boundary sections, and all real-radius end trajectories
are retained. Primitive preservation derives the actual flow transport. -/
theorem exists_strictCompletionComparison_of_inclusionGerms
    {α : Form k M 1} (P Q : NativeLiouvillePresentation α)
    (hi : IsLocallyExtendibleTargetMap (k := k)
      Q.domain.domain.extension Q.inclusion)
    (C : Completion P.domain) (K : Completion Q.domain) :
    ∃ (e : C.ambient.manifold.SmoothEquiv K.ambient.manifold)
      (b : P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary),
      C.ambient.manifold.pullback K.ambient.manifold e K.ambient.primitive =
        C.ambient.primitive ∧
      (∀ x, e (C.inclusion.map (P.inclusion x)) = K.inclusion.map (Q.inclusion x)) ∧
      (∀ x, e.symm (K.inclusion.map (Q.inclusion x)) = C.inclusion.map (P.inclusion x)) ∧
      (∀ x, e (C.inclusion.map (P.domain.domain.boundaryInclusion.map x)) =
        K.inclusion.map (Q.domain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, e (C.endMap (x, r)) = K.endMap (b x, r)) ∧
      ∀ z t, e (C.ambient.completeFlow.flow t z) = K.ambient.completeFlow.flow t (e z) := by
  obtain ⟨U, hU, V, hV, W, hW, p, hsquare, hp⟩ :=
    P.exists_presentationComparison_of_inclusionGerms Q hi
  let P₁ := (P.restrict U hU).restrict V hV
  let C₁ := (C.restrict U hU).restrict V hV
  let K₁ := K.restrict W hW
  obtain ⟨q, hq⟩ := C₁.exists_scaledPresentation_of_compact_primitive K₁ p
    1 (by norm_num) (by simpa only [one_smul] using hp)
  have hprimitive : C.ambient.manifold.pullback K.ambient.manifold q.equiv
      K.ambient.primitive = C.ambient.primitive := by
    simpa only [one_smul] using hq
  have hnative (x : M) :
      q.equiv (C.inclusion.map (P.inclusion x)) = K.inclusion.map (Q.inclusion x) := by
    have hs := q.compact_square (P₁.inclusion x)
      (P₁.carrier_range ▸ mem_range_self x)
    rw [hsquare] at hs
    exact hs
  have hboundary (x : P.domain.domain.boundary.Point) :
      q.equiv (C.inclusion.map (P.domain.domain.boundaryInclusion.map x)) =
        K.inclusion.map (Q.domain.domain.boundaryInclusion.map (p.boundaryEquiv x)) := by
    have hs := q.end_square x 0 (le_refl 0)
    change q.equiv (C.endMap (x, 0)) = K.endMap (p.boundaryEquiv x, 0) at hs
    rwa [C.endMap_zero, K.endMap_zero] at hs
  have hflow := C.ambient.map_flow K.ambient q.equiv hprimitive
  refine ⟨q.equiv, p.boundaryEquiv, hprimitive, hnative, ?_, hboundary, ?_, hflow⟩
  · intro x
    exact (congrArg q.equiv.symm (hnative x)).symm.trans (q.equiv.symm_apply_apply _)
  · intro x r
    rw [C.end_flow, K.end_flow, hflow, hboundary]

/-- The map onto the prescribed ambient is an actual inclusion marking.
Its compact inclusion is the specified original native inclusion expressed
on the source carrier, and the flow equation follows from strictness. -/
theorem exists_inclusionMarking_of_inclusionGerms
    {α : Form k M 1} (P Q : NativeLiouvillePresentation α)
    (hi : IsLocallyExtendibleTargetMap (k := k)
      Q.domain.domain.extension Q.inclusion)
    (C : Completion P.domain) (K : Completion Q.domain) :
    Nonempty (InclusionMarking C K.ambient
      (fun x => K.inclusion.map (Q.inclusion (P.carrierEquiv.symm x)))) := by
  obtain ⟨e, _, hp, hsquare, _, _, _, hflow⟩ :=
    P.exists_strictCompletionComparison_of_inclusionGerms Q hi C K
  refine ⟨{ equiv := e, primitive := hp, inclusion := ?_, flow_induced := ?_ }⟩
  · intro x
    have hx : P.inclusion (P.carrierEquiv.symm x) = x.val :=
      (P.carrier_square _).symm.trans
        (congrArg Subtype.val (P.carrierEquiv.apply_symm_apply x))
    simpa only [hx] using hsquare (P.carrierEquiv.symm x)
  · intro x r
    rw [C.end_flow, hflow]

section ActualCollar

variable [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

omit [CompactSpace M] in
/-- The compact comparison constructed from the actual native inward
collar extends strictly onto the prescribed completion. The same native
inclusion, every real-radius end trajectory and complete flow are retained. -/
theorem exists_strictCompletionComparison_of_inwardCollar
    {α : Form k M 1} (P Q : NativeLiouvillePresentation α)
    (C : Completion P.domain) (K : Completion Q.domain)
    (c : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hemb : Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => c p.val))
    (hzero : ∀ b, c (0, b) = b.val)
    (hode : ∀ b, IsMIntegralCurveOn (fun t => c (t, b))
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ)) :
    ∃ (e : C.ambient.manifold.SmoothEquiv K.ambient.manifold)
      (b : P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary),
      C.ambient.manifold.pullback K.ambient.manifold e K.ambient.primitive =
        C.ambient.primitive ∧
      (∀ x, e (C.inclusion.map (P.inclusion x)) = K.inclusion.map (Q.inclusion x)) ∧
      (∀ x, e.symm (K.inclusion.map (Q.inclusion x)) = C.inclusion.map (P.inclusion x)) ∧
      (∀ x, e (C.inclusion.map (P.domain.domain.boundaryInclusion.map x)) =
        K.inclusion.map (Q.domain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, e (C.endMap (x, r)) = K.endMap (b x, r)) ∧
      ∀ z t, e (C.ambient.completeFlow.flow t z) = K.ambient.completeFlow.flow t (e z) := by
  obtain ⟨U, hU, V, hV, W, hW, p, hsquare, hp⟩ :=
    P.exists_presentationComparison_of_inwardCollar Q C K c hδ hemb hzero hode
  let P₁ := (P.restrict U hU).restrict V hV
  let C₁ := (C.restrict U hU).restrict V hV
  let K₁ := K.restrict W hW
  obtain ⟨q, hq⟩ := C₁.exists_scaledPresentation_of_compact_primitive K₁ p
    1 (by norm_num) (by simpa only [one_smul] using hp)
  have hprimitive : C.ambient.manifold.pullback K.ambient.manifold q.equiv
      K.ambient.primitive = C.ambient.primitive := by
    simpa only [one_smul] using hq
  have hnative (x : M) :
      q.equiv (C.inclusion.map (P.inclusion x)) = K.inclusion.map (Q.inclusion x) := by
    have hs := q.compact_square (P₁.inclusion x)
      (P₁.carrier_range ▸ mem_range_self x)
    rw [hsquare] at hs
    exact hs
  have hboundary (x : P.domain.domain.boundary.Point) :
      q.equiv (C.inclusion.map (P.domain.domain.boundaryInclusion.map x)) =
        K.inclusion.map (Q.domain.domain.boundaryInclusion.map (p.boundaryEquiv x)) := by
    have hs := q.end_square x 0 (le_refl 0)
    change q.equiv (C.endMap (x, 0)) = K.endMap (p.boundaryEquiv x, 0) at hs
    rwa [C.endMap_zero, K.endMap_zero] at hs
  have hflow := C.ambient.map_flow K.ambient q.equiv hprimitive
  refine ⟨q.equiv, p.boundaryEquiv, hprimitive, hnative, ?_, hboundary, ?_, hflow⟩
  · intro x
    exact (congrArg q.equiv.symm (hnative x)).symm.trans (q.equiv.symm_apply_apply _)
  · intro x r
    rw [C.end_flow, K.end_flow, hflow, hboundary]

omit [CompactSpace M] in
/-- The collar-derived strict comparison is an actual marking of the
prescribed ambient and retains the original native inclusion. -/
theorem exists_inclusionMarking_of_inwardCollar
    {α : Form k M 1} (P Q : NativeLiouvillePresentation α)
    (C : Completion P.domain) (K : Completion Q.domain)
    (c : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hemb : Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => c p.val))
    (hzero : ∀ b, c (0, b) = b.val)
    (hode : ∀ b, IsMIntegralCurveOn (fun t => c (t, b))
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ)) :
    Nonempty (InclusionMarking C K.ambient
      (fun x => K.inclusion.map (Q.inclusion (P.carrierEquiv.symm x)))) := by
  obtain ⟨e, _, hp, hsquare, _, _, _, hflow⟩ :=
    P.exists_strictCompletionComparison_of_inwardCollar Q C K c hδ hemb hzero hode
  refine ⟨{ equiv := e, primitive := hp, inclusion := ?_, flow_induced := ?_ }⟩
  · intro x
    have hx : P.inclusion (P.carrierEquiv.symm x) = x.val :=
      (P.carrier_square _).symm.trans
        (congrArg Subtype.val (P.carrierEquiv.apply_symm_apply x))
    simpa only [hx] using hsquare (P.carrierEquiv.symm x)
  · intro x r
    rw [C.end_flow, hflow]

end ActualCollar

omit [CompactSpace M] in
/-- Strict completed maps retaining the same original native inclusion
are equal. Native carrier coverage gives compact agreement; strict flow
transport and compact/end coverage then give agreement everywhere. -/
theorem strictCompletionComparison_unique_on_native_inclusion
    {α : Form k M 1} (P Q : NativeLiouvillePresentation α)
    (C : Completion P.domain) (K : Completion Q.domain)
    (e e' : C.ambient.manifold.SmoothEquiv K.ambient.manifold)
    (hp : C.ambient.manifold.pullback K.ambient.manifold e K.ambient.primitive =
      C.ambient.primitive)
    (hp' : C.ambient.manifold.pullback K.ambient.manifold e' K.ambient.primitive =
      C.ambient.primitive)
    (hs : ∀ x, e (C.inclusion.map (P.inclusion x)) = K.inclusion.map (Q.inclusion x))
    (hs' : ∀ x, e' (C.inclusion.map (P.inclusion x)) = K.inclusion.map (Q.inclusion x)) :
    e = e' := by
  apply C.equiv_eq_of_scaled_primitive_on_compact K.ambient e e' 1 1
  · simpa only [one_smul] using hp
  · simpa only [one_smul] using hp'
  · intro z hz
    rw [← P.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    exact (hs x).trans (hs' x).symm

end NativeLiouvillePresentation

variable [T2Space M] [SecondCountableTopology M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Native primitive, symplecticity and outwardness construct the actual
half-infinite quotient, its completion and a native inward ODE collar.
The actual collar comparison produces a strict marking of that quotient
onto the prescribed completion of an independently specified presentation.
The quotient
ambient, primitive and identity extension inclusion are retained literally;
the marking takes every original point to its independently specified image.

This is the completion correspondence in `def:pair`, lines 142–158, and
`sec:lean`, lines 805–813. The prescribed completion is an independent
input; no across-boundary inclusion germs or comparison map are supplied. -/
theorem exists_nativeCompletionMarking_into_prescribed_completion
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
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (Q : NativeLiouvillePresentation α)
    (K : Completion Q.domain) :
    ∃ (P : NativeLiouvillePresentation α) (C : Completion P.domain)
      (q : InclusionMarking C K.ambient
        (fun x => K.inclusion.map (Q.inclusion (P.carrierEquiv.symm x)))),
      C.ambient.manifold = P.domain.domain.extension ∧
      HEq C.ambient.primitive P.domain.liouville.primitive ∧
      (∀ z : P.domain.domain.extension.Point, HEq (C.inclusion.map z) z) ∧
      (fun x => (C.ambient.primitive (C.inclusion.map (P.inclusion x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (C.inclusion.map ∘ P.inclusion) x)) = α ∧
      ∀ x, q.equiv (C.inclusion.map (P.inclusion x)) = K.inclusion.map (Q.inclusion x) := by
  obtain ⟨P, C, hambient, hprimitive, hinclusion, hnative⟩ :=
    exists_nativeLiouvillePresentation_with_completion α hα hnd hout
  obtain ⟨c, δ, hδ, _, hemb, hzero, hode, _, _⟩ :=
    exists_uniform_collar_of_localDefiningFunction_outward α hα hnd hout
  obtain ⟨q⟩ := P.exists_inclusionMarking_of_inwardCollar Q C K c hδ hemb hzero hode
  refine ⟨P, C, q, hambient, hprimitive, hinclusion, hnative, ?_⟩
  intro x
  have hq := q.inclusion (P.carrierEquiv x)
  simpa only [P.carrier_square, P.carrierEquiv.symm_apply_apply] using hq

end FsFltz.Geometry.IntrinsicLiouville
