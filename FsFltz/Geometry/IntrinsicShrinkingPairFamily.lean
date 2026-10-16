import FsFltz.Geometry.IntrinsicShrinkingPairMotion
import FsFltz.Geometry.WitnessInterpolation
import FsFltz.Geometry.PairRestriction

/-!
# The actual completed intrinsic shrinking pair family

Source: `geometric-part-fsf-proof.tex`, `lem:shrinking`, lines 470–488,
and `subsec:junction`, lines 1876–1892. The ambient tuple, positive
witness and completed ambient are fixed. Ribbon embeddings use the actual
negative intrinsic flow; both primitive scaling and joint smoothness are
proved by the preceding producers. Only the open ribbon extension is
restricted, and that change of presentation is recorded separately.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace WitnessedPair

variable {n : ℕ} (P : WitnessedPair n)
    (U : TopologicalSpace.Opens P.ribbonDomain.domain.extension.Point)
    (hU : P.ribbonDomain.domain.carrier ⊆ U)

/-- Restrict only the ribbon's open extension. Its compact carrier, primitive,
complete flow and ambient boundary image are retained. -/
abbrev restrictRibbon : WitnessedPair n where
  ambientDomain := P.ambientDomain
  ribbonDomain := P.ribbonDomain.restrict U hU
  ribbonEmbedding := P.ribbonEmbedding.comp (P.ribbonDomain.domain.extension.restrictInclusion U)
  witness := P.witness
  smooth_witness := P.smooth_witness
  positive_witness := P.positive_witness
  ribbon_primitive := by
    intro x hx
    exact (P.ribbonDomain.domain.extension.pullback_comp_restrict_val
      P.ambientDomain.domain.boundary U P.ribbonEmbedding.map _ x).trans
      ((P.ribbon_primitive x.val hx).trans
        (P.ribbonDomain.liouville.restrict_primitive U hU x).symm)
  ambientCompletion := P.ambientCompletion
  ribbonCompletion := P.ribbonCompletion.restrict U hU

variable (T : ℝ) (hT : 0 ≤ T) (J : TopologicalSpace.Opens ℝ)
    (hJ : parameterInterval ⊆ J)
    (hdefined : ∀ t ∈ J, ∀ x ∈ U,
      P.ribbonCompletion.ambient.completeFlow.flow (-(T * t))
        (P.ribbonCompletion.inclusion.map x) ∈ P.ribbonCompletion.inclusionImage)

/-- One member of the intrinsic shrinking deformation, with its specified
scaled completion and the same ambient and witness. -/
def shrinkingPair (t : Parameter) : WitnessedPair n := by
  let R := P.ribbonDomain.restrict U hU
  let c := Real.exp (-(T * t.val))
  let q := P.ribbonCompletion.shrinkingEmbedding T J U hJ hdefined t
  refine
    { ambientDomain := P.ambientDomain
      ribbonDomain := ⟨R.domain, R.liouville.positiveScale c (Real.exp_pos _)⟩
      ribbonEmbedding := P.ribbonEmbedding.comp q
      witness := P.witness
      smooth_witness := P.smooth_witness
      positive_witness := P.positive_witness
      ribbon_primitive := ?_
      ambientCompletion := P.ambientCompletion
      ribbonCompletion := (P.ribbonCompletion.restrict U hU).positiveScale c (Real.exp_pos _) }
  intro x hx
  change R.domain.extension.pullback P.ambientDomain.domain.boundary
    (P.ribbonEmbedding.map ∘ q.map) (fun y => P.witness y •
      P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive y) x =
        c • R.liouville.primitive x
  rw [R.domain.extension.pullback_comp P.ribbonDomain.domain.extension
    P.ambientDomain.domain.boundary (q.map.contMDiff.mdifferentiable (by simp))
    (P.ribbonEmbedding.map.contMDiff.mdifferentiable (by simp))]
  have hm : q.map x ∈ P.ribbonDomain.domain.carrier :=
    P.ribbonCompletion.shrinkingLift_mem_carrier T hT t x.val hx
  change ((P.ribbonDomain.domain.extension.pullback P.ambientDomain.domain.boundary
    P.ribbonEmbedding.map (fun y => P.witness y •
      P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive y)
      (q.map x)).compContinuousLinearMap (mfderiv 𝓘(ℝ, Model (2 * n - 2))
        𝓘(ℝ, Model (2 * n - 2)) q.map x)) = c • R.liouville.primitive x
  rw [P.ribbon_primitive (q.map x) hm]
  rw [show R.liouville.primitive x = P.ribbonDomain.liouville.primitive x.val from
    P.ribbonDomain.liouville.restrict_primitive U hU x]
  exact P.ribbonCompletion.pullback_shrinkingEmbedding T hT J U hJ hdefined t x hx

/-- The intrinsic shrinking family has identity compact and completed
presentations; the completed ribbon primitive varies by the same explicit
constant as the compact primitive. -/
def shrinkingDeformation : PairDeformation n := by
  let Q := P.shrinkingPair U hU T hT J hJ hdefined
  let R := P.ribbonDomain.restrict U hU
  let a := DomainPresentationEquiv.refl P.ambientDomain.domain
  let f := DomainPresentationEquiv.refl R.domain
  let ac : CompletionPresentationEquiv P.ambientCompletion P.ambientCompletion a :=
    { equiv := Diffeomorph.refl _ _ ∞
      compact_square := fun _ _ => rfl
      end_square := fun _ _ _ => rfl }
  let fc (t : Parameter) : CompletionPresentationEquiv
      (Q parameterZero).ribbonCompletion (Q t).ribbonCompletion f :=
    { equiv := Diffeomorph.refl _ _ ∞
      compact_square := fun _ _ => rfl
      end_square := fun _ _ _ => rfl }
  have hj : R.domain.extension.IsSmoothIntervalMapFamily P.ambientDomain.domain.boundary
      (fun t x => P.ribbonEmbedding.map
        (P.ribbonCompletion.shrinkingLift T t.val x.val)) := by
    obtain ⟨q, ⟨V, hV, hcover, hs⟩, he⟩ :=
      P.ribbonCompletion.isSmoothInterval_shrinkingLift T J U hJ hdefined
    refine ⟨fun t x => P.ribbonEmbedding.map (q t x),
      ⟨V, hV, hcover, P.ribbonEmbedding.map.contMDiff.comp_contMDiffOn hs⟩, ?_⟩
    intro t
    funext x
    exact congrArg P.ribbonEmbedding.map (congrFun (he t) x)
  have hb : P.ambientDomain.domain.boundary.IsSmoothIntervalScalarFamily (fun _ => P.witness) :=
    ⟨fun _ => P.witness, P.ambientDomain.domain.boundary.isSmoothScalarFamily_of_contMDiff
      (P.smooth_witness.comp contMDiff_snd), fun _ => rfl⟩
  refine
    { pair := Q
      ambientPresentation := fun _ => a
      ribbonPresentation := fun _ => f
      ambientCompletionPresentation := fun _ => ac
      ribbonCompletionPresentation := fc
      ambientPrimitive_smooth := ?_
      ribbonPrimitive_smooth := ?_
      ambientField_smooth := ?_
      ribbonField_smooth := ?_
      ribbonEmbedding_smooth := hj
      witness_smooth := hb
      completedAmbientPrimitive_smooth := ?_
      completedRibbonPrimitive_smooth := ?_
      completedAmbientField_smooth := ?_
      completedRibbonField_smooth := ?_ }
  · change P.ambientDomain.domain.extension.IsSmoothIntervalFormFamily
      (fun _ => P.ambientDomain.domain.extension.pullback _ id P.ambientDomain.liouville.primitive)
    rw [P.ambientDomain.domain.extension.pullback_id]
    exact P.ambientDomain.domain.extension.isSmoothIntervalFormFamily_constant _
      P.ambientDomain.liouville.smooth_primitive
  · change R.domain.extension.IsSmoothIntervalFormFamily
      (fun t => R.domain.extension.pullback _ id
        (Real.exp (-(T * t.val)) • R.liouville.primitive))
    simp_rw [R.domain.extension.pullback_id]
    exact R.domain.extension.isSmoothIntervalFormFamily_expScale _ R.liouville.smooth_primitive T
  · change P.ambientDomain.domain.extension.IsSmoothIntervalVectorFieldFamily
      (fun _ => P.ambientDomain.domain.extension.pullbackVectorField _
        (Diffeomorph.refl _ _ ∞) P.ambientDomain.liouville.field)
    rw [P.ambientDomain.domain.extension.pullbackVectorField_refl]
    exact P.ambientDomain.domain.extension.isSmoothIntervalVectorFieldFamily_constant _
      P.ambientDomain.liouville.smooth_field
  · change R.domain.extension.IsSmoothIntervalVectorFieldFamily
      (fun _ => R.domain.extension.pullbackVectorField _
        (Diffeomorph.refl _ _ ∞) R.liouville.field)
    rw [R.domain.extension.pullbackVectorField_refl]
    exact R.domain.extension.isSmoothIntervalVectorFieldFamily_constant _ R.liouville.smooth_field
  · change P.ambientManifold.IsSmoothIntervalFormFamily
      (fun _ => P.ambientManifold.pullback _ id P.ambientCompletion.ambient.primitive)
    rw [P.ambientManifold.pullback_id]
    exact P.ambientManifold.isSmoothIntervalFormFamily_constant _ P.ambientCompletion.ambient.smooth_primitive
  · change P.ribbonCompletion.ambient.manifold.IsSmoothIntervalFormFamily
      (fun t => P.ribbonCompletion.ambient.manifold.pullback _ id
        (Real.exp (-(T * t.val)) • P.ribbonCompletion.ambient.primitive))
    simp_rw [P.ribbonCompletion.ambient.manifold.pullback_id]
    exact P.ribbonCompletion.ambient.manifold.isSmoothIntervalFormFamily_expScale _
      P.ribbonCompletion.ambient.smooth_primitive T
  · change P.ambientManifold.IsSmoothIntervalVectorFieldFamily
      (fun _ => P.ambientManifold.pullbackVectorField _
        (Diffeomorph.refl _ _ ∞) P.ambientCompletion.ambient.field)
    rw [P.ambientManifold.pullbackVectorField_refl]
    exact P.ambientManifold.isSmoothIntervalVectorFieldFamily_constant _ P.ambientCompletion.ambient.smooth_field
  · change P.ribbonCompletion.ambient.manifold.IsSmoothIntervalVectorFieldFamily
      (fun _ => P.ribbonCompletion.ambient.manifold.pullbackVectorField _
        (Diffeomorph.refl _ _ ∞) P.ribbonCompletion.ambient.field)
    rw [P.ribbonCompletion.ambient.manifold.pullbackVectorField_refl]
    exact P.ribbonCompletion.ambient.manifold.isSmoothIntervalVectorFieldFamily_constant _
      P.ribbonCompletion.ambient.smooth_field

/-- This very shrinking deformation transports every ambient Maslov datum
constantly, since its ambient and all completed ambient presentations are fixed. -/
def gradedShrinkingDeformation (datum : P.Maslov) :
    GradedPairDeformation (P.shrinkingDeformation U hU T hT J hJ hdefined) datum datum where
  etaExtension := fun _ => P.ambientSymplecticForm
  eta_agrees := by
    intro t
    change P.ambientSymplecticForm = P.ambientManifold.exteriorDerivative
      (P.ambientManifold.pullback _ id P.ambientCompletion.ambient.primitive)
    rw [P.ambientManifold.pullback_id]
    rfl
  family := (MaslovHomotopy.refl datum).family
  sourceJ := (pullbackAlmostComplex_refl P.ambientManifold datum.J).symm
  targetJ := (pullbackAlmostComplex_refl P.ambientManifold datum.J).symm
  sourceTensor := (pullbackSquaredTensor_refl P.ambientManifold datum.tensor).symm
  targetTensor := (pullbackSquaredTensor_refl P.ambientManifold datum.tensor).symm

/-- The embedding formula retains the entire ribbon pointwise, rather than
only giving an equality of its embedded cores. -/
theorem shrinkingDeformation_embedding (t : Parameter) (x : U) :
    ((P.shrinkingDeformation U hU T hT J hJ hdefined).pair t).ribbonEmbedding.map x =
      P.ribbonEmbedding.map (P.ribbonCompletion.shrinkingLift T t.val x.val) := rfl

/-- The fixed-source primitive is exactly the constant predicted by
intrinsic Liouville flow, on every point of its open extension. -/
theorem shrinkingDeformation_primitive (t : Parameter) (x : U) :
    ((P.shrinkingDeformation U hU T hT J hJ hdefined).pair t).ribbonDomain.liouville.primitive x =
      Real.exp (-(T * t.val)) • P.ribbonDomain.liouville.primitive x.val := by
  exact congrArg (fun η => Real.exp (-(T * t.val)) • η)
    (P.ribbonDomain.liouville.restrict_primitive U hU x)

/-- The whole moving ribbon stays inside the original compact ribbon,
so it stays inside the same fixed boundary face. -/
theorem shrinkingDeformation_ribbon_subset (t : Parameter) :
    ((P.shrinkingDeformation U hU T hT J hJ hdefined).pair t).ribbonEmbedding.map ''
      ((P.shrinkingDeformation U hU T hT J hJ hdefined).pair t).ribbonDomain.domain.carrier ⊆
        P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨_, P.ribbonCompletion.shrinkingLift_mem_carrier T hT t x.val hx, rfl⟩

/-- The full embedded core is preserved by this very moving family. Both
directions use the native completed flow and the whole all-forward-time core. -/
theorem shrinkingDeformation_embeddedCore (t : Parameter) :
    ((P.shrinkingDeformation U hU T hT J hJ hdefined).pair t).embeddedCore = P.embeddedCore := by
  let C := P.ribbonCompletion
  let F := C.ambient.completeFlow.flow
  let a := T * t.val
  have ha : 0 ≤ a := mul_nonneg hT t.property.1
  change (fun x : U => P.ribbonEmbedding.map (C.shrinkingLift T t.val x.val)) ''
    ((C.restrict U hU).positiveScale (Real.exp (-a)) (Real.exp_pos _)).core =
      P.ribbonEmbedding.map '' C.core
  rw [Completion.positiveScale_core, C.core_restrict U hU]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let q := C.shrinkingLift T t.val x.val
    have hi := C.inclusion_shrinkingLift T t.val x.val
      (hdefined t.val (hJ t.property) x.val x.property)
    change C.inclusion.map q = F (-a) (C.inclusion.map x.val) at hi
    refine ⟨q, ⟨C.shrinkingLift_mem_carrier T hT t x.val hx.1, ?_⟩, rfl⟩
    intro s hs
    rw [hi]
    have hcomm : F s (F (-a) (C.inclusion.map x.val)) =
        F (-a) (F s (C.inclusion.map x.val)) := by
      rw [← F.map_add, ← F.map_add, add_comm]
    rw [hcomm]
    exact C.negative_flow_mem (hx.2 s hs) ha
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hi⟩ := hy.2 a ha
    have hxcore : x ∈ C.core := by
      refine ⟨hx, ?_⟩
      intro s hs
      rw [hi, ← F.map_add]
      exact hy.2 (s + a) (add_nonneg hs ha)
    let xu : U := ⟨x, hU hx⟩
    refine ⟨xu, hxcore, ?_⟩
    apply congrArg P.ribbonEmbedding.map
    apply C.inclusion.embedding.injective
    rw [C.inclusion_shrinkingLift T t.val x
      (hdefined t.val (hJ t.property) x (hU hx)), hi]
    change F (-a) (F a (C.inclusion.map y)) = C.inclusion.map y
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]

end WitnessedPair
end FsFltz.Geometry
