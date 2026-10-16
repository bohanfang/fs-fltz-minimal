import FsFltz.Geometry.TailoringIntrinsicShrinking

/-!
# The preserved full-fiber marking of the concrete shrinking pair

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1881–1889.
We retain the fixed ribbon carrier and its scaled primitive throughout the
subsequent junction. The optional relabeling onto its image domain is omitted;
subsequent spatial maps are precomposed with this actual negative-flow map.
The complete intrinsic fiber and potential are the original marked ones.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Analytic data for a constructed shrinking family, exposing its actual
finite time and common open extension to the next geometric consumer. -/
structure IntrinsicShrinkingData {n : ℕ} (P : WitnessedPair n) where
  time : ℝ
  nonnegative_time : 0 ≤ time
  interval : TopologicalSpace.Opens ℝ
  extension : TopologicalSpace.Opens P.ribbonDomain.domain.extension.Point
  contains_interval : parameterInterval ⊆ interval
  contains_carrier : P.ribbonDomain.domain.carrier ⊆ extension
  flow_defined : ∀ t ∈ interval, ∀ x ∈ extension,
    P.ribbonCompletion.ambient.completeFlow.flow (-(time * t))
      (P.ribbonCompletion.inclusion.map x) ∈ P.ribbonCompletion.inclusionImage

namespace IntrinsicShrinkingData
variable {n : ℕ} {P : WitnessedPair n} (S : IntrinsicShrinkingData P)

abbrev deformation : PairDeformation n :=
  P.shrinkingDeformation S.extension S.contains_carrier S.time S.nonnegative_time
    S.interval S.contains_interval S.flow_defined

abbrev pair (t : Parameter) : WitnessedPair n := S.deformation.pair t

abbrev lift (t : Parameter) :=
  P.ribbonCompletion.shrinkingEmbedding S.time S.interval S.extension
    S.contains_interval S.flow_defined t

abbrev ribbonAmbientEmbedding
    (R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)) (t : Parameter) :
    (S.pair t).ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n) := R.comp (S.lift t)

abbrev chain (x₀ : S.extension) : ComparisonChain P S.deformation.target :=
  P.shrinkingChain S.extension S.contains_carrier x₀ S.time S.nonnegative_time
    S.interval S.contains_interval S.flow_defined

def grading (x₀ : S.extension) (datum : P.Maslov) :
    GradedComparisonChain P (S.chain x₀) datum datum :=
  P.gradedShrinkingChain S.extension S.contains_carrier x₀ S.time S.nonnegative_time
    S.interval S.contains_interval S.flow_defined datum

@[simp] theorem pair_ambient (t : Parameter) : (S.pair t).ambientDomain = P.ambientDomain := rfl

@[simp] theorem pair_witness (t : Parameter) : (S.pair t).witness = P.witness := rfl

theorem pair_ribbonEmbedding (t : Parameter) :
    (S.pair t).ribbonEmbedding = P.ribbonEmbedding.comp (S.lift t) := rfl

theorem pair_primitive (t : Parameter) (x : S.extension) :
    (S.pair t).ribbonDomain.liouville.primitive x =
      Real.exp (-(S.time * t.val)) • P.ribbonDomain.liouville.primitive x.val :=
  P.shrinkingDeformation_primitive S.extension S.contains_carrier S.time S.nonnegative_time
    S.interval S.contains_interval S.flow_defined t x

theorem pair_ribbon_nonempty (hP : P.ribbonDomain.domain.carrier.Nonempty) (t : Parameter) :
    (S.pair t).ribbonDomain.domain.carrier.Nonempty := by
  obtain ⟨x, hx⟩ := hP
  exact ⟨⟨x, S.contains_carrier hx⟩, hx⟩

theorem ribbonAmbientEmbedding_eq
    (A : P.ambientDomain.domain.boundary.SmoothEmbedding (lgManifold n)) (t : Parameter) :
    S.ribbonAmbientEmbedding (A.comp P.ribbonEmbedding) t = A.comp (S.pair t).ribbonEmbedding := rfl

variable {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P R f value φ)

/-- The actual negative-time map followed by the original full-fiber marking.
Its source is the concrete scaled completion; its target is the same native H. -/
def completionEquiv (t : Parameter) :
    (S.pair t).ribbonCompletion.ambient.manifold.SmoothEquiv M.manifold :=
  (P.ribbonCompletion.ambient.completeFlow.timeDiffeomorph (-(S.time * t.val))).trans M.marking.equiv

theorem completionEquiv_apply (t : Parameter)
    (x : P.ribbonCompletion.ambient.manifold.Point) :
    S.completionEquiv M t x = M.marking.equiv
      (P.ribbonCompletion.ambient.completeFlow.flow (-(S.time * t.val)) x) := rfl

/-- Primitive preservation is derived from the actual full completed flow,
and is exactly the primitive of the concrete scaled specified completion. -/
theorem completionEquiv_primitive (t : Parameter) :
    (S.pair t).ribbonCompletion.ambient.manifold.pullback M.manifold
      (S.completionEquiv M t) M.primitive.toCompleteLiouvilleManifold.primitive =
        (S.pair t).ribbonCompletion.ambient.primitive := by
  let C := P.ribbonCompletion
  let q := C.ambient.completeFlow.timeDiffeomorph (-(S.time * t.val))
  have hp : C.ambient.manifold.pullback M.manifold M.marking.equiv
      M.primitive.toCompleteLiouvilleManifold.primitive = C.ambient.primitive := M.marking.primitive
  change C.ambient.manifold.pullback M.manifold (M.marking.equiv ∘ q)
    M.primitive.toCompleteLiouvilleManifold.primitive =
      Real.exp (-(S.time * t.val)) • C.ambient.primitive
  rw [C.ambient.manifold.pullback_comp C.ambient.manifold M.manifold
    (q.contMDiff.mdifferentiable (by simp))
    (M.marking.equiv.contMDiff.mdifferentiable (by simp)), hp]
  exact C.ambient.pullback_timeDiffeomorph _

private def equivEmbedding {d : ℕ} {X Y : SmoothManifold d} (e : X.SmoothEquiv Y) :
    X.SmoothEmbedding Y where
  map := ⟨e, e.contMDiff⟩
  embedding := e.toHomeomorph.isEmbedding
  immersion := fun x => (e.mfderivToContinuousLinearEquiv (by simp) x).injective

/-- The actual whole open ribbon extension embedded into the same native
full fiber. It is available for precomposition with every later hitting map. -/
def fiberEmbedding (t : Parameter) :
    (S.pair t).ribbonDomain.domain.extension.SmoothEmbedding M.manifold :=
  (equivEmbedding (S.completionEquiv M t)).comp
    (P.ribbonCompletion.inclusion.comp
      (P.ribbonDomain.domain.extension.restrictInclusion S.extension))

theorem fiberEmbedding_apply (t : Parameter) (x : S.extension) :
    (S.fiberEmbedding M t).map x = M.marking.equiv
      (P.ribbonCompletion.ambient.completeFlow.flow (-(S.time * t.val))
        (P.ribbonCompletion.inclusion.map x.val)) := rfl

/-- On the whole compact ribbon the new native fiber inclusion is the
original marked inclusion at the actual negative-flow lift. -/
theorem fiberEmbedding_compact (t : Parameter) (x : S.extension)
    (hx : x.val ∈ P.ribbonDomain.domain.carrier) :
    M.embedding.map ((S.fiberEmbedding M t).map x) =
      (S.ribbonAmbientEmbedding R t).map x := by
  have hq := P.ribbonCompletion.shrinkingLift_mem_carrier S.time S.nonnegative_time t x.val hx
  have hi := P.ribbonCompletion.inclusion_shrinkingLift S.time t.val x.val
    (S.flow_defined t.val (S.contains_interval t.property) x.val x.property)
  rw [S.fiberEmbedding_apply M, ← hi,
    M.marking.inclusion (⟨_, hq⟩ : P.ribbonDomain.domain.Point)]
  exact M.compact_square ⟨_, hq⟩

/-- A constructed marking of the concrete moving ribbon onto the original
entire native fiber, preserving its original literal potential primitive. -/
def fullFiberMarking (t : Parameter) :
    FullFiberRibbonMarking (S.pair t) (S.ribbonAmbientEmbedding R t) f value φ where
  manifold := M.manifold
  embedding := M.embedding
  primitive := M.primitive
  inclusion := fun x => (S.fiberEmbedding M t).map x.val
  image := M.image
  compact_square := fun x => S.fiberEmbedding_compact M t x.val x.property
  marking :=
    { equiv := S.completionEquiv M t
      primitive := S.completionEquiv_primitive M t
      inclusion := fun _ => rfl
      flow_induced := by
        intro x r
        rw [(S.pair t).ribbonCompletion.end_flow]
        exact (S.pair t).ribbonCompletion.ambient.map_flow
          M.primitive.toCompleteLiouvilleManifold (S.completionEquiv M t)
          (S.completionEquiv_primitive M t) _ r }

/-- The native complete fiber and its primitive are retained literally. -/
@[simp] theorem fullFiberMarking_manifold (t : Parameter) :
    (S.fullFiberMarking M t).manifold = M.manifold := rfl

@[simp] theorem fullFiberMarking_embedding (t : Parameter) :
    (S.fullFiberMarking M t).embedding = M.embedding := rfl

@[simp] theorem fullFiberMarking_primitive (t : Parameter) :
    (S.fullFiberMarking M t).primitive = M.primitive := rfl

/-- The actual native fiber pullback supplies the compact primitive needed
by the next hitting family, including the complete constant scaling. -/
theorem fiberEmbedding_primitive (t : Parameter) (x : S.extension)
    (hx : x.val ∈ P.ribbonDomain.domain.carrier) :
    (S.pair t).ribbonDomain.domain.extension.pullback M.manifold (S.fiberEmbedding M t).map
      M.primitive.toCompleteLiouvilleManifold.primitive x =
        (S.pair t).ribbonDomain.liouville.primitive x := by
  let C := (S.pair t).ribbonCompletion
  have hp : C.ambient.manifold.pullback M.manifold (S.completionEquiv M t)
      M.primitive.toCompleteLiouvilleManifold.primitive = C.ambient.primitive :=
    S.completionEquiv_primitive M t
  change (S.pair t).ribbonDomain.domain.extension.pullback M.manifold
    (S.completionEquiv M t ∘ C.inclusion.map) M.primitive.toCompleteLiouvilleManifold.primitive x = _
  rw [(S.pair t).ribbonDomain.domain.extension.pullback_comp C.ambient.manifold M.manifold
    (C.inclusion.map.contMDiff.mdifferentiable (by simp))
    ((S.completionEquiv M t).contMDiff.mdifferentiable (by simp)), hp]
  exact C.primitive_on_domain x hx

theorem fiberEmbedding_primitive_scaled (t : Parameter) (x : S.extension)
    (hx : x.val ∈ P.ribbonDomain.domain.carrier) :
    (S.pair t).ribbonDomain.domain.extension.pullback M.manifold (S.fiberEmbedding M t).map
      M.primitive.toCompleteLiouvilleManifold.primitive x =
        Real.exp (-(S.time * t.val)) • P.ribbonDomain.liouville.primitive x.val :=
  (S.fiberEmbedding_primitive M t x hx).trans (S.pair_primitive t x)

include M in
/-- Keeping the same actual full fiber and primitive preserves its entire
embedded full core in the concrete moving ambient-ribbon presentation. -/
theorem ribbonAmbientEmbedding_core (t : Parameter) :
    (S.ribbonAmbientEmbedding R t).map '' (S.pair t).ribbonCompletion.core =
      R.map '' P.ribbonCompletion.core :=
  (S.fullFiberMarking M t).image_core_eq.trans M.image_core_eq.symm

end IntrinsicShrinkingData

/-- Shrink the same retained ribbon directly into an open neighborhood in its
actual native full fiber. The whole open endpoint extension lies there. -/
theorem FullFiberRibbonMarking.exists_shrinkingData_into_fiber {n : ℕ} {P : WitnessedPair n}
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P R f value φ)
    (W : TopologicalSpace.Opens M.manifold.Point)
    (hcore : M.embedding.map ⁻¹' (R.map '' P.ribbonCompletion.core) ⊆ W) :
    ∃ S : IntrinsicShrinkingData P,
      ∀ x : S.extension,
        (S.fiberEmbedding M parameterOne).map x ∈ W := by
  let C := P.ribbonCompletion
  let F := C.ambient.completeFlow.flow
  let K := C.inclusion.map '' P.ribbonDomain.domain.carrier
  let g : C.ambient.manifold.Point → M.manifold.Point := M.marking.equiv
  have hg : Continuous g := M.marking.equiv.contMDiff.continuous
  have hK : IsCompact K := P.ribbonDomain.domain.compact.image C.inclusion.map.contMDiff.continuous
  have hneg : IsForwardInvariant F.reverse K := fun _ ht _ hx => C.negative_flow_mem hx ht
  have hC : FsFltz.flowCore F K ⊆ g ⁻¹' (W : Set M.manifold.Point) := by
    intro y hy
    rw [← C.image_core_eq_flowCore] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply hcore
    change M.embedding.map (M.marking.equiv (C.inclusion.map x)) ∈ R.map '' P.ribbonCompletion.core
    rw [M.marking.inclusion (⟨x, hx.1⟩ : P.ribbonDomain.domain.Point)]
    rw [M.compact_square ⟨x, hx.1⟩]
    exact ⟨x, hx, rfl⟩
  obtain ⟨T, hT, htime⟩ := FsFltz.exists_negative_image_subset F hK hneg
    (W.isOpen.preimage hg) hC
  obtain ⟨J, U₀, hJ, hU₀, hdefined⟩ := C.exists_shrinking_neighborhood T hT
  let k : P.ribbonDomain.domain.extension.Point → M.manifold.Point :=
    fun x => g (F (-T) (C.inclusion.map x))
  have hk : Continuous k := hg.comp ((F.continuous_toFun (-T)).comp C.inclusion.map.contMDiff.continuous)
  let V : TopologicalSpace.Opens P.ribbonDomain.domain.extension.Point :=
    ⟨k ⁻¹' (W : Set M.manifold.Point), W.isOpen.preimage hk⟩
  let U := U₀ ⊓ V
  have hU : P.ribbonDomain.domain.carrier ⊆ U := by
    intro x hx
    refine ⟨hU₀ hx, ?_⟩
    exact htime ⟨C.inclusion.map x, ⟨x, hx, rfl⟩, rfl⟩
  let S : IntrinsicShrinkingData P :=
    { time := T, nonnegative_time := hT, interval := J, extension := U
      contains_interval := hJ, contains_carrier := hU
      flow_defined := fun t ht x hx => hdefined t ht x hx.1 }
  refine ⟨S, ?_⟩
  intro x
  change g (F (-(T * parameterOne.val)) (C.inclusion.map x.val)) ∈ W
  simp only [parameterOne, mul_one]
  exact x.property.2

/-- Compactness selects a concrete finite shrinking family of this same
marked ribbon. Its entire open endpoint extension lies in the requested
neighborhood, so later hitting maps can be precomposed there. -/
theorem FullFiberRibbonMarking.exists_shrinkingData_into {n : ℕ} {P : WitnessedPair n}
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P R f value φ)
    (W : TopologicalSpace.Opens (LGSpace n))
    (hcore : R.map '' P.ribbonCompletion.core ⊆ (W : Set (LGSpace n))) :
    ∃ S : IntrinsicShrinkingData P,
      ∀ x : S.extension,
        M.embedding.map ((S.fiberEmbedding M parameterOne).map x) ∈ W := by
  let U : TopologicalSpace.Opens M.manifold.Point :=
    ⟨M.embedding.map ⁻¹' (W : Set (LGSpace n)),
      W.isOpen.preimage M.embedding.map.contMDiff.continuous⟩
  exact M.exists_shrinkingData_into_fiber U (fun _ hx => hcore hx)

/-- The native data selection also supplies a genuine source point for its
explicit localization and graded comparison, using the retained nonempty
ribbon rather than choosing a different pair or potential. -/
theorem FullFiberRibbonMarking.exists_marked_shrinkingData_into {n : ℕ} {P : WitnessedPair n}
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P R f value φ)
    (hP : P.ribbonDomain.domain.carrier.Nonempty)
    (W : TopologicalSpace.Opens (LGSpace n))
    (hcore : R.map '' P.ribbonCompletion.core ⊆ (W : Set (LGSpace n))) :
    ∃ (S : IntrinsicShrinkingData P) (x₀ : S.extension),
      (∀ x : S.extension, M.embedding.map ((S.fiberEmbedding M parameterOne).map x) ∈ W) ∧
      (∀ datum : P.Maslov, Nonempty (GradedComparisonChain P (S.chain x₀) datum datum)) ∧
      ((S.ribbonAmbientEmbedding R parameterOne).map ''
        S.deformation.target.ribbonDomain.domain.carrier ⊆ (W : Set (LGSpace n))) := by
  obtain ⟨S, hS⟩ := M.exists_shrinkingData_into W hcore
  obtain ⟨x, hx⟩ := hP
  let x₀ : S.extension := ⟨x, S.contains_carrier hx⟩
  refine ⟨S, x₀, hS, fun datum => ⟨S.grading x₀ datum⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  rw [← S.fiberEmbedding_compact M parameterOne x hx]
  exact hS x

end FsFltz
