import FsFltz.Geometry.IntrinsicNativePairFamily
import FsFltz.Geometry.IntrinsicNativeZeroPairFamily
import FsFltz.Geometry.IntrinsicNativeMapComparison
import FsFltz.Geometry.IntrinsicZeroCompactDiffeomorph

/-!
# Prescribed native maps on the exact completed family endpoints

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 783–814 and 825–830. The endpoint adapters retain the
compact domains, native carrier identifications and completions of the
already constructed pair families. Original coordinate germs and primitive
squares construct the map on these completions. In dimension zero the
actual native inclusion is a diffeomorphism onto the whole completion.

These maps extend native compact diffeomorphisms. General strict completion
maps with radial shifts, boundary/ribbon matching for a permitted pair
identification, bundle trivializations and target-specific chains remain
separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k d : ℕ} [NeZero d] {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [IsManifold (𝓡∂ (k + 1)) ∞ N]
  [CompactSpace M]

/-- Extend a prescribed native map on the two already fixed endpoints
and their original supplied completions. The endpoint presentations are
constructed from the retained carrier maps; neither endpoint is replaced. -/
theorem exists_scaledEquiv_on_fixed_native_endpoints
    (hdim : k + 1 = d) (D D' : LiouvilleDomain d)
    (C : Completion D) (C' : Completion D')
    (α : Form k M 1) (β : Form k N 1)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (eN : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) N D'.domain.Point ∞)
    (hM : ∀ x, (D.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) (fun y => (eM y).val) x) = α x)
    (hN : ∀ x, (D'.liouville.primitive (eN x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) (fun y => (eN y).val) x) = β x)
    (hcoordM : HasNativeCoordinateExtensions (k := k) D.domain.extension (fun x => (eM x).val))
    (hcoordN : HasNativeCoordinateExtensions (k := k) D'.domain.extension (fun x => (eN x).val))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) :
    ∃ (e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
      (b : D.domain.boundary.SmoothEquiv D'.domain.boundary),
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        c • C.ambient.primitive ∧
      (∀ x, e (C.inclusion.map (eM x).val) = C'.inclusion.map (eN (h x)).val) ∧
      (∀ y, e.symm (C'.inclusion.map (eN y).val) = C.inclusion.map (eM (h.symm y)).val) ∧
      (∀ x, e (C.inclusion.map (D.domain.boundaryInclusion.map x)) =
        C'.inclusion.map (D'.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e (C.endMap (x, r)) = C'.endMap (b x, r)) ∧
      (∀ z t, e (C.ambient.completeFlow.flow t z) = C'.ambient.completeFlow.flow t (e z)) ∧
      (∀ x, (eM x).val ∈ C.core ↔ (eN (h x)).val ∈ C'.core) := by
  subst d
  let P := NativeLiouvillePresentation.of_endpoint α D eM hM hcoordM
  let Q := NativeLiouvillePresentation.of_endpoint β D' eN hN hcoordN
  obtain ⟨e, b, hp, hsquare, hinverse, hboundary, hend⟩ :=
    P.exists_scaledCompletionEquiv_of_nativeDiffeomorph Q h hgerm c hc hscale C C'
  have hflow := C.ambient.map_flow_of_scaled_primitive C'.ambient e c hp
  exact ⟨e, b, hp, hsquare, hinverse, hboundary, hend, hflow,
    P.core_transport_of_native_square Q C C' h.toEquiv e hsquare hflow⟩

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicZeroLiouville

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- The native carrier map into an arbitrary original zero-dimensional
completion is a diffeomorphism. Coverage proves surjectivity because its
cylindrical boundary is empty; no new completion is constructed. -/
def endpointCompletionDiffeomorph (D : LiouvilleDomain 0) (C : Completion D)
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞) :
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M C.ambient.manifold.Point ∞ := by
  let f : M → C.ambient.manifold.Point := fun x => C.inclusion.map (eM x).val
  have hinj : Function.Injective f := by
    intro x y hxy
    exact eM.injective (Subtype.ext (C.inclusion.embedding.injective hxy))
  have hsurj : Function.Surjective f := by
    intro y
    have hy : y ∈ C.inclusion.map '' D.domain.carrier ∪
        C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := C.covering ▸ mem_univ y
    rcases hy with hy | hy
    · obtain ⟨z, hz, hzy⟩ := hy
      obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
      exact ⟨x, (congrArg (fun w => C.inclusion.map w.val) hx).trans hzy⟩
    · obtain ⟨⟨b, _⟩, _, _⟩ := hy
      exact ((D.domain.zero_boundary rfl).false b).elim
  letI := source_discreteTopology M
  letI := C.ambient.manifold.discreteTopology_of_dimension_zero
  exact { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
          contMDiff_toFun := contMDiff_of_discreteTopology
          contMDiff_invFun := contMDiff_of_discreteTopology }

@[simp] theorem endpointCompletionDiffeomorph_apply (D : LiouvilleDomain 0) (C : Completion D)
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞) (x : M) :
    endpointCompletionDiffeomorph D C eM x = C.inclusion.map (eM x).val := rfl

variable {N : Type} [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N]
  [ChartedSpace (Model 0) N] [IsManifold 𝓘(ℝ, Model 0) ∞ N]

/-- Prescribed zero-dimensional native maps extend on independently fixed
compact endpoints and their original completions, preserving both compact
directions. Vanishing forms give the full constant primitive scale. -/
theorem exists_scaledEquiv_on_fixed_native_endpoints
    (D D' : LiouvilleDomain 0) (C : Completion D) (C' : Completion D')
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞)
    (eN : letI := D'.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N D'.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (c : ℝ) :
    ∃ e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold,
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        c • C.ambient.primitive ∧
      (∀ x, e (C.inclusion.map (eM x).val) = C'.inclusion.map (eN (h x)).val) ∧
      (∀ y, e.symm (C'.inclusion.map (eN y).val) = C.inclusion.map (eM (h.symm y)).val) ∧
      (∀ z t, e (C.ambient.completeFlow.flow t z) = C'.ambient.completeFlow.flow t (e z)) := by
  let a := endpointCompletionDiffeomorph D C eM
  let b := endpointCompletionDiffeomorph D' C' eN
  let e := (a.symm.trans h).trans b
  have hp : C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
      c • C.ambient.primitive := by
    rw [C'.ambient.manifold.oneForm_eq_zero_of_dimension_zero C'.ambient.primitive,
      C.ambient.manifold.oneForm_eq_zero_of_dimension_zero C.ambient.primitive]
    ext x v
    simp [SmoothManifold.pullback]
  refine ⟨e, hp, ?_, ?_, C.ambient.map_flow_of_scaled_primitive C'.ambient e c hp⟩
  · intro x
    change b (h (a.symm (a x))) = b (h x)
    rw [a.symm_apply_apply]
  · intro y
    change a (h.symm (b.symm (b y))) = a (h.symm y)
    rw [b.symm_apply_apply]

end FsFltz.Geometry.IntrinsicZeroLiouville


namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville

variable {k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [IsManifold (𝓡∂ (k + 1)) ∞ N]
  [CompactSpace M]

omit [NeZero n] in
/-- The exact ribbon completions of two actual pair families extend a
prescribed native constant-scale compact map. Coordinate and primitive
premises are the endpoint conclusions retained by the native family producer. -/
theorem exists_scaledNativeRibbonEndpointEquiv
    (Q Q' : PairDeformation n) (t t' : Parameter) (hdim : k + 1 = 2 * n - 2)
    (α : Form k M 1) (β : Form k N 1)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M (Q.pair t).ribbonDomain.domain.Point ∞)
    (eN : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) N (Q'.pair t').ribbonDomain.domain.Point ∞)
    (hM : ∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = α x)
    (hN : ∀ x, ((Q'.pair t').ribbonDomain.liouville.primitive (eN x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eN y).val) x) = β x)
    (hcoordM : HasNativeCoordinateExtensions (k := k) (Q.pair t).ribbonDomain.domain.extension (fun x => (eM x).val))
    (hcoordN : HasNativeCoordinateExtensions (k := k) (Q'.pair t').ribbonDomain.domain.extension (fun x => (eN x).val))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) :
    ∃ (e : (Q.pair t).ribbonCompletion.ambient.manifold.SmoothEquiv (Q'.pair t').ribbonCompletion.ambient.manifold)
      (b : (Q.pair t).ribbonDomain.domain.boundary.SmoothEquiv (Q'.pair t').ribbonDomain.domain.boundary),
      (Q.pair t).ribbonCompletion.ambient.manifold.pullback (Q'.pair t').ribbonCompletion.ambient.manifold e (Q'.pair t').ribbonCompletion.ambient.primitive =
        c • (Q.pair t).ribbonCompletion.ambient.primitive ∧
      (∀ x, e ((Q.pair t).ribbonCompletion.inclusion.map (eM x).val) = (Q'.pair t').ribbonCompletion.inclusion.map (eN (h x)).val) ∧
      (∀ y, e.symm ((Q'.pair t').ribbonCompletion.inclusion.map (eN y).val) = (Q.pair t).ribbonCompletion.inclusion.map (eM (h.symm y)).val) ∧
      (∀ x, e ((Q.pair t).ribbonCompletion.inclusion.map ((Q.pair t).ribbonDomain.domain.boundaryInclusion.map x)) =
        (Q'.pair t').ribbonCompletion.inclusion.map ((Q'.pair t').ribbonDomain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e ((Q.pair t).ribbonCompletion.endMap (x, r)) = (Q'.pair t').ribbonCompletion.endMap (b x, r)) ∧
      (∀ z s, e ((Q.pair t).ribbonCompletion.ambient.completeFlow.flow s z) = (Q'.pair t').ribbonCompletion.ambient.completeFlow.flow s (e z)) ∧
      (∀ x, (eM x).val ∈ (Q.pair t).ribbonCompletion.core ↔ (eN (h x)).val ∈ (Q'.pair t').ribbonCompletion.core) := by
  exact IntrinsicLiouville.exists_scaledEquiv_on_fixed_native_endpoints hdim
    (Q.pair t).ribbonDomain (Q'.pair t').ribbonDomain
    (Q.pair t).ribbonCompletion (Q'.pair t').ribbonCompletion
    α β eM eN hM hN hcoordM hcoordN h hgerm c hc hscale

omit [NeZero (2 * n - 2)] in
/-- The exact ambient completions of two actual pair families extend a
prescribed primitive-preserving native compact map. The native compact
directions, actual boundary, same-radius ends, flows and full cores agree. -/
theorem exists_strictNativeAmbientEndpointEquiv
    (Q Q' : PairDeformation n) (t t' : Parameter) (hdim : k + 1 = 2 * n)
    (α : Form k M 1) (β : Form k N 1)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M (Q.pair t).ambientDomain.domain.Point ∞)
    (eN : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) N (Q'.pair t').ambientDomain.domain.Point ∞)
    (hM : ∀ x, ((Q.pair t).ambientDomain.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eM y).val) x) = α x)
    (hN : ∀ x, ((Q'.pair t').ambientDomain.liouville.primitive (eN x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eN y).val) x) = β x)
    (hcoordM : HasNativeCoordinateExtensions (k := k) (Q.pair t).ambientDomain.domain.extension (fun x => (eM x).val))
    (hcoordN : HasNativeCoordinateExtensions (k := k) (Q'.pair t').ambientDomain.domain.extension (fun x => (eN x).val))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = α x) :
    ∃ (e : (Q.pair t).ambientCompletion.ambient.manifold.SmoothEquiv (Q'.pair t').ambientCompletion.ambient.manifold)
      (b : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv (Q'.pair t').ambientDomain.domain.boundary),
      (Q.pair t).ambientCompletion.ambient.manifold.pullback (Q'.pair t').ambientCompletion.ambient.manifold e (Q'.pair t').ambientCompletion.ambient.primitive =
        (Q.pair t).ambientCompletion.ambient.primitive ∧
      (∀ x, e ((Q.pair t).ambientCompletion.inclusion.map (eM x).val) = (Q'.pair t').ambientCompletion.inclusion.map (eN (h x)).val) ∧
      (∀ y, e.symm ((Q'.pair t').ambientCompletion.inclusion.map (eN y).val) = (Q.pair t).ambientCompletion.inclusion.map (eM (h.symm y)).val) ∧
      (∀ x, e ((Q.pair t).ambientCompletion.inclusion.map ((Q.pair t).ambientDomain.domain.boundaryInclusion.map x)) =
        (Q'.pair t').ambientCompletion.inclusion.map ((Q'.pair t').ambientDomain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e ((Q.pair t).ambientCompletion.endMap (x, r)) = (Q'.pair t').ambientCompletion.endMap (b x, r)) ∧
      (∀ z s, e ((Q.pair t).ambientCompletion.ambient.completeFlow.flow s z) = (Q'.pair t').ambientCompletion.ambient.completeFlow.flow s (e z)) ∧
      (∀ x, (eM x).val ∈ (Q.pair t).ambientCompletion.core ↔ (eN (h x)).val ∈ (Q'.pair t').ambientCompletion.core) := by
  simpa only [one_smul] using
    (IntrinsicLiouville.exists_scaledEquiv_on_fixed_native_endpoints hdim
      (Q.pair t).ambientDomain (Q'.pair t').ambientDomain
      (Q.pair t).ambientCompletion (Q'.pair t').ambientCompletion
      α β eM eN hM hN hcoordM hcoordN h hgerm 1 (by norm_num)
      (by simpa only [one_smul] using hscale))

end FsFltz.Geometry.PairDeformation

namespace FsFltz.Geometry.PairDeformation

variable {M N : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Model 0) M]
  [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
  [ChartedSpace (Model 0) N] [IsManifold 𝓘(ℝ, Model 0) ∞ N]

/-- The exact zero-dimensional ribbon completions of the already
constructed rank-one pair families retain the prescribed native map
and inverse. No ribbon presentation or completion is reconstructed. -/
theorem exists_nativeZeroRibbonEndpointEquiv
    (Q Q' : PairDeformation 1) (t t' : Parameter)
    (eM : letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair t).ribbonDomain.domain.Point ∞)
    (eN : letI := (Q'.pair t').ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N (Q'.pair t').ribbonDomain.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (c : ℝ) :
    ∃ e : (Q.pair t).ribbonCompletion.ambient.manifold.SmoothEquiv
        (Q'.pair t').ribbonCompletion.ambient.manifold,
      (Q.pair t).ribbonCompletion.ambient.manifold.pullback
        (Q'.pair t').ribbonCompletion.ambient.manifold e
        (Q'.pair t').ribbonCompletion.ambient.primitive =
          c • (Q.pair t).ribbonCompletion.ambient.primitive ∧
      (∀ x, e ((Q.pair t).ribbonCompletion.inclusion.map (eM x).val) =
        (Q'.pair t').ribbonCompletion.inclusion.map (eN (h x)).val) ∧
      (∀ y, e.symm ((Q'.pair t').ribbonCompletion.inclusion.map (eN y).val) =
        (Q.pair t).ribbonCompletion.inclusion.map (eM (h.symm y)).val) ∧
      (∀ z s, e ((Q.pair t).ribbonCompletion.ambient.completeFlow.flow s z) =
        (Q'.pair t').ribbonCompletion.ambient.completeFlow.flow s (e z)) := by
  exact IntrinsicZeroLiouville.exists_scaledEquiv_on_fixed_native_endpoints
    (Q.pair t).ribbonDomain (Q'.pair t').ribbonDomain
    (Q.pair t).ribbonCompletion (Q'.pair t').ribbonCompletion eM eN h c

end FsFltz.Geometry.PairDeformation
