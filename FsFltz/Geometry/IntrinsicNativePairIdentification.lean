import FsFltz.Geometry.IntrinsicNativeFamilyEndpointComparison
import FsFltz.Geometry.IntrinsicNativeOriginalCompactMap
import FsFltz.Geometry.IntrinsicZeroOriginalCompactMap
import FsFltz.Geometry.BoundaryContact
import FsFltz.Geometry.Chain

/-!
# Native ribbon maps and strict completion identifications

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199, and
`sec:lean`, lines 788–814. A prescribed strict ambient map determines its
smooth boundary map, radial shift and contact primitive. Compatibility with
a prescribed native ribbon map is stated on their actual escaping trajectories.
Injectivity of the completed end then proves the required boundary/ribbon
square on the entire original ribbon carrier.

Positive-dimensional native germs and primitive squares construct the compact
ribbon map on the original endpoint domains. No ambient, ribbon or completion
is replaced. The ambient map can have arbitrary radial shifts; neither its
boundary map nor an assembled completion identification is assumed. This is
a conditional foundational adapter, not a construction of a target-specific
chain, marking, core equality or grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

/-- Once the boundary coordinates of the same ambient map are known, its
boundary square is equivalent to agreement of the actual escaping trajectory.
The witness is an unrestricted real shift, with no sign or zero condition. -/
theorem boundary_square_iff_trajectory {d e : ℕ}
    {D : LiouvilleDomain d} {E : LiouvilleDomain e}
    (C : Completion D) (C' : Completion E)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (ψ : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (s : D.domain.boundary.Point → ℝ)
    (hend : ∀ x r, f (C.endMap (x, r)) = C'.endMap (ψ x, r + s x))
    (x : D.domain.boundary.Point) (y : E.domain.boundary.Point) :
    ψ x = y ↔ ∃ r : ℝ, f (C.endMap (x, 0)) = C'.endMap (y, r) := by
  constructor
  · intro hxy
    exact ⟨s x, by simpa only [zero_add, hxy] using hend x 0⟩
  · rintro ⟨r, hr⟩
    exact congrArg Prod.fst (C'.endMap_injective ((hend x 0).symm.trans hr))

end Completion

namespace CompletionIdentification

/-- A strict ambient map and a scaled compact ribbon map assemble into a
permitted identification when their full ribbons follow the same escaping
trajectories. The induced boundary map, its shift and its primitive law are
derived from the supplied ambient map. This includes dimension zero. -/
theorem exists_of_ribbon_trajectory_square {n : ℕ}
    (P Q : WitnessedPair n)
    (f : P.ambientCompletion.ambient.manifold.SmoothEquiv
      Q.ambientCompletion.ambient.manifold)
    (hprimitive : P.ambientCompletion.ambient.manifold.pullback
      Q.ambientCompletion.ambient.manifold f Q.ambientCompletion.ambient.primitive =
        P.ambientCompletion.ambient.primitive)
    (g : CompactDomainDiffeomorph P.ribbonDomain.domain Q.ribbonDomain.domain)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x ∈ P.ribbonDomain.domain.carrier,
      P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension g.map
        Q.ribbonDomain.liouville.primitive x = c • P.ribbonDomain.liouville.primitive x)
    (htrajectory : ∀ x ∈ P.ribbonDomain.domain.carrier, ∃ r : ℝ,
      f (P.ambientCompletion.endMap (P.ribbonEmbedding.map x, 0)) =
        Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (g.map x), r)) :
    ∃ I : CompletionIdentification P Q,
      I.ambientEquiv = f ∧ I.ribbonEquiv = g ∧ I.scale = c := by
  obtain ⟨ψ, s, hs, hend, hp⟩ :=
    P.ambientCompletion.exists_boundaryEquiv_with_pullback Q.ambientCompletion f hprimitive
  have hsquare (x : P.ribbonDomain.domain.extension.Point)
      (hx : x ∈ P.ribbonDomain.domain.carrier) :
      ψ (P.ribbonEmbedding.map x) = Q.ribbonEmbedding.map (g.map x) := by
    exact (P.ambientCompletion.boundary_square_iff_trajectory Q.ambientCompletion
      f ψ s hend (P.ribbonEmbedding.map x) (Q.ribbonEmbedding.map (g.map x))).mpr
        (htrajectory x hx)
  let I : CompletionIdentification P Q :=
    { ambientEquiv := f
      primitive := hprimitive
      boundaryEquiv := ψ
      shift := s
      smooth_shift := hs
      induced_at_infinity := fun x => ⟨0, fun r _ => hend x r⟩
      boundary_primitive := hp
      ribbonEquiv := g
      scale := c
      positive_scale := hc
      ribbon_primitive := hscale
      ribbon_square := hsquare }
  exact ⟨I, rfl, rfl, rfl⟩

end CompletionIdentification

namespace IntrinsicLiouville

variable {k d : ℕ} [NeZero d] {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [IsManifold (𝓡∂ (k + 1)) ∞ N]
  [CompactSpace M]

/-- Reconstruct the native presentations on the original fixed compact
domains, and represent the prescribed native map on those same domains. -/
theorem exists_originalNativeCompactDiffeomorph_on_fixed_endpoints
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
    (c : ℝ)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) :
    ∃ g : CompactDomainDiffeomorph D.domain D'.domain,
      (∀ x, g.map (eM x).val = (eN (h x)).val) ∧
      (∀ y, g.inverse (eN y).val = (eM (h.symm y)).val) ∧
      ∀ x ∈ D.domain.carrier,
        D.domain.extension.pullback D'.domain.extension g.map D'.liouville.primitive x =
          c • D.liouville.primitive x := by
  subst d
  let R := NativeLiouvillePresentation.of_endpoint α D eM hM hcoordM
  let R' := NativeLiouvillePresentation.of_endpoint β D' eN hN hcoordN
  exact R.exists_originalNativeCompactDiffeomorph R' C C' h hgerm c hscale

end IntrinsicLiouville

namespace CompletionIdentification
open IntrinsicLiouville

variable {k n : ℕ} [NeZero (2 * n - 2)] {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [IsManifold (𝓡∂ (k + 1)) ∞ N]
  [CompactSpace M]

/-- Compatible native ribbon trajectories construct a full permitted
identification on the exact original pairs and completions. The supplied
strict ambient map is retained, including any nonzero radial shifts.
The prescribed native ribbon map and inverse and its constant scale are
retained on the entire ribbon; encoded compatibility is proved. -/
theorem exists_of_nativeRibbon_trajectory_square
    (P Q : WitnessedPair n) (hdim : k + 1 = 2 * n - 2)
    (f : P.ambientCompletion.ambient.manifold.SmoothEquiv
      Q.ambientCompletion.ambient.manifold)
    (hprimitive : P.ambientCompletion.ambient.manifold.pullback
      Q.ambientCompletion.ambient.manifold f Q.ambientCompletion.ambient.primitive =
        P.ambientCompletion.ambient.primitive)
    (α : Form k M 1) (β : Form k N 1)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞)
    (eN : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) N Q.ribbonDomain.domain.Point ∞)
    (hM : ∀ x, (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = α x)
    (hN : ∀ x, (Q.ribbonDomain.liouville.primitive (eN x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eN y).val) x) = β x)
    (hcoordM : HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => (eM x).val))
    (hcoordN : HasNativeCoordinateExtensions (k := k) Q.ribbonDomain.domain.extension (fun x => (eN x).val))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x)
    (htrajectory : ∀ x, ∃ r : ℝ,
      f (P.ambientCompletion.endMap (P.ribbonEmbedding.map (eM x).val, 0)) =
        Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (eN (h x)).val, r)) :
    ∃ I : CompletionIdentification P Q,
      I.ambientEquiv = f ∧ I.scale = c ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eN (h x)).val) ∧
      (∀ y, I.ribbonEquiv.inverse (eN y).val = (eM (h.symm y)).val) := by
  obtain ⟨g, hsquare, hinverse, hp⟩ :=
    exists_originalNativeCompactDiffeomorph_on_fixed_endpoints hdim
      P.ribbonDomain Q.ribbonDomain P.ribbonCompletion Q.ribbonCompletion
      α β eM eN hM hN hcoordM hcoordN h hgerm c hscale
  have ht (z : P.ribbonDomain.domain.extension.Point)
      (hz : z ∈ P.ribbonDomain.domain.carrier) : ∃ r : ℝ,
      f (P.ambientCompletion.endMap (P.ribbonEmbedding.map z, 0)) =
        Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (g.map z), r) := by
    obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
    have hx' : (eM x).val = z := congrArg Subtype.val hx
    rw [← hx', hsquare]
    exact htrajectory x
  obtain ⟨I, hf, hg, hc'⟩ := exists_of_ribbon_trajectory_square P Q f hprimitive g c hc hp ht
  exact ⟨I, hf, hc', by simpa only [hg] using hsquare, by simpa only [hg] using hinverse⟩

end CompletionIdentification

namespace CompletionIdentification

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (Model 0) M] [ChartedSpace (Model 0) N]

/-- The same assembly for a rank-one pair's zero-dimensional native ribbon.
The original finite map producer supplies the compact diffeomorphism and
its full primitive scale, including empty carriers. Arbitrary radial shifts
of the supplied strict ambient map remain permitted. -/
theorem exists_of_nativeZeroRibbon_trajectory_square
    (P Q : WitnessedPair 1)
    (f : P.ambientCompletion.ambient.manifold.SmoothEquiv
      Q.ambientCompletion.ambient.manifold)
    (hprimitive : P.ambientCompletion.ambient.manifold.pullback
      Q.ambientCompletion.ambient.manifold f Q.ambientCompletion.ambient.primitive =
        P.ambientCompletion.ambient.primitive)
    (eM : letI := P.ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞)
    (eN : letI := Q.ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N Q.ribbonDomain.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞)
    (c : ℝ) (hc : 0 < c)
    (htrajectory : ∀ x, ∃ r : ℝ,
      f (P.ambientCompletion.endMap (P.ribbonEmbedding.map (eM x).val, 0)) =
        Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (eN (h x)).val, r)) :
    ∃ I : CompletionIdentification P Q,
      I.ambientEquiv = f ∧ I.scale = c ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eN (h x)).val) ∧
      (∀ y, I.ribbonEquiv.inverse (eN y).val = (eM (h.symm y)).val) := by
  obtain ⟨g, hsquare, hinverse, hp⟩ :=
    IntrinsicZeroLiouville.exists_originalNativeCompactDiffeomorph
      P.ribbonDomain Q.ribbonDomain P.ribbonCompletion Q.ribbonCompletion eM eN h c
  have ht (z : P.ribbonDomain.domain.extension.Point)
      (hz : z ∈ P.ribbonDomain.domain.carrier) : ∃ r : ℝ,
      f (P.ambientCompletion.endMap (P.ribbonEmbedding.map z, 0)) =
        Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (g.map z), r) := by
    obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
    have hx' : (eM x).val = z := congrArg Subtype.val hx
    rw [← hx', hsquare]
    exact htrajectory x
  obtain ⟨I, hf, hg, hc'⟩ := exists_of_ribbon_trajectory_square P Q f hprimitive g c hc hp ht
  exact ⟨I, hf, hc', by simpa only [hg] using hsquare, by simpa only [hg] using hinverse⟩

end CompletionIdentification
end FsFltz.Geometry
