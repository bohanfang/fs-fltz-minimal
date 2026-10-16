import FsFltz.Geometry.Liouville

/-!
# Completeness and finite type for a prescribed ambient primitive

These are concrete existence-witness types for `g:complete` of
`geoemtric-part-fsf.tex`, lines 358–362. Their manifold and primitive are fixed
parameters, so no abstract replacement of the specified source is possible.
Completeness uses an actual smooth flow of the primitive-determined Liouville
vector in both real time directions. Finite type records the actual compact
domain, completion, embedding and primitive-preserving inclusion marking
required by `sec:data`, lines 86–90, and `sec:lean`, lines 805–814.
No existence theorem for these witness types is asserted.
-/

noncomputable section

namespace FsFltz.Geometry
open SmoothManifold

/-- A fixed primitive is symplectic and has its actual smooth complete
Liouville flow. All data concern this very `M` and `lambda`. -/
structure CompletePrimitive {d : ℕ} (M : SmoothManifold d) (lambda : M.Form 1) where
  smooth_primitive : M.IsSmoothForm lambda
  symplectic : M.IsSymplecticOn (M.exteriorDerivative lambda) Set.univ
  smooth_field : M.IsSmoothVectorField (M.liouvilleVector lambda)
  contraction : ∀ x v,
    evalTwo (M.exteriorDerivative lambda) x (M.liouvilleVector lambda x) v =
      evalOne lambda x v
  completeFlow : CompleteLiouvilleFlow M (M.liouvilleVector lambda)

namespace CompletePrimitive

/-- Expose the existing complete-manifold interface without changing points,
primitive, Liouville vector, or flow. -/
def toCompleteLiouvilleManifold {d : ℕ} {M : SmoothManifold d} {lambda : M.Form 1}
    (C : CompletePrimitive M lambda) : CompleteLiouvilleManifold d where
  manifold := M
  primitive := lambda
  smooth_primitive := C.smooth_primitive
  symplectic := C.symplectic
  field := M.liouvilleVector lambda
  smooth_field := C.smooth_field
  contraction := C.contraction
  completeFlow := C.completeFlow

end CompletePrimitive

/-- Finite type of a prescribed primitive means an actual compact Liouville
domain whose marked completion is the whole prescribed ambient. This is an
existence witness used in the conclusion of the target, never a toric input. -/
structure FiniteTypePrimitive {d : ℕ} (M : SmoothManifold d) (lambda : M.Form 1) where
  complete : CompletePrimitive M lambda
  compactDomain : LiouvilleDomain d
  completion : Completion compactDomain
  compactEmbedding : compactDomain.domain.extension.SmoothEmbedding M
  marking : InclusionMarking completion complete.toCompleteLiouvilleManifold
    (fun x => compactEmbedding.map x.val)

end FsFltz.Geometry
