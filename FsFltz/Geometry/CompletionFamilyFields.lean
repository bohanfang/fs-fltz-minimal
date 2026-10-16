import FsFltz.Geometry.CompletionFamilyEquations
import FsFltz.Geometry.FamilyLiouville

/-!
# Actual Liouville fields in presented completion families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. The differential of a presentation equivalence
transports nondegeneracy and the target Liouville contraction equation.
Consequently joint smoothness of the transported primitives produces joint
smoothness of the transported actual fields. No contraction equation or
field regularity for the transported family is assumed anew.

This removes a redundant regularity obligation once compatible completed
primitive extensions have been obtained. It does not construct those
extensions, completions, or presentation maps.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- Nondegeneracy is transported by the actual differential of a smooth
diffeomorphism, with no separate nondegeneracy certificate on the source. -/
theorem nondegenerate_pullback_equiv {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : M.SmoothEquiv N) (eta : N.Form 2) (x : M.Point)
    (heta : N.Nondegenerate eta (f x)) :
    M.Nondegenerate (M.pullback N f eta) x := by
  let A := f.mfderivToContinuousLinearEquiv (by simp) x
  intro v hv
  apply A.injective
  rw [map_zero]
  apply heta
  intro w
  obtain ⟨u, rfl⟩ := A.surjective w
  have he := hv u
  change eta (f x) (fun i =>
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x (![v, u] i)) = 0 at he
  convert he using 1
  change eta (f x) ![A v, A u] = eta (f x) (fun i =>
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x (![v, u] i))
  apply congrArg (eta (f x))
  funext i
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse derivative used by vector-field pullback is an actual
inverse to the forward derivative. -/
theorem mfderiv_pullbackVectorField {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (f : M.SmoothEquiv N)
    (Z : (x : N.Point) → N.Tangent x) (x : M.Point) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x
      (M.pullbackVectorField N f Z x) = Z (f x) := by
  have hs : (f ∘ f.invFun : N.Point → N.Point) = id := funext f.right_inv
  have hd := mfderiv_comp (f x) (f.contMDiff.mdifferentiableAt (by simp))
    (f.symm.contMDiff.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) (f ∘ f.invFun) (f x) =
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f (f.invFun (f x))).comp
      (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) f.invFun (f x)) at hd
  rw [hs, mfderiv_id] at hd
  have hdv := congrArg (fun L => L (Z (f x))) hd
  change Z (f x) = mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f (f.invFun (f x))
    (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) f.invFun (f x) (Z (f x))) at hdv
  have hinv : f.invFun (f x) = x := f.left_inv x
  rw [hinv] at hdv
  exact hdv.symm

end SmoothManifold

namespace CompleteLiouvilleManifold

/-- Exterior-derivative naturality and target symplecticity give actual
nondegeneracy for the transported primitive. -/
theorem nondegenerate_pullback_primitive {d e : ℕ}
    (Y : CompleteLiouvilleManifold e) (M : SmoothManifold d)
    (f : M.SmoothEquiv Y.manifold) (x : M.Point) :
    M.Nondegenerate (M.exteriorDerivative (M.pullback Y.manifold f Y.primitive)) x := by
  have hd := M.exteriorDerivative_pullback Y.manifold f.toContMDiffMap
    Y.primitive Y.smooth_primitive
  change M.exteriorDerivative (M.pullback Y.manifold f Y.primitive) =
    M.pullback Y.manifold f (Y.manifold.exteriorDerivative Y.primitive) at hd
  rw [hd]
  exact M.nondegenerate_pullback_equiv Y.manifold f _ x
    (Y.symplectic.2.2 (f x) (mem_univ _))

set_option backward.isDefEq.respectTransparency false in
/-- The actual pulled-back field satisfies the contraction equation for
the actual pulled-back primitive. No equation for it is extra data. -/
theorem liouvilleEquation_pullback_field {d e : ℕ}
    (Y : CompleteLiouvilleManifold e) (M : SmoothManifold d)
    (f : M.SmoothEquiv Y.manifold) (x : M.Point) :
    M.LiouvilleEquation (M.pullback Y.manifold f Y.primitive) x
      (M.pullbackVectorField Y.manifold f Y.field x) := by
  intro v
  have hd := M.exteriorDerivative_pullback Y.manifold f.toContMDiffMap
    Y.primitive Y.smooth_primitive
  change M.exteriorDerivative (M.pullback Y.manifold f Y.primitive) =
    M.pullback Y.manifold f (Y.manifold.exteriorDerivative Y.primitive) at hd
  rw [hd]
  have hs : (fun i : Fin 2 => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x
      (![M.pullbackVectorField Y.manifold f Y.field x, v] i)) =
      ![Y.field (f x), mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x v] := by
    funext i
    fin_cases i
    · exact M.mfderiv_pullbackVectorField Y.manifold f Y.field x
    · rfl
  change (Y.manifold.exteriorDerivative Y.primitive (f x))
    (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x
      (![M.pullbackVectorField Y.manifold f Y.field x, v] i)) =
    evalOne Y.primitive (f x) (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x v)
  rw [hs]
  exact Y.contraction (f x) _

/-- For independent moving completed manifolds, regularity of the
transported primitives implies regularity of their actual transported
Liouville fields. Symplecticity and contraction come from the target data. -/
theorem isSmoothIntervalVectorFieldFamily_pullback {d e : ℕ}
    (M : SmoothManifold d) (Y : Parameter → CompleteLiouvilleManifold e)
    (f : ∀ t, M.SmoothEquiv (Y t).manifold)
    (hα : M.IsSmoothIntervalFormFamily
      (fun t => M.pullback (Y t).manifold (f t) (Y t).primitive)) :
    M.IsSmoothIntervalVectorFieldFamily
      (fun t => M.pullbackVectorField (Y t).manifold (f t) (Y t).field) := by
  apply M.isSmoothIntervalVectorFieldFamily_of_liouvilleEquation
    (fun t => M.pullback (Y t).manifold (f t) (Y t).primitive) hα
  · intro t x
    exact (Y t).nondegenerate_pullback_primitive M (f t) x
  · intro t x
    exact (Y t).liouvilleEquation_pullback_field M (f t) x

end CompleteLiouvilleManifold

namespace Completion

/-- The completed-field regularity clause for a presented domain family is
a theorem from its completed primitive clause. The independent geometric
input has no completed smooth-field certificate. -/
theorem isSmoothIntervalVectorFieldFamily_pullback_of_primitive_smooth
    {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (hα : C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive)) :
    C.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
      C.ambient.manifold.pullbackVectorField (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.field) :=
  CompleteLiouvilleManifold.isSmoothIntervalVectorFieldFamily_pullback
    C.ambient.manifold (fun t => (C' t).ambient) (fun t => (p t).equiv) hα

/-- Compatible compact/collar extensions supply both completed regularity
clauses at once. Identification of the completed primitive and the actual
field contraction equation are proved by the preceding producers. The
raw extension and collar choices remain explicit construction obligations. -/
theorem isSmoothIntervalPrimitiveAndFieldFamily_of_compatible_extensions
    {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val =
      D.domain.extension.pullback (E t).domain.extension (h t).extensionEquiv
        (E t).liouville.primitive)
    (η : ℝ → C.ambient.manifold.Form 1)
    (hcompact : ∀ t x, x ∈ interior D.domain.carrier →
      D.domain.extension.pullback C.ambient.manifold C.inclusion.map (η t) x = α t x)
    (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) (hU : IsOpen U)
    (hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U)
    (hend : ∀ q ∈ U, ∀ v s,
      evalOne (η q.1) (C.endMap q.2)
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap q.2 (v, s)) = Real.exp q.2.2 *
          evalOne (D.domain.boundaryForm (α q.1)) q.2.1 v) :
    C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive) ∧
    C.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
      C.ambient.manifold.pullbackVectorField (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.field) := by
  have hp := C.isSmoothIntervalFormFamily_pullback_of_compatible_extensions
    E C' h p α hα hαeq η hcompact U hU hpos hend
  exact ⟨hp, C.isSmoothIntervalVectorFieldFamily_pullback_of_primitive_smooth E C' h p hp⟩

end Completion
end FsFltz.Geometry
