import FsFltz.Geometry.CompletionMapUniqueness

/-!
# Inclusion markings transported from a distinct native slice

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 143–146;
`g:initial`, lines 374–384; and `sec:lean`, lines 805–814.
A supplied native slice diffeomorphism and a supplied original marking
give an actual inclusion marking on the very same represented completion.
Its compact equation retains the original native inclusion; its all-real
end equation follows from primitive preservation and the actual flows.
The construction allows dimension zero. It asserts no target-specific
existence of a native slice equivalence or a full-fiber marking.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace FsFltz.Geometry.Completion

variable {a d : ℕ} {D : LiouvilleDomain d} {M : Type}

/-- Transport a supplied original native marking through the inverse of
the specified native slice comparison. The represented compact inclusion
is exactly the original inclusion relabeled by the retained carrier map. -/
def inclusionMarkingOfNativeSliceEquiv
    (C : Completion D) (X : SmoothManifold a) (Λ : X.Form 1)
    (S : X.SmoothEquiv C.ambient.manifold)
    (hS : X.pullback C.ambient.manifold S C.ambient.primitive = Λ)
    (e : M ≃ D.domain.Point) (ν : M → X.Point)
    (hScompact : ∀ x, S (ν x) = C.inclusion.map (e x).val)
    (Z : CompleteLiouvilleManifold d) (i : M → Z.manifold.Point)
    (q : X.SmoothEquiv Z.manifold)
    (hq : X.pullback Z.manifold q Z.primitive = Λ)
    (hqcompact : ∀ x, q (ν x) = i x) :
    InclusionMarking C Z (fun y => i (e.symm y)) := by
  have hSinv : C.ambient.manifold.pullback X S.symm Λ = C.ambient.primitive := by
    rw [← hS]
    exact X.pullback_symm_pullback C.ambient.manifold S C.ambient.primitive
  have hp : C.ambient.manifold.pullback Z.manifold (S.symm.trans q) Z.primitive =
      C.ambient.primitive := by
    change C.ambient.manifold.pullback Z.manifold (q ∘ S.symm) Z.primitive = _
    rw [C.ambient.manifold.pullback_comp X Z.manifold
      (S.symm.contMDiff.mdifferentiable (by simp))
      (q.contMDiff.mdifferentiable (by simp)), hq, hSinv]
  refine { equiv := S.symm.trans q, primitive := hp, inclusion := ?_, flow_induced := ?_ }
  · intro y
    change q (S.symm (C.inclusion.map y.val)) = i (e.symm y)
    rw [← show S (ν (e.symm y)) = C.inclusion.map y.val by
      simpa only [e.apply_symm_apply] using hScompact (e.symm y), S.symm_apply_apply]
    exact hqcompact (e.symm y)
  · intro x r
    rw [C.end_flow, C.ambient.map_flow Z (S.symm.trans q) hp]

@[simp] theorem inclusionMarkingOfNativeSliceEquiv_equiv
    (C : Completion D) (X : SmoothManifold a) (Λ : X.Form 1)
    (S : X.SmoothEquiv C.ambient.manifold)
    (hS : X.pullback C.ambient.manifold S C.ambient.primitive = Λ)
    (e : M ≃ D.domain.Point) (ν : M → X.Point)
    (hScompact : ∀ x, S (ν x) = C.inclusion.map (e x).val)
    (Z : CompleteLiouvilleManifold d) (i : M → Z.manifold.Point)
    (q : X.SmoothEquiv Z.manifold)
    (hq : X.pullback Z.manifold q Z.primitive = Λ)
    (hqcompact : ∀ x, q (ν x) = i x) :
    (C.inclusionMarkingOfNativeSliceEquiv X Λ S hS e ν hScompact Z i q hq hqcompact).equiv =
      S.symm.trans q := rfl

/-- Returning along the retained native slice recovers the original
supplied marking on the whole source, not just on its compact piece. -/
theorem inclusionMarkingOfNativeSliceEquiv_recovers_original
    (C : Completion D) (X : SmoothManifold a) (Λ : X.Form 1)
    (S : X.SmoothEquiv C.ambient.manifold)
    (hS : X.pullback C.ambient.manifold S C.ambient.primitive = Λ)
    (e : M ≃ D.domain.Point) (ν : M → X.Point)
    (hScompact : ∀ x, S (ν x) = C.inclusion.map (e x).val)
    (Z : CompleteLiouvilleManifold d) (i : M → Z.manifold.Point)
    (q : X.SmoothEquiv Z.manifold)
    (hq : X.pullback Z.manifold q Z.primitive = Λ)
    (hqcompact : ∀ x, q (ν x) = i x) :
    S.trans (C.inclusionMarkingOfNativeSliceEquiv
      X Λ S hS e ν hScompact Z i q hq hqcompact).equiv = q := by
  apply Diffeomorph.ext
  intro x
  change q (S.symm (S x)) = q x
  rw [S.symm_apply_apply]

/-- The transported marking retains the supplied original native compact
equation, rather than choosing a new marking on the endpoint. -/
theorem inclusionMarkingOfNativeSliceEquiv_native
    (C : Completion D) (X : SmoothManifold a) (Λ : X.Form 1)
    (S : X.SmoothEquiv C.ambient.manifold)
    (hS : X.pullback C.ambient.manifold S C.ambient.primitive = Λ)
    (e : M ≃ D.domain.Point) (ν : M → X.Point)
    (hScompact : ∀ x, S (ν x) = C.inclusion.map (e x).val)
    (Z : CompleteLiouvilleManifold d) (i : M → Z.manifold.Point)
    (q : X.SmoothEquiv Z.manifold)
    (hq : X.pullback Z.manifold q Z.primitive = Λ)
    (hqcompact : ∀ x, q (ν x) = i x) (x : M) :
    (C.inclusionMarkingOfNativeSliceEquiv X Λ S hS e ν hScompact Z i q hq hqcompact).equiv
      (C.inclusion.map (e x).val) = i x := by
  simpa only [e.symm_apply_apply] using
    (C.inclusionMarkingOfNativeSliceEquiv X Λ S hS e ν hScompact Z i q hq hqcompact).inclusion (e x)

/-- The specified native inclusion also determines the target trajectory
of every represented boundary point, at every real radius. -/
theorem inclusionMarkingOfNativeSliceEquiv_end
    (C : Completion D) (X : SmoothManifold a) (Λ : X.Form 1)
    (S : X.SmoothEquiv C.ambient.manifold)
    (hS : X.pullback C.ambient.manifold S C.ambient.primitive = Λ)
    (e : M ≃ D.domain.Point) (ν : M → X.Point)
    (hScompact : ∀ x, S (ν x) = C.inclusion.map (e x).val)
    (Z : CompleteLiouvilleManifold d) (i : M → Z.manifold.Point)
    (q : X.SmoothEquiv Z.manifold)
    (hq : X.pullback Z.manifold q Z.primitive = Λ)
    (hqcompact : ∀ x, q (ν x) = i x) (x : D.domain.boundary.Point) (r : ℝ) :
    (C.inclusionMarkingOfNativeSliceEquiv X Λ S hS e ν hScompact Z i q hq hqcompact).equiv
      (C.endMap (x, r)) = Z.completeFlow.flow r
        (i (e.symm ⟨D.domain.boundaryInclusion.map x,
          D.domain.boundaryInclusion_mem_carrier x⟩)) := by
  let m := C.inclusionMarkingOfNativeSliceEquiv X Λ S hS e ν hScompact Z i q hq hqcompact
  rw [m.flow_induced, m.inclusion
    ⟨D.domain.boundaryInclusion.map x, D.domain.boundaryInclusion_mem_carrier x⟩]

end FsFltz.Geometry.Completion
