import FsFltz.Geometry.CompactMapNeighborhood
import FsFltz.Geometry.DomainCompletionRestriction
import FsFltz.Geometry.CompletionScaledPresentation

/-!
# Extending a prescribed locally represented compact map to completions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189, and
`sec:lean`, lines 805–814. Open restriction turns a compact map's actual
local extensions into a presentation equivalence. The supplied completions
retain their original ambients, flows and end maps under that restriction.
The completion construction therefore extends the prescribed compact map
between the original completed manifolds, rather than changing it to a
collar-adjusted compact map.

The input remains a `CompactDomainDiffeomorph`; producing that local
representation from an arbitrary native compact diffeomorphism is separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
namespace Completion

/-- A prescribed compact diffeomorphism with positive constant-scale
primitive equality extends between arbitrary supplied completions. The
compact formula uses the original forward map; the end formula uses its
derived boundary restriction and retains the radius coordinate. -/
theorem exists_scaledEquiv_of_compactDiffeomorph {d : ℕ} {D E : LiouvilleDomain d}
    (C : Completion D) (C' : Completion E)
    (h : CompactDomainDiffeomorph D.domain E.domain) (c : ℝ) (hc : 0 < c)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.map E.liouville.primitive x =
        c • D.liouville.primitive x) :
    ∃ (e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
      (b : D.domain.boundary.SmoothEquiv E.domain.boundary),
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        c • C.ambient.primitive ∧
      (∀ x ∈ D.domain.carrier,
        e (C.inclusion.map x) = C'.inclusion.map (h.map x)) ∧
      (∀ x, h.map (D.domain.boundaryInclusion.map x) =
        E.domain.boundaryInclusion.map (b x)) ∧
      (∀ x r, 0 ≤ r → e (C.endMap (x, r)) = C'.endMap (b x, r)) := by
  obtain ⟨U, hDU, V, hEV, p, he, _⟩ := h.exists_restrictedPresentationEquiv
  have hd (x : U) (hx : x.val ∈ D.domain.carrier) :
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) p.extensionEquiv x =
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.map x.val := by
    have hcomp := mfderiv_comp (f := p.extensionEquiv)
      (g := (Subtype.val : V → E.domain.extension.Point)) x
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
      (p.extensionEquiv.contMDiff.mdifferentiableAt (by simp))
    have hval : (Subtype.val : V → E.domain.extension.Point) ∘ p.extensionEquiv =
        fun y : U => h.map y.val := funext he
    rw [hval] at hcomp
    erw [E.domain.extension.mfderiv_restrict_val V (p.extensionEquiv x)] at hcomp
    rw [D.domain.extension.mfderiv_comp_restrict_val E.domain.extension U x
      ((h.smooth_map.contMDiffAt (h.open_source.mem_nhds (h.contains_source hx))).mdifferentiableAt
        (by simp))] at hcomp
    exact hcomp.symm
  have hp' : ∀ x ∈ (D.restrict U hDU).domain.carrier,
      (D.restrict U hDU).domain.extension.pullback (E.restrict V hEV).domain.extension
        p.extensionEquiv (E.restrict V hEV).liouville.primitive x =
          c • (D.restrict U hDU).liouville.primitive x := by
    intro x hx
    unfold SmoothManifold.pullback
    rw [E.liouville.restrict_primitive, D.liouville.restrict_primitive]
    change (E.liouville.primitive (p.extensionEquiv x).val).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) p.extensionEquiv x) = _
    rw [he, hd x hx]
    exact hp x.val hx
  obtain ⟨q, hq⟩ := (C.restrict U hDU).exists_scaledPresentation_of_compact_primitive
    (C'.restrict V hEV) p c hc hp'
  refine ⟨q.equiv, p.boundaryEquiv, hq, ?_, ?_, q.end_square⟩
  · intro x hx
    have hs := q.compact_square ⟨x, hDU hx⟩ hx
    change q.equiv (C.inclusion.map x) = C'.inclusion.map (p.extensionEquiv ⟨x, hDU hx⟩).val at hs
    rwa [he] at hs
  · intro x
    exact (he ((D.domain.restrict U hDU).boundaryInclusion.map x)).symm.trans
      (congrArg Subtype.val (p.boundary_square x))

/-- Scale one gives the primitive-preserving ambient map required for a
strict completion identification, retaining the prescribed compact map
and its induced boundary map. -/
theorem exists_strictEquiv_of_compactDiffeomorph {d : ℕ} {D E : LiouvilleDomain d}
    (C : Completion D) (C' : Completion E)
    (h : CompactDomainDiffeomorph D.domain E.domain)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.map E.liouville.primitive x =
        D.liouville.primitive x) :
    ∃ (e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
      (b : D.domain.boundary.SmoothEquiv E.domain.boundary),
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        C.ambient.primitive ∧
      (∀ x ∈ D.domain.carrier,
        e (C.inclusion.map x) = C'.inclusion.map (h.map x)) ∧
      (∀ x, h.map (D.domain.boundaryInclusion.map x) =
        E.domain.boundaryInclusion.map (b x)) ∧
      (∀ x r, 0 ≤ r → e (C.endMap (x, r)) = C'.endMap (b x, r)) := by
  simpa only [one_smul] using C.exists_scaledEquiv_of_compactDiffeomorph C' h 1
    (by norm_num) (by simpa only [one_smul] using hp)

end Completion
end FsFltz.Geometry
