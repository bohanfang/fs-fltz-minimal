import FsFltz.Geometry.MaslovSectionCompactDetection
import FsFltz.Geometry.TailoringStrictAmbientComparison

/-!
# Compact detection on any actual completion

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and
`geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2089.
The constructed collar comparison transports the smooth compression to
the supplied completion, retaining its actual compact inclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.Completion
open SmoothManifold

theorem exists_compactCompression {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (hne : D.domain.carrier.Nonempty) :
    ∃ H : ℝ → C.ambient.manifold.Point → C.ambient.manifold.Point,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × C.ambient.manifold.Point => H p.1 p.2) ∧
      (∀ x, H 0 x = x) ∧
      ∀ x, H 1 x ∈ C.inclusion.map '' D.domain.carrier := by
  let B := D.flowCollar
  obtain ⟨h, _hproj, hp⟩ := B.exists_originalCompactComparison hne
  obtain ⟨e, _b, _he, hc, _hb, _hend⟩ :=
    C.exists_strictEquiv_of_compactDiffeomorph B.cylindricalCompletion h hp
  let H := fun t x => e.symm (B.compactCompression t (e x))
  refine ⟨H, ?_, ?_, ?_⟩
  · exact e.symm.contMDiff.comp (B.compactCompression_smooth.comp
      (contMDiff_fst.prodMk (e.contMDiff.comp contMDiff_snd)))
  · intro x
    change e.symm (B.compactCompression 0 (e x)) = x
    rw [B.compactCompression_zero, e.symm_apply_apply]
  · intro x
    let z := B.compactCompression 1 (e x)
    have hz : z ∈ B.localizedDomain.domain.carrier := B.compactCompression_one_mem (e x)
    refine ⟨h.inverse z, h.maps_target hz, ?_⟩
    apply e.injective
    change e (C.inclusion.map (h.inverse z)) = e (e.symm z)
    rw [hc _ (h.maps_target hz), h.right_inverse _ hz]
    exact (e.apply_symm_apply z).symm

/-- Equality of the actual compact tensor sections determines the grading
class on the supplied completion, with no prescribed collar presentation. -/
theorem maslovHomotopic_of_eq_on_compact {n : ℕ} {D : LiouvilleDomain (2 * n)}
    (C : Completion D) (hne : D.domain.carrier.Nonempty)
    (s r : MaslovRepresentative C.ambient.manifold
      (C.ambient.manifold.exteriorDerivative C.ambient.primitive))
    (he : ∀ x ∈ D.domain.carrier,
      r.tensor (C.inclusion.map x) = s.tensor (C.inclusion.map x)) :
    MaslovHomotopic s r := by
  obtain ⟨H, hH, hH0, hH1⟩ := C.exists_compactCompression hne
  apply s.homotopic_of_eq_on_compression r (C.inclusion.map '' D.domain.carrier)
    H hH hH0 hH1
  rintro _ ⟨x, hx, rfl⟩
  exact he x hx

end FsFltz.Geometry.Completion
