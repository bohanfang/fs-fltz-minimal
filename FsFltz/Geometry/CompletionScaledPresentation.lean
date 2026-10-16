import FsFltz.Geometry.CompactPrimitiveNaturality
import FsFltz.Geometry.CompletionCollarRecovery
import FsFltz.Geometry.CompletionLocalization
import FsFltz.Geometry.CompletionFamilyEquations

/-!
# Extending the prescribed constant-scale compact presentation

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 171–189; and `sec:lean`, lines 783–814.
The prescribed compact map transports the Liouville field by carrier-only
primitive naturality. Its image of the constructed inward collar is therefore
the target inward collar, by uniqueness for the actual completed flow.
This derives the collar square needed for gluing between two arbitrary
chosen completions. The resulting map retains the given compact and boundary
maps and preserves the cylinder radius.

Constant ambient scaling is foundational machinery; a permitted strict
ambient completion step uses scale one. Native compact-map presentation
correspondence and the geometric target remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d}

/-- Constant-scale primitive equality derives the negative-collar square
for the original compact presentation, without changing its map. -/
theorem exists_collar_square_of_scaled_compact_primitive
    (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain) (c : ℝ)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.extensionEquiv
        E.liouville.primitive x = c • D.liouville.primitive x) :
    ∃ U : Set (D.domain.boundary.Point × ℝ), IsOpen U ∧
      univ ×ˢ Ici (0 : ℝ) ⊆ U ∧
      ∀ p ∈ U, ∀ x ∈ D.domain.carrier,
        C.inclusion.map x = C.endMap p →
        C'.inclusion.map (h.extensionEquiv x) =
          C'.endMap (h.boundaryEquiv p.1, p.2) := by
  let k := D.flowCollar
  let f : D.domain.boundary.Point × ℝ → D.domain.extension.Point :=
    fun p => (k.map p).val
  have hfzero : ∀ x, f (x, 0) = D.domain.boundaryInclusion.map x := by
    intro x
    change (k.map (x, 0)).val = _
    rw [k.map_zero]
    rfl
  have hstrip {r : ℝ} (hr : r ∈ Ioc (-k.width) 0) :
      r ∈ Ioo (-k.width) k.width := ⟨hr.1, lt_of_le_of_lt hr.2 k.positive_width⟩
  have hfcarrier : ∀ x r, r ∈ Ioc (-k.width) 0 → f (x, r) ∈ D.domain.carrier := by
    intro x r hr
    exact (k.side x r (hstrip hr)).mpr hr.2
  have hfode : ∀ x r, r ∈ Ioc (-k.width) 0 →
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => f (x, s)) r
        ((1 : ℝ →L[ℝ] ℝ).smulRight (D.liouville.field (f (x, r)))) := by
    intro x r hr
    have hi := (D.domain.extension.restrictInclusion D.symplecticNeighborhood).map.contMDiff
    have hd := (hi.mdifferentiableAt (by simp)).hasMFDerivAt.comp r
      (k.solves x r (hstrip hr))
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro s
    change ℝ at s
    change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (Subtype.val : D.symplecticNeighborhood → D.domain.extension.Point) (k.map (x, r)))
        (s • D.neighborhoodStructure.field (k.map (x, r))) =
      s • D.liouville.field (f (x, r))
    erw [D.domain.extension.mfderiv_restrict_val D.symplecticNeighborhood]
    change s • D.neighborhoodStructure.field (k.map (x, r)) =
      s • D.liouville.field (f (x, r))
    exact congrArg (fun a : Model d => s • a)
      (D.neighborhood_field (k.map (x, r)) ((k.side x r (hstrip hr)).mpr hr.2))
  let g : E.domain.boundary.Point × ℝ → E.domain.extension.Point :=
    fun p => h.extensionEquiv (f (h.boundaryEquiv.symm p.1, p.2))
  have hgzero : ∀ y, g (y, 0) = E.domain.boundaryInclusion.map y := by
    intro y
    change h.extensionEquiv (f (h.boundaryEquiv.symm y, 0)) = _
    rw [hfzero, h.boundary_square, h.boundaryEquiv.apply_symm_apply]
  have hgcarrier : ∀ y r, r ∈ Ioc (-k.width) 0 → g (y, r) ∈ E.domain.carrier := by
    intro y r hr
    exact (h.mem_carrier_iff _).mpr (hfcarrier _ r hr)
  have hgode : ∀ y r, r ∈ Ioc (-k.width) 0 →
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => g (y, s)) r
        ((1 : ℝ →L[ℝ] ℝ).smulRight (E.liouville.field (g (y, r)))) := by
    intro y r hr
    have hd := (h.extensionEquiv.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt.comp r
      (hfode (h.boundaryEquiv.symm y) r hr)
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro s
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.extensionEquiv
      (f (h.boundaryEquiv.symm y, r))
      (s • D.liouville.field (f (h.boundaryEquiv.symm y, r))) =
      s • E.liouville.field (g (y, r))
    rw [map_smul, h.map_field_of_scaled_primitive c hp _ (hfcarrier _ r hr)]
  refine ⟨univ ×ˢ Ioi (-k.width), isOpen_univ.prod isOpen_Ioi, ?_, ?_⟩
  · intro p hp'
    exact ⟨mem_univ _, lt_of_lt_of_le (neg_lt_zero.mpr k.positive_width) hp'.2⟩
  · intro p hp' x hx he
    have hr : p.2 ≤ 0 := by
      by_contra hn
      exact C.overlap p.1 p.2 (lt_of_not_ge hn) ⟨x, hx, he⟩
    have hr' : p.2 ∈ Ioc (-k.width) 0 := ⟨hp'.2, hr⟩
    have hs := C.endMap_eq_inclusion_of_negative_collar f k.positive_width
      hfzero hfcarrier hfode p.1 p.2 hr'
    have hx' : x = f p := C.inclusion.embedding.injective (he.trans hs)
    rw [hx']
    have ht := C'.endMap_eq_inclusion_of_negative_collar g k.positive_width
      hgzero hgcarrier hgode (h.boundaryEquiv p.1) p.2 hr'
    simpa only [g, Diffeomorph.symm_apply_apply] using ht.symm

end Completion

/-- The glued completion map has the same constant scaling as the prescribed
compact map. The compact and end squares determine all completed coefficients. -/
theorem CompletionPresentationEquiv.primitive_scaled_of_compact_primitive
    {d : ℕ} {D E : LiouvilleDomain d}
    {C : Completion D} {C' : Completion E}
    {h : DomainPresentationEquiv D.domain E.domain}
    (p : CompletionPresentationEquiv C C' h) (c : ℝ)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.extensionEquiv
        E.liouville.primitive x = c • D.liouville.primitive x) :
    C.ambient.manifold.pullback C'.ambient.manifold p.equiv C'.ambient.primitive =
      c • C.ambient.primitive := by
  have hb : D.domain.boundaryForm
      (D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive) =
      c • D.domain.boundaryForm D.liouville.primitive := by
    funext x
    change (D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive
        (D.domain.boundaryInclusion.map x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) D.domain.boundaryInclusion.map x) = _
    rw [hp _ (D.domain.boundaryInclusion_mem_carrier x)]
    ext vs
    rfl
  apply (C.form_eq_pullback_of_compactInterior_end C' h p (c • C.ambient.primitive) ?_ ?_).symm
  · intro x hx
    rw [hp x (interior_subset hx)]
    have he := C.primitive_on_domain x (interior_subset hx)
    ext vs
    exact congrArg (fun A => c * A vs) he
  · intro x r hr v s
    have he := C.end_primitive x r v s
    rw [hb]
    change c * evalOne C.ambient.primitive (C.endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s)) =
      Real.exp r * (c * evalOne (D.domain.boundaryForm D.liouville.primitive) x v)
    rw [he]
    ring

namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d}

/-- A prescribed compact presentation satisfying positive constant-scale
primitive equality only on its carrier extends between arbitrary chosen
completions, with that same completed primitive equality. -/
theorem exists_scaledPresentation_of_compact_primitive
    (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain)
    (c : ℝ) (_hc : 0 < c)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.extensionEquiv
        E.liouville.primitive x = c • D.liouville.primitive x) :
    ∃ p : CompletionPresentationEquiv C C' h,
      C.ambient.manifold.pullback C'.ambient.manifold p.equiv
        C'.ambient.primitive = c • C.ambient.primitive := by
  obtain ⟨U, hU, hpos, hcollar⟩ :=
    C.exists_collar_square_of_scaled_compact_primitive C' h c hp
  let p := C.presentationEquivOfCollar C' h U hU hpos hcollar
  exact ⟨p, p.primitive_scaled_of_compact_primitive c hp⟩

end Completion
end FsFltz.Geometry
