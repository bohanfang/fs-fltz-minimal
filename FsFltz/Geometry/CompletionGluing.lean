import FsFltz.Geometry.Deformation
import FsFltz.Geometry.BoundarySmooth

/-!
# Gluing collar-adapted completion presentations

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. A compact presentation determines a map on the compact pieces and
its boundary map determines a map on the nonnegative cylinders. The two
formulas agree at radius zero. Agreement with the same formula on an open
collar makes the glued map smooth; the inverse is obtained by the inverse
compact presentation. This constructs a completed presentation from local
collar compatibility, not from a supplied completed diffeomorphism.

Constructing collar-adapted presentations for arbitrary smooth families
remains a separate foundation.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace DomainPresentationEquiv

variable {d : ℕ} {D E : CompactDomain d}

lemma mem_carrier_iff (h : DomainPresentationEquiv D E) (x : D.extension.Point) :
    h.extensionEquiv x ∈ E.carrier ↔ x ∈ D.carrier := by
  rw [← h.carrier]
  exact h.extensionEquiv.injective.mem_set_image

def symm (h : DomainPresentationEquiv D E) : DomainPresentationEquiv E D where
  extensionEquiv := h.extensionEquiv.symm
  carrier := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h.mem_carrier_iff _).mp (by simpa using hy)
    · intro hx
      exact ⟨h.extensionEquiv x, (h.mem_carrier_iff x).mpr hx, by simp⟩
  boundaryEquiv := h.boundaryEquiv.symm
  boundary_square := by
    intro x
    apply h.extensionEquiv.injective
    simpa using (h.boundary_square (h.boundaryEquiv.symm x)).symm

@[simp] theorem symm_symm (h : DomainPresentationEquiv D E) : h.symm.symm = h := by
  cases h
  rfl

end DomainPresentationEquiv

namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d}

private theorem end_exists_of_not_compact (C : Completion D)
    (z : C.ambient.manifold.Point) (hz : z ∉ C.inclusion.map '' D.domain.carrier) :
    ∃ p : D.domain.boundary.Point × ℝ, 0 ≤ p.2 ∧ C.endMap p = z := by
  have hc : z ∈ C.inclusion.map '' D.domain.carrier ∪
      C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by rw [C.covering]; trivial
  obtain ⟨p, hp, he⟩ := hc.resolve_left hz
  exact ⟨p, hp.2, he⟩

/-- The set-theoretic gluing of the two prescribed formulas. -/
def presentationMap (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain)
    (z : C.ambient.manifold.Point) : C'.ambient.manifold.Point := by
  classical
  exact if hz : z ∈ C.inclusion.map '' D.domain.carrier then
    C'.inclusion.map (h.extensionEquiv hz.choose)
  else
    let p := (C.end_exists_of_not_compact z hz).choose
    C'.endMap (h.boundaryEquiv p.1, p.2)

@[simp] theorem presentationMap_compact (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain) (x : D.domain.extension.Point)
    (hx : x ∈ D.domain.carrier) :
    C.presentationMap C' h (C.inclusion.map x) = C'.inclusion.map (h.extensionEquiv x) := by
  classical
  have hz : C.inclusion.map x ∈ C.inclusion.map '' D.domain.carrier := ⟨x, hx, rfl⟩
  simp only [presentationMap, dite_eq_left hz]
  rw [C.inclusion.embedding.injective hz.choose_spec.2]

@[simp] theorem presentationMap_end (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain) (x : D.domain.boundary.Point)
    (r : ℝ) (hr : 0 ≤ r) :
    C.presentationMap C' h (C.endMap (x, r)) = C'.endMap (h.boundaryEquiv x, r) := by
  classical
  rcases eq_or_lt_of_le hr with hr | hr
  · subst r
    rw [C.endMap_zero, C'.endMap_zero, C.presentationMap_compact]
    · rw [h.boundary_square]
    · apply D.domain.compact.isClosed.frontier_subset
      rw [← D.domain.boundary_range]
      exact ⟨x, rfl⟩
  · have hz := C.overlap x r hr
    simp only [presentationMap, dite_eq_right hz]
    have he := (C.end_exists_of_not_compact (C.endMap (x, r)) hz).choose_spec.2
    rw [C.endMap_injective he]

private theorem presentationMap_leftInverse (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain) :
    Function.LeftInverse (C'.presentationMap C h.symm) (C.presentationMap C' h) := by
  intro z
  by_cases hz : z ∈ C.inclusion.map '' D.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hz
    rw [C.presentationMap_compact C' h x hx,
      C'.presentationMap_compact C h.symm _ ((h.mem_carrier_iff x).mpr hx)]
    simp [DomainPresentationEquiv.symm]
  · obtain ⟨⟨x, r⟩, hr, rfl⟩ := C.end_exists_of_not_compact z hz
    rw [C.presentationMap_end C' h x r hr,
      C'.presentationMap_end C h.symm _ r hr]
    simp [DomainPresentationEquiv.symm]

/-- Negative cylinder points lie in the compact piece, a consequence of the
covering and injectivity equations for an already supplied completion. -/
theorem endMap_mem_compact_of_neg (C : Completion D)
    (p : D.domain.boundary.Point × ℝ) (hp : p.2 < 0) :
    C.endMap p ∈ C.inclusion.map '' D.domain.carrier := by
  by_contra hn
  obtain ⟨q, hq, he⟩ := C.end_exists_of_not_compact (C.endMap p) hn
  have hqp := C.endMap_injective he
  exact (not_le_of_gt hp) (hqp ▸ hq)

/-- Local agreement with the cylindrical formula across the seam proves
smoothness of the glued function; smoothness of that function is not assumed. -/
theorem contMDiff_presentationMap_of_collar (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain)
    (U : Set (D.domain.boundary.Point × ℝ)) (hU : IsOpen U)
    (hpos : univ ×ˢ Ici (0 : ℝ) ⊆ U)
    (hcollar : ∀ p ∈ U, ∀ x ∈ D.domain.carrier,
      C.inclusion.map x = C.endMap p →
      C'.inclusion.map (h.extensionEquiv x) = C'.endMap (h.boundaryEquiv p.1, p.2)) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (C.presentationMap C' h) := by
  have hend (p) (hp : p ∈ U) : C.presentationMap C' h (C.endMap p) =
      C'.endMap (h.boundaryEquiv p.1, p.2) := by
    by_cases hr : 0 ≤ p.2
    · exact C.presentationMap_end C' h p.1 p.2 hr
    · obtain ⟨x, hx, he⟩ := C.endMap_mem_compact_of_neg p (lt_of_not_ge hr)
      rw [← he, C.presentationMap_compact C' h x hx]
      exact hcollar p hp x hx he
  intro z
  by_cases hz : z ∈ C.inclusion.map '' interior D.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hz
    have hloc : IsLocalDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ C.inclusion.map := by
      apply isLocalDiffeomorph_of_bijective_mfderiv_manifold C.inclusion.map.contMDiff
      intro y
      exact ⟨C.inclusion.immersion y,
        LinearMap.injective_iff_surjective.mp (C.inclusion.immersion y)⟩
    let l := hloc x
    have hi := l.localInverse_contMDiffAt
    have hix : l.localInverse (C.inclusion.map x) = x :=
      l.localInverse_left_inv l.localInverse_mem_target
    have hsm := C'.inclusion.map.contMDiff.comp
      (h.extensionEquiv.contMDiff)
    apply ((hsm _).comp _ hi).congr_of_eventuallyEq
    have hn : ∀ᶠ y in 𝓝 (C.inclusion.map x), l.localInverse y ∈ interior D.domain.carrier :=
      hi.continuousAt.preimage_mem_nhds (by simpa only [hix] using isOpen_interior.mem_nhds hx)
    filter_upwards [hn, l.localInverse_eventuallyEq_right] with y hy he
    change C.inclusion.map (l.localInverse y) = y at he
    change C.presentationMap C' h y = C'.inclusion.map (h.extensionEquiv (l.localInverse y))
    simpa only [he] using C.presentationMap_compact C' h _ (interior_subset hy)
  · have hz' : z ∈ Set.range (fun p : D.domain.boundary.Point × Ici (0 : ℝ) =>
        C.endMap (p.1, p.2)) := by rw [C.range_nonnegative_endMap]; exact hz
    obtain ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ := hz'
    let l := C.endMap_isLocalDiffeomorph (x, r)
    have hi := l.localInverse_contMDiffAt
    have hip : l.localInverse (C.endMap (x, r)) = (x, r) :=
      l.localInverse_left_inv l.localInverse_mem_target
    have hpair : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : D.domain.boundary.Point × ℝ => (h.boundaryEquiv p.1, p.2)) :=
      (h.boundaryEquiv.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    have hsm := C'.smooth_endMap.comp hpair
    apply ((hsm _).comp _ hi).congr_of_eventuallyEq
    have hn : ∀ᶠ y in 𝓝 (C.endMap (x, r)), l.localInverse y ∈ U :=
      hi.continuousAt.preimage_mem_nhds
        (by simpa only [hip] using hU.mem_nhds (hpos ⟨mem_univ x, hr⟩))
    filter_upwards [hn, l.localInverse_eventuallyEq_right] with y hy he
    change C.endMap (l.localInverse y) = y at he
    change C.presentationMap C' h y =
      C'.endMap (h.boundaryEquiv (l.localInverse y).1, (l.localInverse y).2)
    simpa only [he] using hend _ hy

/-- A collar-adapted compact presentation extends to the existing smooth
completion-presentation structure. Only the forward local collar agreement
is required; inverse compatibility follows from injectivity and covering. -/
def presentationEquivOfCollar (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain)
    (U : Set (D.domain.boundary.Point × ℝ)) (hU : IsOpen U)
    (hpos : univ ×ˢ Ici (0 : ℝ) ⊆ U)
    (hcollar : ∀ p ∈ U, ∀ x ∈ D.domain.carrier,
      C.inclusion.map x = C.endMap p →
      C'.inclusion.map (h.extensionEquiv x) = C'.endMap (h.boundaryEquiv p.1, p.2)) :
    CompletionPresentationEquiv C C' h := by
  let b : (D.domain.boundary.Point × ℝ) ≃ₜ (E.domain.boundary.Point × ℝ) :=
    h.boundaryEquiv.toHomeomorph.prodCongr (Homeomorph.refl ℝ)
  have hU' : IsOpen (b '' U) := b.isOpenMap U hU
  have hpos' : univ ×ˢ Ici (0 : ℝ) ⊆ b '' U := by
    intro p hp
    exact ⟨b.symm p, hpos ⟨mem_univ _, hp.2⟩, b.apply_symm_apply p⟩
  have hc' : ∀ p ∈ b '' U, ∀ y ∈ E.domain.carrier,
      C'.inclusion.map y = C'.endMap p →
      C.inclusion.map (h.symm.extensionEquiv y) =
        C.endMap (h.symm.boundaryEquiv p.1, p.2) := by
    rintro _ ⟨p, hp, rfl⟩ y hy he
    have hr : p.2 ≤ 0 := by
      by_contra hn
      exact C'.overlap (h.boundaryEquiv p.1) p.2 (lt_of_not_ge hn) ⟨y, hy, he⟩
    have hc : C.endMap p ∈ C.inclusion.map '' D.domain.carrier := by
      rcases lt_or_eq_of_le hr with hr | hr
      · exact C.endMap_mem_compact_of_neg p hr
      · rcases p with ⟨x, r⟩
        dsimp at hr
        subst r
        refine ⟨D.domain.boundaryInclusion.map x, ?_, (C.endMap_zero x).symm⟩
        apply D.domain.compact.isClosed.frontier_subset
        rw [← D.domain.boundary_range]
        exact ⟨x, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hc
    have hxy : h.extensionEquiv x = y :=
      C'.inclusion.embedding.injective ((hcollar p hp x hx hxe).trans he.symm)
    have hyx : h.extensionEquiv.symm y = x := by rw [← hxy]; simp
    change C.inclusion.map (h.extensionEquiv.symm y) =
      C.endMap (h.boundaryEquiv.symm (h.boundaryEquiv p.1), p.2)
    simpa only [hyx, Diffeomorph.symm_apply_apply] using hxe
  let f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold :=
    { toFun := C.presentationMap C' h
      invFun := C'.presentationMap C h.symm
      left_inv := C.presentationMap_leftInverse C' h
      right_inv := by
        intro y
        simpa only [DomainPresentationEquiv.symm_symm] using
          C'.presentationMap_leftInverse C h.symm y
      contMDiff_toFun := C.contMDiff_presentationMap_of_collar C' h U hU hpos hcollar
      contMDiff_invFun := C'.contMDiff_presentationMap_of_collar C h.symm
        (b '' U) hU' hpos' hc' }
  exact ⟨f, C.presentationMap_compact C' h, C.presentationMap_end C' h⟩

/-- The compact and cylindrical equations determine the completed map
uniquely, so the gluing is independent of the chosen collar neighborhood. -/
theorem presentationEquiv_unique (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain)
    (f g : CompletionPresentationEquiv C C' h) : f.equiv = g.equiv := by
  apply Diffeomorph.ext
  intro z
  by_cases hz : z ∈ C.inclusion.map '' D.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hz
    rw [f.compact_square x hx, g.compact_square x hx]
  · obtain ⟨⟨x, r⟩, hr, rfl⟩ := C.end_exists_of_not_compact z hz
    rw [f.end_square x r hr, g.end_square x r hr]

end Completion
end FsFltz.Geometry
