import FsFltz.Geometry.CompletionMapUniqueness

/-!
# Joint map regularity from compact and cylindrical extension germs

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:chain`,
163–199, and `sec:lean`, 788–814. Compact-interior inverse charts and
two-sided end inverse charts prove joint smoothness of the actual glued
map, including the completion seam and both parameter endpoints.

The real-parameter extensions are maps, with no diffeomorphism or
Liouville law imposed outside the closed parameter interval. Their
agreement on a genuine open collar is explicit input. Producing such
coherent germs for independently prescribed moving completed families
remains a separate foundation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.Completion
open SmoothManifold

variable {d : ℕ} {D E : LiouvilleDomain d}

/-- Raw compact/end gluing of real-parameter map extensions. No geometric
law or smoothness of this completed map is part of its definition. -/
def extendedMap (C : Completion D) (C' : Completion E)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point)
    (t : ℝ) (z : C.ambient.manifold.Point) : C'.ambient.manifold.Point :=
  if hz : z ∈ C.inclusion.map '' D.domain.carrier then
    C'.inclusion.map (g t hz.choose)
  else
    let p := (show ∃ p : D.domain.boundary.Point × ℝ,
        0 ≤ p.2 ∧ C.endMap p = z from by
      have hc : z ∈ C.inclusion.map '' D.domain.carrier ∪
          C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by rw [C.covering]; trivial
      obtain ⟨p, hp, he⟩ := hc.resolve_left hz
      exact ⟨p, hp.2, he⟩).choose
    C'.endMap (b t p.1, p.2)

@[simp] theorem extendedMap_compact (C : Completion D) (C' : Completion E)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point)
    (t : ℝ) (x : D.domain.extension.Point) (hx : x ∈ D.domain.carrier) :
    C.extendedMap C' g b t (C.inclusion.map x) = C'.inclusion.map (g t x) := by
  have hz : C.inclusion.map x ∈ C.inclusion.map '' D.domain.carrier := ⟨x, hx, rfl⟩
  simp only [extendedMap, dite_eq_left hz]
  rw [C.inclusion.embedding.injective hz.choose_spec.2]

/-- The actual gluing is cylindrical on the whole open collar. Inward
points are covered by the compact piece; outward points use the cylinder. -/
theorem extendedMap_end_of_collar (C : Completion D) (C' : Completion E)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point)
    (t : ℝ) (δ : ℝ)
    (hcollar : ∀ q : D.domain.boundary.Point × ℝ, -δ < q.2 →
      ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
        C'.inclusion.map (g t x) = C'.endMap (b t q.1, q.2))
    (q : D.domain.boundary.Point × ℝ) (hq : -δ < q.2) :
    C.extendedMap C' g b t (C.endMap q) = C'.endMap (b t q.1, q.2) := by
  by_cases hz : C.endMap q ∈ C.inclusion.map '' D.domain.carrier
  · obtain ⟨x, hx, he⟩ := hz
    rw [← he, C.extendedMap_compact C' g b t x hx]
    exact hcollar q hq x hx he
  · simp only [extendedMap, dite_eq_right hz]
    congr 1
    have he := (show ∃ p : D.domain.boundary.Point × ℝ,
        0 ≤ p.2 ∧ C.endMap p = C.endMap q from by
      have hc : C.endMap q ∈ C.inclusion.map '' D.domain.carrier ∪
          C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by rw [C.covering]; trivial
      obtain ⟨p, hp, he⟩ := hc.resolve_left hz
      exact ⟨p, hp.2, he⟩).choose_spec.2
    exact congrArg (fun p : D.domain.boundary.Point × ℝ => (b t p.1, p.2))
      (C.endMap_injective he)

/-- Joint smoothness follows from the actual compact and open-collar
formulas. The completed map and its joint regularity are outputs. -/
theorem contMDiffOn_extendedMap (C : Completion D) (C' : Completion E)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point)
    (V : TopologicalSpace.Opens ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => g p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hb : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1)))
      𝓘(ℝ, Model (d - 1)) ∞
      (fun p : ℝ × D.domain.boundary.Point => b p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hcollar : ∀ t ∈ V, ∀ q : D.domain.boundary.Point × ℝ, -δ < q.2 →
      ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
        C'.inclusion.map (g t x) = C'.endMap (b t q.1, q.2)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × C.ambient.manifold.Point => C.extendedMap C' g b p.1 p.2)
      ((V : Set ℝ) ×ˢ univ) := by
  rintro ⟨t, z⟩ ⟨ht, _⟩
  apply ContMDiffAt.contMDiffWithinAt
  by_cases hz : z ∈ C.inclusion.map '' interior D.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hz
    let l := C.inclusion_isLocalDiffeomorph x
    have hi := l.localInverse_contMDiffAt
    have hix : l.localInverse (C.inclusion.map x) = x :=
      l.localInverse_left_inv l.localInverse_mem_target
    have ha : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × C.ambient.manifold.Point => (p.1, l.localInverse p.2))
        (t, C.inclusion.map x) :=
      contMDiffAt_fst.prodMk (hi.comp (t, C.inclusion.map x) contMDiffAt_snd)
    have hsm := C'.inclusion.map.contMDiff.contMDiffAt.comp (t, C.inclusion.map x)
      ((hg.contMDiffAt ((V.isOpen.prod isOpen_univ).mem_nhds
        ⟨ht, mem_univ _⟩)).comp _ ha)
    apply hsm.congr_of_eventuallyEq
    have hn : ∀ᶠ p : ℝ × C.ambient.manifold.Point in 𝓝 (t, C.inclusion.map x),
        l.localInverse p.2 ∈ interior D.domain.carrier :=
      ha.snd.continuousAt.preimage_mem_nhds
        (by simpa only [hix] using isOpen_interior.mem_nhds hx)
    have he : ∀ᶠ p : ℝ × C.ambient.manifold.Point in 𝓝 (t, C.inclusion.map x),
        C.inclusion.map (l.localInverse p.2) = p.2 :=
      l.localInverse_eventuallyEq_right.comp_tendsto continuousAt_snd
    filter_upwards [hn, he] with p hp he
    change C.extendedMap C' g b p.1 p.2 = C'.inclusion.map (g p.1 (l.localInverse p.2))
    simpa only [he] using
      C.extendedMap_compact C' g b p.1 _ (interior_subset hp)
  · have hz' : z ∈ Set.range (fun p : D.domain.boundary.Point × Ici (0 : ℝ) =>
        C.endMap (p.1, p.2)) := by rw [C.range_nonnegative_endMap]; exact hz
    obtain ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ := hz'
    let l := C.endMap_isLocalDiffeomorph (x, r)
    have hi := l.localInverse_contMDiffAt
    have hip : l.localInverse (C.endMap (x, r)) = (x, r) :=
      l.localInverse_left_inv l.localInverse_mem_target
    have hpair : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1))) ∞
        (fun p : ℝ × C.ambient.manifold.Point => (p.1, (l.localInverse p.2).1))
        (t, C.endMap (x, r)) :=
      contMDiffAt_fst.prodMk ((hi.comp (t, C.endMap (x, r)) contMDiffAt_snd).fst)
    have hboundary := (hb.contMDiffAt ((V.isOpen.prod isOpen_univ).mem_nhds
        ⟨ht, mem_univ _⟩)).comp _ hpair
    have hcyl := hboundary.prodMk ((hi.comp (t, C.endMap (x, r)) contMDiffAt_snd).snd)
    have hsm := C'.smooth_endMap.contMDiffAt.comp (t, C.endMap (x, r)) hcyl
    apply hsm.congr_of_eventuallyEq
    have hn : ∀ᶠ p : ℝ × C.ambient.manifold.Point in 𝓝 (t, C.endMap (x, r)),
        p.1 ∈ V ∧ -δ < (l.localInverse p.2).2 := by
      have htime : ∀ᶠ p : ℝ × C.ambient.manifold.Point in 𝓝 (t, C.endMap (x, r)),
          p.1 ∈ V := continuousAt_fst.preimage_mem_nhds (V.isOpen.mem_nhds ht)
      have hrad : ∀ᶠ p : ℝ × C.ambient.manifold.Point in 𝓝 (t, C.endMap (x, r)),
          -δ < (l.localInverse p.2).2 :=
        hcyl.continuousAt.snd.preimage_mem_nhds
          (isOpen_Ioi.mem_nhds (by
            simp only [Function.comp_apply, hip]
            exact lt_of_lt_of_le (neg_lt_zero.mpr hδ) hr))
      exact htime.and hrad
    have he : ∀ᶠ p : ℝ × C.ambient.manifold.Point in 𝓝 (t, C.endMap (x, r)),
        C.endMap (l.localInverse p.2) = p.2 :=
      l.localInverse_eventuallyEq_right.comp_tendsto continuousAt_snd
    filter_upwards [hn, he] with p hp he
    change C.extendedMap C' g b p.1 p.2 =
      C'.endMap (b p.1 (l.localInverse p.2).1, (l.localInverse p.2).2)
    simpa only [he] using
      C.extendedMap_end_of_collar C' g b p.1 δ (hcollar p.1 hp.1)
        (l.localInverse p.2) hp.2

/- The raw completed extension retains any prescribed interval map with
the same compact and outward-cylinder formulas. -/
theorem extendedMap_eq_of_squares (C : Completion D) (C' : Completion E)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point)
    (t : ℝ) (f : C.ambient.manifold.Point → C'.ambient.manifold.Point)
    (hcompact : ∀ x ∈ D.domain.carrier,
      f (C.inclusion.map x) = C'.inclusion.map (g t x))
    (hend : ∀ x r, 0 ≤ r → f (C.endMap (x, r)) = C'.endMap (b t x, r)) :
    C.extendedMap C' g b t = f := by
  funext z
  by_cases hz : z ∈ C.inclusion.map '' D.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hz
    exact (C.extendedMap_compact C' g b t x hx).trans (hcompact x hx).symm
  · simp only [extendedMap, dite_eq_right hz]
    let hp : ∃ p : D.domain.boundary.Point × ℝ, 0 ≤ p.2 ∧ C.endMap p = z := by
      have hc : z ∈ C.inclusion.map '' D.domain.carrier ∪
          C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by rw [C.covering]; trivial
      obtain ⟨p, hp, he⟩ := hc.resolve_left hz
      exact ⟨p, hp.2, he⟩
    exact (hend hp.choose.1 hp.choose.2 hp.choose_spec.1).symm.trans
      (congrArg f hp.choose_spec.2)

/-- The same prescribed interval maps acquire an actual smooth extension
from compact and two-sided cylindrical extension germs. No completed-map
regularity is assumed, and the equality covers both endpoints literally. -/
theorem isSmoothIntervalMapFamily_of_compact_end_extensions
    (C : Completion D) (C' : Completion E)
    (f : Parameter → C.ambient.manifold.Point → C'.ambient.manifold.Point)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point)
    (V : TopologicalSpace.Opens ℝ) (hIV : parameterInterval ⊆ V)
    (δ : ℝ) (hδ : 0 < δ)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => g p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hb : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1)))
      𝓘(ℝ, Model (d - 1)) ∞
      (fun p : ℝ × D.domain.boundary.Point => b p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hcollar : ∀ t ∈ V, ∀ q : D.domain.boundary.Point × ℝ, -δ < q.2 →
      ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
        C'.inclusion.map (g t x) = C'.endMap (b t q.1, q.2))
    (hcompact : ∀ t x, x ∈ D.domain.carrier →
      f t (C.inclusion.map x) = C'.inclusion.map (g t.val x))
    (hend : ∀ t x r, 0 ≤ r →
      f t (C.endMap (x, r)) = C'.endMap (b t.val x, r)) :
    C.ambient.manifold.IsSmoothIntervalMapFamily C'.ambient.manifold f := by
  refine ⟨C.extendedMap C' g b, ⟨(V : Set ℝ) ×ˢ univ,
    V.isOpen.prod isOpen_univ, ?_, C.contMDiffOn_extendedMap C' g b V δ hδ hg hb hcollar⟩, ?_⟩
  · exact prod_mono hIV Subset.rfl
  · intro t
    exact C.extendedMap_eq_of_squares C' g b t.val (f t) (hcompact t) (hend t)

/-- Carrier primitive preservation constructs the strict maps themselves.
Coherent compact and cylindrical germs in each direction then prove joint
smoothness of those same maps and their inverses. The real extensions need
not be strict or inverse to one another outside the actual interval. -/
theorem exists_strictEquivFamily_of_compact_primitive_extensions
    (C : Completion D) (C' : Completion E)
    (h : Parameter → DomainPresentationEquiv D.domain E.domain)
    (hp : ∀ t x, x ∈ D.domain.carrier →
      D.domain.extension.pullback E.domain.extension (h t).extensionEquiv
        E.liouville.primitive x = D.liouville.primitive x)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (gi : ℝ → E.domain.extension.Point → D.domain.extension.Point)
    (b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point)
    (bi : ℝ → E.domain.boundary.Point → D.domain.boundary.Point)
    (V : TopologicalSpace.Opens ℝ) (hIV : parameterInterval ⊆ V)
    (δ : ℝ) (hδ : 0 < δ)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => g p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hgi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × E.domain.extension.Point => gi p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hb : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1)))
      𝓘(ℝ, Model (d - 1)) ∞
      (fun p : ℝ × D.domain.boundary.Point => b p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hbi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1)))
      𝓘(ℝ, Model (d - 1)) ∞
      (fun p : ℝ × E.domain.boundary.Point => bi p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hgval : ∀ t x, x ∈ D.domain.carrier → g t.val x = (h t).extensionEquiv x)
    (hgival : ∀ t y, y ∈ E.domain.carrier → gi t.val y = (h t).extensionEquiv.symm y)
    (hbval : ∀ t x, b t.val x = (h t).boundaryEquiv x)
    (hbival : ∀ t y, bi t.val y = (h t).boundaryEquiv.symm y)
    (hcollar : ∀ t ∈ V, ∀ q : D.domain.boundary.Point × ℝ, -δ < q.2 →
      ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
        C'.inclusion.map (g t x) = C'.endMap (b t q.1, q.2))
    (hicollar : ∀ t ∈ V, ∀ q : E.domain.boundary.Point × ℝ, -δ < q.2 →
      ∀ y ∈ E.domain.carrier, C'.inclusion.map y = C'.endMap q →
        C.inclusion.map (gi t y) = C.endMap (bi t q.1, q.2)) :
    ∃ e : Parameter → C.ambient.manifold.SmoothEquiv C'.ambient.manifold,
      C.ambient.manifold.IsSmoothIntervalMapFamily C'.ambient.manifold (fun t => e t) ∧
      C'.ambient.manifold.IsSmoothIntervalMapFamily C.ambient.manifold (fun t => (e t).symm) ∧
      (∀ t, C.ambient.manifold.pullback C'.ambient.manifold (e t) C'.ambient.primitive =
        C.ambient.primitive) ∧
      (∀ t x, x ∈ D.domain.carrier →
        e t (C.inclusion.map x) = C'.inclusion.map ((h t).extensionEquiv x)) ∧
      (∀ t y, y ∈ E.domain.carrier →
        (e t).symm (C'.inclusion.map y) = C.inclusion.map ((h t).extensionEquiv.symm y)) ∧
      (∀ t x r, e t (C.endMap (x, r)) = C'.endMap ((h t).boundaryEquiv x, r)) ∧
      (∀ t y r, (e t).symm (C'.endMap (y, r)) = C.endMap ((h t).boundaryEquiv.symm y, r)) := by
  have hex (t : Parameter) := C.exists_scaledPresentation_of_compact_primitive C'
    (h t) 1 (by norm_num) (by simpa only [one_smul] using hp t)
  choose p hpull using hex
  let e := fun t => (p t).equiv
  have hprim (t : Parameter) : C.ambient.manifold.pullback C'.ambient.manifold
      (e t) C'.ambient.primitive = C.ambient.primitive := by
    simpa only [one_smul] using hpull t
  have hcomp (t : Parameter) (x) (hx : x ∈ D.domain.carrier) :
      e t (C.inclusion.map x) = C'.inclusion.map ((h t).extensionEquiv x) :=
    (p t).compact_square x hx
  have hcompinv (t : Parameter) (y) (hy : y ∈ E.domain.carrier) :
      (e t).symm (C'.inclusion.map y) = C.inclusion.map ((h t).extensionEquiv.symm y) := by
    have hs := congrArg (e t).symm (hcomp t ((h t).extensionEquiv.symm y)
      (((h t).mem_carrier_iff _).mp (by simpa only [(h t).extensionEquiv.apply_symm_apply] using hy)))
    simpa only [(e t).symm_apply_apply, (h t).extensionEquiv.apply_symm_apply] using hs.symm
  have hend (t : Parameter) (x) (r) :
      e t (C.endMap (x, r)) = C'.endMap ((h t).boundaryEquiv x, r) :=
    C.end_square_of_scaled_primitive C' (h t) (e t) 1
      (by simpa only [one_smul] using hprim t) (hcomp t) x r
  have hendinv (t : Parameter) (y) (r) :
      (e t).symm (C'.endMap (y, r)) = C.endMap ((h t).boundaryEquiv.symm y, r) := by
    have hs := congrArg (e t).symm (hend t ((h t).boundaryEquiv.symm y) r)
    simpa only [(e t).symm_apply_apply, (h t).boundaryEquiv.apply_symm_apply] using hs.symm
  refine ⟨e, ?_, ?_, hprim, hcomp, hcompinv, hend, hendinv⟩
  · apply C.isSmoothIntervalMapFamily_of_compact_end_extensions C' (fun t => e t)
      g b V hIV δ hδ hg hb hcollar
    · intro t x hx
      rw [hgval t x hx]
      exact hcomp t x hx
    · intro t x r _
      rw [hbval]
      exact hend t x r
  · apply C'.isSmoothIntervalMapFamily_of_compact_end_extensions C (fun t => (e t).symm)
      gi bi V hIV δ hδ hgi hbi hicollar
    · intro t y hy
      rw [hgival t y hy]
      exact hcompinv t y hy
    · intro t y r _
      rw [hbival]
      exact hendinv t y r

end FsFltz.Geometry.Completion
