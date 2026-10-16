import FsFltz.Geometry.IntrinsicNativeCompactMapFamilyGerms
import FsFltz.Geometry.PrescribedFamilyCollarInverse
import FsFltz.Geometry.CompletionPositiveEndMapFamily

/-!
# Joint regularity of prescribed moving completion comparisons

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. The same prescribed interval maps are retained
on the whole compact carrier and in their actual transported collar square.
The two original smooth transported primitive families produce the seam
germs; the cylindrical reference formula is used only at positive radii.
These ingredients imply joint regularity over the whole completion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.Completion
open SmoothManifold

/-- A whole-carrier compact extension and the actual transported collar
square imply joint smoothness of the same completed interval maps. Both
collar families and the inverse germ at the seam are derived from their
original transported primitives. No negative-radius reference end square
or completed comparison germ is an input. -/
theorem isSmoothIntervalMapFamily_of_compact_extension_prescribed_collar_square
    {d e : ℕ} {D : LiouvilleDomain d} {F : LiouvilleDomain e}
    (C : Completion D) (K : Completion F)
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (hα : C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive))
    (G : Parameter → LiouvilleDomain e) (K' : ∀ t, Completion (G t))
    (k : ∀ t, DomainPresentationEquiv F.domain (G t).domain)
    (q : ∀ t, CompletionPresentationEquiv K (K' t) (k t))
    (hprimitive : K.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      K.ambient.manifold.pullback (K' t).ambient.manifold (q t).equiv
        (K' t).ambient.primitive))
    (f : Parameter → C.ambient.manifold.Point → K.ambient.manifold.Point)
    (B : D.domain.boundary.SmoothEquiv F.domain.boundary)
    (W : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point))
    (hW : parameterInterval ×ˢ (C.inclusion.map '' D.domain.carrier) ⊆ (W : Set _))
    (g : W → K.ambient.manifold.Point)
    (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g)
    (heq : ∀ t x (_hx : x ∈ D.domain.carrier) (hp : (t.val, C.inclusion.map x) ∈ W),
      g ⟨(t.val, C.inclusion.map x), hp⟩ = f t (C.inclusion.map x))
    (hsquare : ∀ (t : Parameter) b r,
      f t ((p t).prescribedEndMap (b, r)) = (q t).prescribedEndMap (B b, r)) :
    C.ambient.manifold.IsSmoothIntervalMapFamily K.ambient.manifold f := by
  obtain ⟨δ, hδ, γ, hγ, heγ⟩ :=
    K.exists_prescribedFamily_collar_germ G K' k q hprimitive
  let β : ℝ → D.domain.boundary.Point × ℝ → K.ambient.manifold.Point :=
    fun s br => γ s (B br.1, br.2)
  have hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun z : ℝ × (D.domain.boundary.Point × ℝ) => β z.1 z.2) :=
    hγ.comp (contMDiff_fst.prodMk
      ((B.contMDiff.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
        (contMDiff_snd.comp contMDiff_snd)))
  have hseam := C.exists_familyMap_germ_on_end_of_collar_square E C' h p hα
    K.ambient.manifold f β hβ δ hδ (fun t b r hr =>
      (hsquare t b r).trans (heγ t (B b) r hr).symm)
  have hlocal : ∀ (t : Parameter) x, x ∈ D.domain.carrier →
      ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
        (t.val, C.inclusion.map x) ∈ U ∧ ∃ a : U → K.ambient.manifold.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a ∧
          ∀ s z (hz : (s.val, z) ∈ U), a ⟨(s.val, z), hz⟩ = f s z := by
    intro t x hx
    by_cases hi : C.inclusion.map x ∈ C.inclusion.map '' interior D.domain.carrier
    · exact C.exists_interiorMapFamily_germ_of_compact_extension
        K.ambient.manifold f W hW g hg heq t (C.inclusion.map x) hi
    · have hrange : C.inclusion.map x ∈ Set.range
          (fun br : D.domain.boundary.Point × Ici (0 : ℝ) => C.endMap (br.1, br.2)) := by
        rw [C.range_nonnegative_endMap]
        exact hi
      obtain ⟨⟨b, r⟩, hbr⟩ := hrange
      have hrzero : r.val = 0 := by
        apply le_antisymm _ r.property
        by_contra hn
        exact C.overlap b r (lt_of_not_ge hn) ⟨x, hx, hbr.symm⟩
      have hzero : C.endMap (b, 0) = C.inclusion.map x := by
        simpa only [hrzero] using hbr
      obtain ⟨U, htU, a, ha, hea⟩ := hseam t b
      exact ⟨U, hzero ▸ htU, a, ha, hea⟩
  let βpos : ℝ → D.domain.boundary.Point × ℝ → K.ambient.manifold.Point :=
    fun _ br => K.endMap (B br.1, br.2)
  have hβpos : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun z : ℝ × (D.domain.boundary.Point × ℝ) => βpos z.1 z.2) :=
    K.smooth_endMap.comp
      ((B.contMDiff.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
        (contMDiff_snd.comp contMDiff_snd))
  apply C.isSmoothIntervalMapFamily_of_compact_germs_positive_end
    K.ambient.manifold f βpos ⊤ (fun _ _ => mem_univ _) hβpos.contMDiffOn _ hlocal
  intro t b r hr
  have hh := hsquare t b r
  rw [(p t).prescribedEndMap_nonnegative b r (le_of_lt hr),
    (q t).prescribedEndMap_nonnegative (B b) r (le_of_lt hr)] at hh
  exact hh

end FsFltz.Geometry.Completion
