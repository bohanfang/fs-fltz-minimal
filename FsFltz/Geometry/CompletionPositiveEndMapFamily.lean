import FsFltz.Geometry.CompletionIntervalMapFamily

/-!
# Completion-map gluing from positive ends and genuine seam germs

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. A jointly smooth positive-radius cylindrical
formula and actual full-neighborhood compact germs extend the original
interval maps jointly over the whole completion. The compact germs cover
the seam; no negative-radius cylindrical formula or presentation identity
is assumed or inferred.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.Completion
open SmoothManifold

variable {d : ℕ} {D : LiouvilleDomain d}

/-- Genuine neighborhoods of all compact points, including the seam,
and a cylindrical formula smooth and exact only at positive radii produce
joint smoothness of those same completed interval maps. The short interval
from radius zero to one half is covered by the supplied seam germs and the
positive formula before the far end is retained by relative gluing. -/
theorem isSmoothIntervalMapFamily_of_compact_germs_positive_end {e : ℕ}
    (C : Completion D) (N : SmoothManifold e)
    (f : Parameter → C.ambient.manifold.Point → N.Point)
    (β : ℝ → D.domain.boundary.Point × ℝ → N.Point)
    (V : TopologicalSpace.Opens ℝ) (hIV : parameterInterval ⊆ V)
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × (D.domain.boundary.Point × ℝ) => β p.1 p.2)
      ((V : Set ℝ) ×ˢ (univ ×ˢ Ioi (0 : ℝ))))
    (hend : ∀ t x r, 0 < r → f t (C.endMap (x, r)) = β t.val (x, r))
    (hlocal : ∀ (t : Parameter) x, x ∈ D.domain.carrier →
      ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
        (t.val, C.inclusion.map x) ∈ U ∧ ∃ g : U → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g ∧
          ∀ s z (hz : (s.val, z) ∈ U), g ⟨(s.val, z), hz⟩ = f s z) :
    C.ambient.manifold.IsSmoothIntervalMapFamily N f := by
  let A : Set (ℝ × C.ambient.manifold.Point) := parameterInterval ×ˢ univ
  let f₀ : A → N.Point := fun p => f ⟨p.val.1, p.property.1⟩ p.val.2
  let K : Set (ℝ × C.ambient.manifold.Point) :=
    parameterInterval ×ˢ (C.inclusion.map '' D.domain.carrier ∪
      C.endMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)))
  let L : Set (ℝ × C.ambient.manifold.Point) :=
    parameterInterval ×ˢ (C.endMap '' (univ ×ˢ Icc (1 / 2 : ℝ) 2))
  let B : Set (ℝ × C.ambient.manifold.Point) :=
    univ ×ˢ (C.endMap '' (univ ×ˢ Ici (1 : ℝ)))
  let O : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
    ⟨(V : Set ℝ) ×ˢ C.endAbove 0, V.isOpen.prod (C.endAbove 0).isOpen⟩
  let b : O → ℝ × C.escapingBasin := fun p =>
    (p.val.1, ⟨p.val.2, C.endAbove_subset_escapingBasin 0 p.property.2⟩)
  let g : O → N.Point := C.endFamilyMap N β ∘ b
  have hb : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ b :=
    (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      ((ContMDiff.subtypeVal_comp_iff C.escapingBasin _).mp
        (contMDiff_snd.comp contMDiff_subtype_val))
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g := by
    intro p
    have hpβ : (p.val.1, C.endCoordinates (b p).2) ∈
        (V : Set ℝ) ×ˢ (univ ×ˢ Ioi (0 : ℝ)) :=
      ⟨p.property.1, mem_univ _,
        C.endCoordinates_radius_gt_of_mem_endAbove 0 p.val.2 p.property.2⟩
    have hsm : ContMDiffAt ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
        (fun q : ℝ × (D.domain.boundary.Point × ℝ) => β q.1 q.2)
        (p.val.1, C.endCoordinates (b p).2) :=
      hβ.contMDiffAt ((V.isOpen.prod (isOpen_univ.prod isOpen_Ioi)).mem_nhds hpβ)
    change ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : O => β q.val.1 (C.endCoordinates (b q).2)) p
    exact hsm.comp p
        ((contMDiff_fst.prodMk (C.contMDiff_endCoordinates.comp contMDiff_snd)).comp hb p)
  have hgA : ∀ p (hpO : p ∈ O) (hpA : p ∈ A),
      g ⟨p, hpO⟩ = f₀ ⟨p, hpA⟩ := by
    rintro ⟨t, z⟩ hpO hpA
    let q := C.endCoordinates ⟨z, C.endAbove_subset_escapingBasin 0 hpO.2⟩
    have he : C.endMap q = z :=
      C.endMap_endCoordinates ⟨z, C.endAbove_subset_escapingBasin 0 hpO.2⟩
    change β t q = f ⟨t, hpA.1⟩ z
    rw [← he]
    exact (hend ⟨t, hpA.1⟩ q.1 q.2
      (C.endCoordinates_radius_gt_of_mem_endAbove 0 z hpO.2)).symm
  have hK : IsCompact K := isCompact_Icc.prod
    ((D.domain.compact.image C.inclusion.map.contMDiff.continuous).union
      ((D.domain.isCompact_boundary.prod isCompact_Icc).image C.smooth_endMap.continuous))
  have hKA : K ⊆ A := fun _ hp => ⟨hp.1, mem_univ _⟩
  have hL : IsCompact L := isCompact_Icc.prod
    ((D.domain.isCompact_boundary.prod isCompact_Icc).image C.smooth_endMap.continuous)
  have hLO : L ⊆ O := by
    rintro ⟨t, _⟩ ⟨ht, q, hq, rfl⟩
    exact ⟨hIV ht, ⟨q, ⟨mem_univ _, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hq.2.1⟩, rfl⟩⟩
  have hB : IsClosed B := isClosed_univ.prod (C.isClosed_endMap_image_Ici 1)
  have hKB : Disjoint K B := by
    apply Set.disjoint_left.mpr
    rintro ⟨t, z⟩ ⟨_, hzK⟩ ⟨_, ⟨y, r⟩, ⟨_, hr⟩, hrz⟩
    rcases hzK with ⟨x, hx, he⟩ | ⟨⟨x, s⟩, ⟨_, hs⟩, he⟩
    · have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr
      exact C.overlap y r hrpos ⟨x, hx, he.trans hrz.symm⟩
    · have heq := C.endMap_injective (he.trans hrz.symm)
      have hrs : s = r := congrArg Prod.snd heq
      change 0 ≤ s ∧ s ≤ 1 / 2 at hs
      change 1 ≤ r at hr
      linarith
  have hlocalK : ∀ p : K, ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
      p.val ∈ U ∧ ∃ a : U → N.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a ∧
        ∀ z (hzU : z ∈ U) (hzA : z ∈ A), a ⟨z, hzU⟩ = f₀ ⟨z, hzA⟩ := by
    rintro ⟨⟨t, z⟩, ht, hz⟩
    have hlocalCarrier (x : D.domain.extension.Point) (hx : x ∈ D.domain.carrier) :
        ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
          (t, C.inclusion.map x) ∈ U ∧ ∃ a : U → N.Point,
            ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a ∧
            ∀ z (hzU : z ∈ U) (hzA : z ∈ A), a ⟨z, hzU⟩ = f₀ ⟨z, hzA⟩ := by
      obtain ⟨U, hpU, a, ha, heq⟩ := hlocal ⟨t, ht⟩ x hx
      exact ⟨U, hpU, a, ha, fun ⟨s, z⟩ hzU hzA => heq ⟨s, hzA.1⟩ z hzU⟩
    rcases hz with ⟨x, hx, he⟩ | ⟨⟨x, r⟩, ⟨_, hr⟩, he⟩
    · change C.inclusion.map x = z at he
      subst z
      exact hlocalCarrier x hx
    · change C.endMap (x, r) = z at he
      subst z
      by_cases hrzero : r = 0
      · subst r
        simpa only [C.endMap_zero] using hlocalCarrier (D.domain.boundaryInclusion.map x)
          (D.domain.compact.isClosed.frontier_subset (D.domain.boundaryInclusion_mem_frontier x))
      · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hrzero)
        exact ⟨O, ⟨hIV ht, ⟨(x, r), ⟨mem_univ _, hrpos⟩, rfl⟩⟩, g, hg, hgA⟩
  have hM : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (ℝ × C.ambient.manifold.Point) := inferInstance
  let : ChartedSpace (ℝ × Model d) (ℝ × C.ambient.manifold.Point) :=
    prodChartedSpace ℝ ℝ (Model d) C.ambient.manifold.Point
  rw [← modelWithCornersSelf_prod] at hM
  let : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × C.ambient.manifold.Point) := hM
  simp_rw +instances [← modelWithCornersSelf_prod] at hg hlocalK
  obtain ⟨W, hcover, α, hα, hαA, hretain⟩ :=
    SmoothMapExtension.exists_extension_from_compact_germs_preserving_region
      f₀ hK hKA hL hB hKB O hLO g hg hgA hlocalK
  let P : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
    ⟨(V : Set ℝ) ×ˢ C.endAbove 1, V.isOpen.prod (C.endAbove 1).isOpen⟩
  have hPO : (P : Set (ℝ × C.ambient.manifold.Point)) ⊆ O := by
    rintro ⟨t, z⟩ ⟨ht, q, hq, he⟩
    exact ⟨ht, ⟨q, ⟨mem_univ _,
      lt_trans (by norm_num : (0 : ℝ) < 1) hq.2⟩, he⟩⟩
  have hPB : (P : Set (ℝ × C.ambient.manifold.Point)) ⊆ B := by
    rintro ⟨t, z⟩ ⟨_, q, hq, he⟩
    exact ⟨mem_univ _, ⟨q, ⟨mem_univ _, by
      change 1 ≤ q.2
      exact le_of_lt hq.2⟩, he⟩⟩
  let c : P → O := TopologicalSpace.Opens.inclusion hPO
  have hc : ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, Model e) ∞ (g ∘ c) :=
    hg.comp (contMDiff_inclusion hPO)
  have hmatch : ∀ z (hzW : z ∈ W) (hzP : z ∈ P),
      α ⟨z, hzW⟩ = (g ∘ c) ⟨z, hzP⟩ := by
    intro z hzW hzP
    obtain ⟨hzO, he⟩ := hretain z hzW (hPB hzP)
    exact he
  obtain ⟨u, hu, huW, huP⟩ := SmoothMapExtension.exists_smooth_open_gluing W P
    α (g ∘ c) hα hc hmatch
  have hAcover : A ⊆ ((W ⊔ P : TopologicalSpace.Opens
      (ℝ × C.ambient.manifold.Point)) : Set (ℝ × C.ambient.manifold.Point)) := by
    rintro ⟨t, z⟩ ⟨ht, _⟩
    have hz : z ∈ C.inclusion.map '' D.domain.carrier ∪
        C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by rw [C.covering]; trivial
    rcases hz with hz | ⟨⟨x, r⟩, ⟨_, hr⟩, rfl⟩
    · exact Or.inl (hcover (Or.inr ⟨ht, Or.inl hz⟩))
    · by_cases hr2 : r ≤ 2
      · by_cases hrhalf : r ≤ 1 / 2
        · exact Or.inl (hcover (Or.inr ⟨ht, Or.inr ⟨(x, r), ⟨mem_univ _, hr, hrhalf⟩, rfl⟩⟩))
        · exact Or.inl (hcover (Or.inl ⟨ht, ⟨(x, r),
            ⟨mem_univ _, le_of_lt (lt_of_not_ge hrhalf), hr2⟩, rfl⟩⟩))
      · exact Or.inr ⟨hIV ht, ⟨(x, r), ⟨mem_univ _, by change 1 < r; linarith⟩, rfl⟩⟩
  have huA : ∀ z (hzU : z ∈ W ⊔ P) (hzA : z ∈ A),
      u ⟨z, hzU⟩ = f₀ ⟨z, hzA⟩ := by
    intro z hzU hzA
    rcases hzU with hzW | hzP
    · exact (huW z hzW).trans (hαA z hzW hzA)
    · exact (huP z hzP).trans (hgA z (hPO hzP) hzA)
  rw [modelWithCornersSelf_prod] at hu
  let ext : ℝ → C.ambient.manifold.Point → N.Point := fun t z =>
    if hz : (t, z) ∈ W ⊔ P then u ⟨(t, z), hz⟩ else f parameterZero z
  have hext : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun z : ↥(W ⊔ P) => ext z.val.1 z.val.2) := by
    have heq : (fun z : ↥(W ⊔ P) => ext z.val.1 z.val.2) = u := by
      funext z
      simp only [ext, dite_eq_left z.property]
    rw [heq]
    exact hu
  refine ⟨ext, ⟨W ⊔ P, (W ⊔ P).isOpen, hAcover, ?_⟩, ?_⟩
  · intro z hz
    exact ((contMDiffAt_subtype_iff (f := fun z : ℝ × C.ambient.manifold.Point =>
      ext z.1 z.2) (x := (⟨z, hz⟩ : ↥(W ⊔ P)))).mp (hext ⟨z, hz⟩)).contMDiffWithinAt
  · intro t
    funext z
    have hzA : (t.val, z) ∈ A := ⟨t.property, mem_univ _⟩
    have hzU : (t.val, z) ∈ W ⊔ P := hAcover hzA
    dsimp only [ext]
    rw [dite_eq_left hzU]
    exact huA (t.val, z) hzU hzA

end FsFltz.Geometry.Completion
