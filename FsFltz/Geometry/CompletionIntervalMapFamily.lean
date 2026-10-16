import FsFltz.Geometry.CompletionMapFamily
import FsFltz.Geometry.SmoothMapExteriorExtension

/-!
# Interval completion maps from independently extended local formulas

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:chain`,
163–199, and `sec:lean`, 788–814. Compact germs and a cylindrical formula
above a negative cutoff need agree only at actual parameters. Finite target-chart corrections on the
compact piece preserve a far-cylinder extension, which is glued back on
the noncompact end. No off-interval primitive or diffeomorphism law is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.Completion
open SmoothManifold

variable {d : ℕ} {D : LiouvilleDomain d}

/-- Every fixed outward end cutoff is closed in the actual completion. -/
theorem isClosed_endMap_image_Ici (C : Completion D) (a : ℝ) :
    IsClosed (C.endMap '' (univ ×ˢ Ici a)) := by
  have hzero : C.endMap '' (univ ×ˢ Ici (0 : ℝ)) =
      (C.inclusion.map '' interior D.domain.carrier)ᶜ := by
    rw [← C.range_nonnegative_endMap]
    ext z
    constructor
    · rintro ⟨⟨x, r⟩, ⟨_, hr⟩, rfl⟩
      exact ⟨(x, ⟨r, hr⟩), rfl⟩
    · rintro ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩
      exact ⟨(x, r), ⟨mem_univ _, hr⟩, rfl⟩
  have hc : IsClosed (C.endMap '' (univ ×ˢ Ici (0 : ℝ))) := by
    rw [hzero]
    exact (C.inclusion_isLocalDiffeomorph.isLocalHomeomorph.isOpenMap
      _ isOpen_interior).isClosed_compl
  have he : C.endMap '' (univ ×ˢ Ici a) =
      C.ambient.completeFlow.flow a '' (C.endMap '' (univ ×ˢ Ici (0 : ℝ))) := by
    ext z
    constructor
    · rintro ⟨⟨x, r⟩, ⟨_, hr⟩, rfl⟩
      change a ≤ r at hr
      refine ⟨C.endMap (x, r - a), ⟨(x, r - a), ⟨mem_univ _, sub_nonneg.mpr hr⟩, rfl⟩, ?_⟩
      rw [C.flow_endMap]
      congr 1
      simp
    · rintro ⟨_, ⟨⟨x, r⟩, ⟨_, hr⟩, rfl⟩, rfl⟩
      change 0 ≤ r at hr
      rw [C.flow_endMap]
      exact ⟨(x, a + r), ⟨mem_univ _, by change a ≤ a + r; linarith⟩, rfl⟩
  rw [he]
  exact (C.ambient.completeFlow.flow.toHomeomorph a).isClosedMap _ hc

/-- The actual completion has a smooth open end above any real cutoff. -/
def endAbove (C : Completion D) (a : ℝ) : TopologicalSpace.Opens C.ambient.manifold.Point :=
  ⟨C.endMap '' (univ ×ˢ Ioi a), C.endMap_isLocalDiffeomorph.isLocalHomeomorph.isOpenMap
    _ (isOpen_univ.prod isOpen_Ioi)⟩

theorem endAbove_subset_escapingBasin (C : Completion D) (a : ℝ) :
    (C.endAbove a : Set C.ambient.manifold.Point) ⊆ C.escapingBasin := by
  rintro z ⟨q, _, he⟩
  exact ⟨q, he⟩

theorem endCoordinates_radius_gt_of_mem_endAbove (C : Completion D) (a : ℝ)
    (z : C.ambient.manifold.Point) (hz : z ∈ C.endAbove a) :
    a < (C.endCoordinates ⟨z, C.endAbove_subset_escapingBasin a hz⟩).2 := by
  have hbasin := C.endAbove_subset_escapingBasin a hz
  obtain ⟨q, hq, he⟩ := hz
  have hcoord := C.endMap_injective
    ((C.endMap_endCoordinates ⟨z, hbasin⟩).trans he.symm)
  rw [hcoord]
  exact hq.2

/-- A jointly smooth cylindrical formula defines a smooth map on the
actual escaping basin, using its proved smooth end coordinates. -/
def endFamilyMap {e : ℕ} (C : Completion D) (N : SmoothManifold e)
    (β : ℝ → D.domain.boundary.Point × ℝ → N.Point)
    (p : ℝ × C.escapingBasin) : N.Point := β p.1 (C.endCoordinates p.2)

theorem contMDiffOn_endFamilyMap {e : ℕ} (C : Completion D) (N : SmoothManifold e)
    (β : ℝ → D.domain.boundary.Point × ℝ → N.Point)
    (V : TopologicalSpace.Opens ℝ)
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × (D.domain.boundary.Point × ℝ) => β p.1 p.2)
      ((V : Set ℝ) ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (C.endFamilyMap N β) ((V : Set ℝ) ×ˢ univ) :=
  hβ.comp (contMDiff_fst.prodMk (C.contMDiff_endCoordinates.comp contMDiff_snd)).contMDiffOn
    (fun _ hp => ⟨hp.1, mem_univ _⟩)

/-- Compact local germs and an independently smooth cylindrical formula
on a two-sided strip and the outward end produce a smooth extension of
the same interval maps on the entire completion. Only a negative cutoff
is required; no inward formula below that cutoff is used. -/
theorem isSmoothIntervalMapFamily_of_compact_germs_end_strip {e : ℕ}
    (C : Completion D) (N : SmoothManifold e)
    (f : Parameter → C.ambient.manifold.Point → N.Point)
    (β : ℝ → D.domain.boundary.Point × ℝ → N.Point)
    (V : TopologicalSpace.Opens ℝ) (hIV : parameterInterval ⊆ V)
    (a : ℝ) (ha : a < 0)
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × (D.domain.boundary.Point × ℝ) => β p.1 p.2)
      ((V : Set ℝ) ×ˢ (univ ×ˢ Ioi a)))
    (hend : ∀ t x r, a < r → f t (C.endMap (x, r)) = β t.val (x, r))
    (hlocal : ∀ (t : Parameter) x, x ∈ D.domain.carrier →
      ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
        (t.val, C.inclusion.map x) ∈ U ∧ ∃ g : U → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g ∧
          ∀ s z (hz : (s.val, z) ∈ U), g ⟨(s.val, z), hz⟩ = f s z) :
    C.ambient.manifold.IsSmoothIntervalMapFamily N f := by
  let A : Set (ℝ × C.ambient.manifold.Point) := parameterInterval ×ˢ univ
  let f₀ : A → N.Point := fun p => f ⟨p.val.1, p.property.1⟩ p.val.2
  let K : Set (ℝ × C.ambient.manifold.Point) :=
    parameterInterval ×ˢ (C.inclusion.map '' D.domain.carrier)
  let L : Set (ℝ × C.ambient.manifold.Point) :=
    parameterInterval ×ˢ (C.endMap '' (univ ×ˢ Icc (0 : ℝ) 2))
  let B : Set (ℝ × C.ambient.manifold.Point) :=
    univ ×ˢ (C.endMap '' (univ ×ˢ Ici (1 : ℝ)))
  let O : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
    ⟨(V : Set ℝ) ×ˢ C.endAbove a, V.isOpen.prod (C.endAbove a).isOpen⟩
  let b : O → ℝ × C.escapingBasin := fun p =>
    (p.val.1, ⟨p.val.2, C.endAbove_subset_escapingBasin a p.property.2⟩)
  let g : O → N.Point := C.endFamilyMap N β ∘ b
  have hb : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ b :=
    (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      ((ContMDiff.subtypeVal_comp_iff C.escapingBasin _).mp
        (contMDiff_snd.comp contMDiff_subtype_val))
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g := by
    intro p
    have hpβ : (p.val.1, C.endCoordinates (b p).2) ∈
        (V : Set ℝ) ×ˢ (univ ×ˢ Ioi a) :=
      ⟨p.property.1, mem_univ _,
        C.endCoordinates_radius_gt_of_mem_endAbove a p.val.2 p.property.2⟩
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
    let q := C.endCoordinates ⟨z, C.endAbove_subset_escapingBasin a hpO.2⟩
    have he : C.endMap q = z :=
      C.endMap_endCoordinates ⟨z, C.endAbove_subset_escapingBasin a hpO.2⟩
    change β t q = f ⟨t, hpA.1⟩ z
    rw [← he]
    exact (hend ⟨t, hpA.1⟩ q.1 q.2
      (C.endCoordinates_radius_gt_of_mem_endAbove a z hpO.2)).symm
  have hK : IsCompact K := isCompact_Icc.prod
    (D.domain.compact.image C.inclusion.map.contMDiff.continuous)
  have hKA : K ⊆ A := fun _ hp => ⟨hp.1, mem_univ _⟩
  have hL : IsCompact L := isCompact_Icc.prod
    ((D.domain.isCompact_boundary.prod isCompact_Icc).image C.smooth_endMap.continuous)
  have hLO : L ⊆ O := by
    rintro ⟨t, _⟩ ⟨ht, q, hq, rfl⟩
    exact ⟨hIV ht, ⟨q, ⟨mem_univ _, lt_of_lt_of_le ha hq.2.1⟩, rfl⟩⟩
  have hB : IsClosed B := isClosed_univ.prod (C.isClosed_endMap_image_Ici 1)
  have hKB : Disjoint K B := by
    apply Set.disjoint_left.mpr
    rintro ⟨t, z⟩ ⟨_, x, hx, he⟩ ⟨_, ⟨y, r⟩, ⟨_, hr⟩, hrz⟩
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr
    exact C.overlap y r hrpos ⟨x, hx, he.trans hrz.symm⟩
  have hlocalK : ∀ p : K, ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
      p.val ∈ U ∧ ∃ a : U → N.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a ∧
        ∀ z (hzU : z ∈ U) (hzA : z ∈ A), a ⟨z, hzU⟩ = f₀ ⟨z, hzA⟩ := by
    rintro ⟨⟨t, z⟩, ht, x, hx, he⟩
    change C.inclusion.map x = z at he
    subst z
    obtain ⟨U, hpU, a, ha, heq⟩ := hlocal ⟨t, ht⟩ x hx
    refine ⟨U, hpU, a, ha, ?_⟩
    rintro ⟨s, z⟩ hzU hzA
    exact heq ⟨s, hzA.1⟩ z hzU
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
      lt_trans ha (lt_trans (by norm_num : (0 : ℝ) < 1) hq.2)⟩, he⟩⟩
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
    · exact Or.inl (hcover (Or.inr ⟨ht, hz⟩))
    · by_cases hr2 : r ≤ 2
      · exact Or.inl (hcover (Or.inl ⟨ht, ⟨(x, r), ⟨mem_univ _, hr, hr2⟩, rfl⟩⟩))
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

/-- All-real cylindrical formulas are a convenient special case of the
two-sided-strip extension theorem. -/
theorem isSmoothIntervalMapFamily_of_compact_germs_end_formula {e : ℕ}
    (C : Completion D) (N : SmoothManifold e)
    (f : Parameter → C.ambient.manifold.Point → N.Point)
    (β : ℝ → D.domain.boundary.Point × ℝ → N.Point)
    (V : TopologicalSpace.Opens ℝ) (hIV : parameterInterval ⊆ V)
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × (D.domain.boundary.Point × ℝ) => β p.1 p.2)
      ((V : Set ℝ) ×ˢ univ))
    (hend : ∀ t x r, f t (C.endMap (x, r)) = β t.val (x, r))
    (hlocal : ∀ (t : Parameter) x, x ∈ D.domain.carrier →
      ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
        (t.val, C.inclusion.map x) ∈ U ∧ ∃ g : U → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g ∧
          ∀ s z (hz : (s.val, z) ∈ U), g ⟨(s.val, z), hz⟩ = f s z) :
    C.ambient.manifold.IsSmoothIntervalMapFamily N f :=
  C.isSmoothIntervalMapFamily_of_compact_germs_end_strip N f β V hIV (-1)
    (by norm_num) (hβ.mono (fun _ hp => ⟨hp.1, mem_univ _⟩))
    (fun t x r _ => hend t x r) hlocal

/-- Independently extended compact and cylindrical formulas determine a
jointly smooth family on the whole fixed completion. Their equality is
required only at actual interval parameters, including both endpoints. -/
theorem isSmoothIntervalMapFamily_of_compact_and_end_formulas {e : ℕ}
    (C : Completion D) (N : SmoothManifold e)
    (f : Parameter → C.ambient.manifold.Point → N.Point)
    (g : ℝ → D.domain.extension.Point → N.Point)
    (β : ℝ → D.domain.boundary.Point × ℝ → N.Point)
    (V : TopologicalSpace.Opens ℝ) (hIV : parameterInterval ⊆ V)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × D.domain.extension.Point => g p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × (D.domain.boundary.Point × ℝ) => β p.1 p.2)
      ((V : Set ℝ) ×ˢ univ))
    (hcompact : ∀ t x, x ∈ D.domain.carrier → f t (C.inclusion.map x) = g t.val x)
    (hend : ∀ t x r, f t (C.endMap (x, r)) = β t.val (x, r)) :
    C.ambient.manifold.IsSmoothIntervalMapFamily N f := by
  apply C.isSmoothIntervalMapFamily_of_compact_germs_end_formula N f β V hIV hβ hend
  intro t x hx
  by_cases hz : C.inclusion.map x ∈ C.inclusion.map '' interior D.domain.carrier
  · obtain ⟨y, hy, he⟩ := hz
    let l := C.inclusion_isLocalDiffeomorph y
    let S : Set C.ambient.manifold.Point :=
      {z | z ∈ l.localInverse.source ∧ l.localInverse z ∈ interior D.domain.carrier}
    have hS : IsOpen S := by
      apply isOpen_iff_mem_nhds.mpr
      intro z hz
      exact inter_mem (l.localInverse.open_source.mem_nhds hz.1)
        ((l.localInverse_contMDiffOn.contMDiffAt
          (l.localInverse.open_source.mem_nhds hz.1)).continuousAt.preimage_mem_nhds
            (isOpen_interior.mem_nhds hz.2))
    let U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
      ⟨(V : Set ℝ) ×ˢ S, V.isOpen.prod hS⟩
    let a : U → N.Point := fun p => g p.val.1 (l.localInverse p.val.2)
    have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a := by
      intro p
      have hi := l.localInverse_contMDiffOn.contMDiffAt
        (l.localInverse.open_source.mem_nhds p.property.2.1)
      have hp : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
          (fun q : U => (q.val.1, l.localInverse q.val.2)) p :=
        (contMDiffAt_fst.comp p contMDiff_subtype_val.contMDiffAt).prodMk
        (hi.comp p (contMDiffAt_snd.comp p contMDiff_subtype_val.contMDiffAt))
      exact (hg.contMDiffAt ((V.isOpen.prod isOpen_univ).mem_nhds
        ⟨p.property.1, mem_univ _⟩)).comp p hp
    refine ⟨U, ?_, a, ha, ?_⟩
    · refine ⟨hIV t.property, ?_⟩
      rw [← he]
      exact ⟨l.localInverse_mem_source, by
        rw [l.localInverse_left_inv l.localInverse_mem_target]; exact hy⟩
    · intro s z hzU
      change g s.val (l.localInverse z) = f s z
      have hez : C.inclusion.map (l.localInverse z) = z :=
        l.localInverse_right_inv hzU.2.1
      simpa only [hez] using (hcompact s _ (interior_subset hzU.2.2)).symm
  · have hz' : C.inclusion.map x ∈ C.escapingBasin := by
      have hr : C.inclusion.map x ∈ Set.range
          (fun p : D.domain.boundary.Point × Ici (0 : ℝ) => C.endMap (p.1, p.2)) := by
        rw [C.range_nonnegative_endMap]
        exact hz
      obtain ⟨⟨y, r⟩, he⟩ := hr
      exact ⟨(y, r.val), he⟩
    let U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
      ⟨(V : Set ℝ) ×ˢ C.escapingBasin, V.isOpen.prod C.escapingBasin.isOpen⟩
    let b : U → ℝ × C.escapingBasin := fun p => (p.val.1, ⟨p.val.2, p.property.2⟩)
    let a : U → N.Point := C.endFamilyMap N β ∘ b
    have hb : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ b :=
      (contMDiff_fst.comp contMDiff_subtype_val).prodMk
        ((ContMDiff.subtypeVal_comp_iff C.escapingBasin _).mp
          (contMDiff_snd.comp contMDiff_subtype_val))
    have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a := by
      intro p
      exact ((C.contMDiffOn_endFamilyMap N β V hβ).contMDiffAt
        ((V.isOpen.prod isOpen_univ).mem_nhds ⟨p.property.1, mem_univ _⟩)).comp p (hb p)
    refine ⟨U, ⟨hIV t.property, hz'⟩, a, ha, ?_⟩
    intro s z hzU
    let q := C.endCoordinates ⟨z, hzU.2⟩
    have he : C.endMap q = z := C.endMap_endCoordinates ⟨z, hzU.2⟩
    change β s.val q = f s z
    rw [← he]
    exact (hend s q.1 q.2).symm

variable {E : LiouvilleDomain d}

/-- Strict compact primitive transport produces comparison maps whose
forward and inverse families are jointly smooth from independent smooth
compact and boundary extensions. No real-parameter collar compatibility
and no off-interval inverse or primitive law is assumed. -/
theorem exists_strictEquivFamily_of_independent_compact_extensions
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
    (hbival : ∀ t y, bi t.val y = (h t).boundaryEquiv.symm y) :
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
  · apply C.isSmoothIntervalMapFamily_of_compact_and_end_formulas C'.ambient.manifold
      (fun t => e t) (fun t x => C'.inclusion.map (g t x))
      (fun t q => C'.endMap (b t q.1, q.2)) V hIV
    · exact C'.inclusion.map.contMDiff.comp_contMDiffOn hg
    · have hbb : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model (d - 1)) ∞
          (fun p : ℝ × (D.domain.boundary.Point × ℝ) => b p.1 p.2.1)
          ((V : Set ℝ) ×ˢ univ) :=
        hb.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).contMDiffOn
          (fun _ hp => ⟨hp.1, mem_univ _⟩)
      exact C'.smooth_endMap.comp_contMDiffOn
        (hbb.prodMk (contMDiff_snd.comp contMDiff_snd).contMDiffOn)
    · intro t x hx
      rw [hgval t x hx]
      exact hcomp t x hx
    · intro t x r
      rw [hbval]
      exact hend t x r
  · apply C'.isSmoothIntervalMapFamily_of_compact_and_end_formulas C.ambient.manifold
      (fun t => (e t).symm) (fun t y => C.inclusion.map (gi t y))
      (fun t q => C.endMap (bi t q.1, q.2)) V hIV
    · exact C.inclusion.map.contMDiff.comp_contMDiffOn hgi
    · have hbb : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model (d - 1)) ∞
          (fun p : ℝ × (E.domain.boundary.Point × ℝ) => bi p.1 p.2.1)
          ((V : Set ℝ) ×ˢ univ) :=
        hbi.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).contMDiffOn
          (fun _ hp => ⟨hp.1, mem_univ _⟩)
      exact C.smooth_endMap.comp_contMDiffOn
        (hbb.prodMk (contMDiff_snd.comp contMDiff_snd).contMDiffOn)
    · intro t y hy
      rw [hgival t y hy]
      exact hcompinv t y hy
    · intro t y r
      rw [hbival]
      exact hendinv t y r

end FsFltz.Geometry.Completion
