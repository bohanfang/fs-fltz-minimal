import FsFltz.Geometry.CompactCollarFamily

/-!
# Compactly supported velocity for a coherently embedded collar family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. The family parameter is frozen during the
correction flow; compact support is chosen jointly over its closed interval.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
namespace CollarFamilyExtension

variable {B F M Q HM HQ : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace HM] [TopologicalSpace HQ]
  {I : ModelWithCorners ℝ B HM} {J : ModelWithCorners ℝ F HQ}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold J ∞ Q]

/-- A geometric embedded isotopy, with joint local inverses. -/
structure EmbeddedIsotopy (f : ℝ × M → Q) where
  source : TopologicalSpace.Opens (ℝ × M)
  smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) J ∞ f source
  embedding : Topology.IsOpenEmbedding (fun p : source => (p.val.1, f p.val))
  localDiffeomorph : IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod I)
    ((𝓘(ℝ, ℝ)).prod J) ∞ (fun p => (p.1, f p)) source

namespace EmbeddedIsotopy
variable {f : ℝ × M → Q} (A : EmbeddedIsotopy (I := I) (J := J) f)

def target : TopologicalSpace.Opens (ℝ × Q) :=
  ⟨range (fun p : A.source => (p.val.1, f p.val)), A.embedding.isOpen_range⟩

def coordinates (z : A.target) : ℝ × M := z.property.choose.val

omit [IsManifold I ∞ M] [IsManifold J ∞ Q] in
theorem coordinates_mem (z : A.target) : A.coordinates z ∈ A.source :=
  z.property.choose.property

omit [IsManifold I ∞ M] [IsManifold J ∞ Q] in
@[simp] theorem apply_coordinates (z : A.target) :
    ((A.coordinates z).1, f (A.coordinates z)) = z.val := z.property.choose_spec

omit [IsManifold I ∞ M] [IsManifold J ∞ Q] in
theorem coordinates_apply (p : ℝ × M) (hp : p ∈ A.source) :
    A.coordinates ⟨(p.1, f p), ⟨⟨p, hp⟩, rfl⟩⟩ = p := by
  have hinj : InjOn (fun p => (p.1, f p)) A.source :=
    Set.injOn_iff_injective.mpr A.embedding.injective
  exact hinj (A.coordinates_mem _) hp (A.apply_coordinates _)

omit [IsManifold I ∞ M] [IsManifold J ∞ Q] in
theorem contMDiff_coordinates :
    ContMDiff ((𝓘(ℝ, ℝ)).prod J) ((𝓘(ℝ, ℝ)).prod I) ∞
      A.coordinates := by
  intro z
  let l := A.localDiffeomorph ⟨A.coordinates z, A.coordinates_mem z⟩
  have hi : ContMDiffAt ((𝓘(ℝ, ℝ)).prod J)
      ((𝓘(ℝ, ℝ)).prod I) ∞ l.localInverse z.val := by
    rw [← A.apply_coordinates z]
    exact l.localInverse_contMDiffAt
  have hz : l.localInverse z.val = A.coordinates z := by
    rw [← A.apply_coordinates z]
    exact l.localInverse_left_inv l.localInverse_mem_target
  apply (hi.comp z (contMDiff_subtype_val z)).congr_of_eventuallyEq
  have ht : Tendsto (Subtype.val : A.target → ℝ × Q) (𝓝 z)
      (𝓝 ((A.coordinates z).1, f (A.coordinates z))) := by
    rw [A.apply_coordinates]
    exact continuous_subtype_val.continuousAt
  have hn : ∀ᶠ y in 𝓝 z, l.localInverse y.val ∈ A.source :=
    (hi.continuousAt.comp continuousAt_subtype_val).preimage_mem_nhds
      (by simpa only [Function.comp_apply, hz] using
        A.source.isOpen.mem_nhds (A.coordinates_mem z))
  filter_upwards [hn, l.localInverse_eventuallyEq_right.comp_tendsto ht] with y hy he
  have hinj : InjOn (fun p => (p.1, f p)) A.source :=
    Set.injOn_iff_injective.mpr A.embedding.injective
  exact hinj (A.coordinates_mem y) hy ((A.apply_coordinates y).trans he.symm)

/-- Eulerian velocity from the unique joint inverse, zero outside its
actual open target. -/
def velocity (p : ℝ × Q) : TangentSpace J p.2 :=
  if hp : p ∈ A.target then
    mfderiv ((𝓘(ℝ, ℝ)).prod I) J f
      (A.coordinates ⟨p, hp⟩) (1, (0 : B))
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_velocity :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod J) ((J).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, A.velocity p⟩ : TangentBundle J Q)) A.target := by
  have hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) J.tangent ∞
      (fun p : ℝ × M => (⟨f p, mfderiv ((𝓘(ℝ, ℝ)).prod I) J f p (1, (0 : B))⟩ :
        TangentBundle J Q)) A.source := by
    have hv := A.smooth.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      A.source.isOpen.uniqueMDiffOn |>.comp
        (CollarExtension.contMDiff_timeUnitSection (I := I)).contMDiffOn (fun _ hp => hp)
    apply hv.congr
    intro p hp
    dsimp only [Function.comp_def, tangentMapWithin]
    rw [mfderivWithin_eq_mfderiv (A.source.isOpen.uniqueMDiffOn p hp)
      ((A.smooth.contMDiffAt (A.source.isOpen.mem_nhds hp)).mdifferentiableAt (by simp))]
  have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod J) ((J).tangent) ∞
      (fun p : A.target => (⟨p.val.2, A.velocity p.val⟩ : TangentBundle J Q)) := by
    intro p
    have hg := (hv.contMDiffAt (A.source.isOpen.mem_nhds (A.coordinates_mem p))).comp
      p (A.contMDiff_coordinates p)
    apply hg.congr_of_eventuallyEq
    filter_upwards [] with q
    have he : f (A.coordinates q) = q.val.2 := congrArg Prod.snd (A.apply_coordinates q)
    dsimp only [Function.comp_def]
    rw [he]
    simp only [velocity, dite_eq_left q.property]
    rfl
  intro p hp
  exact ((contMDiffAt_subtype_iff (U := A.target)
    (f := fun p : ℝ × Q => (⟨p.2, A.velocity p⟩ : TangentBundle J Q))).mp
      (hs ⟨p, hp⟩)).contMDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold I ∞ M] [IsManifold J ∞ Q] in
theorem velocity_apply (p : ℝ × M) (hp : p ∈ A.source) :
    A.velocity (p.1, f p) =
      mfderiv ((𝓘(ℝ, ℝ)).prod I) J f p (1, (0 : B)) := by
  rw [velocity, dite_eq_left (show (p.1, f p) ∈ A.target from ⟨⟨p, hp⟩, rfl⟩),
    A.coordinates_apply p hp]

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold I ∞ M] [IsManifold J ∞ Q] in
theorem hasMFDerivAt_apply (s : ℝ) (q : M) (hp : (s, q) ∈ A.source) :
    HasMFDerivAt 𝓘(ℝ, ℝ) J (fun u => f (u, q)) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (A.velocity (s, f (s, q)))) := by
  have hf := A.smooth.contMDiffAt (A.source.isOpen.mem_nhds hp)
  have hi : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun u : ℝ => (u, q)) := contMDiff_id.prodMk contMDiff_const
  have hm := mfderiv_comp (f := fun u : ℝ => (u, q)) (g := f) s
    (hf.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  have hs := (hf.comp s (hi s)).mdifferentiableAt (by simp) |>.hasMFDerivAt
  apply hs.congr_mfderiv
  rw [hm, mfderiv_prod_left, A.velocity_apply (s, q) hp]
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change mfderiv ((𝓘(ℝ, ℝ)).prod I) J f (s, q) (r, 0) =
    r • mfderiv ((𝓘(ℝ, ℝ)).prod I) J f (s, q) (1, (0 : B))
  rw [← map_smul]
  congr 1
  change (r, (0 : B)) = r • (1, (0 : B))
  simp

private def liftedVelocity (p : ℝ × Q) :
    TangentSpace ((𝓘(ℝ, ℝ)).prod J) p := (0, A.velocity p)

private theorem contMDiffOn_liftedVelocity :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod J)
      (((𝓘(ℝ, ℝ)).prod J).tangent) ∞
      (fun p => (⟨p, A.liftedVelocity p⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod J) (ℝ × Q))) A.target := by
  have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
      (fun s : ℝ => (⟨s, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
    ((ht.comp contMDiff_fst).contMDiffOn.prodMk A.contMDiffOn_velocity)

def supportedVelocity (χ : ℝ × Q → ℝ) (p : ℝ × Q) : TangentSpace J p.2 :=
  χ p • A.velocity p

theorem contMDiff_supportedVelocity (χ : ℝ × Q → ℝ)
    (hχ : ContMDiff ((𝓘(ℝ, ℝ)).prod J) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ (A.target : Set (ℝ × Q))) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod J) ((J).tangent) ∞
      (fun p => (⟨p.2, A.supportedVelocity χ p⟩ : TangentBundle J Q)) := by
  have hs := hχ.contMDiffOn.smul_section_of_tsupport A.target.isOpen hsupp
    A.contMDiffOn_liftedVelocity
  exact (contMDiff_equivTangentBundleProd.comp hs).snd

end EmbeddedIsotopy
end CollarFamilyExtension

namespace Completion
open SmoothManifold

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : ℝ → DomainPresentationEquiv D.domain E.domain)

structure EmbeddedFamilyCollar
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) extends
    CollarFamilyExtension.EmbeddedIsotopy
      (I := (𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      (J := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (C.familyCompactInterpolation C' h) where
  seam : Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ
    ((univ : Set D.domain.boundary.Point) ×ˢ ({0} : Set ℝ))) ⊆ source
  source_mem : (source : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ)))) ⊆
    (C.familyCompactInterpolationDomain C' h hh : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))))
  seam_mem : ∀ p ∈ source, ∀ x : D.domain.boundary.Point, (p.1, (p.2.1, (x, 0))) ∈ source

def embeddedFamilyCollar
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    C.EmbeddedFamilyCollar C' h hh := by
  apply Classical.choice
  obtain ⟨U, hK, hU, hseam, he, hd⟩ := C.exists_embedded_familyCompactInterpolation C' h hh
  exact ⟨⟨⟨U, (C.contMDiffOn_familyCompactInterpolation C' h hh).mono hU, he, hd⟩,
    hK, hU, hseam⟩⟩

namespace EmbeddedFamilyCollar
variable {C C' h}
  {hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
    (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)}
  (A : C.EmbeddedFamilyCollar C' h hh)

set_option backward.isDefEq.respectTransparency false in
theorem velocity_fst_zero (p : ℝ × (ℝ × E.domain.extension.Point)) :
    (A.toEmbeddedIsotopy.velocity p).1 = 0 := by
  by_cases hp : p ∈ A.toEmbeddedIsotopy.target
  · let q := A.toEmbeddedIsotopy.coordinates ⟨p, hp⟩
    have hq := A.toEmbeddedIsotopy.coordinates_mem ⟨p, hp⟩
    have hf := A.smooth.contMDiffAt (A.source.isOpen.mem_nhds hq)
    have hc := mfderiv_comp (f := C.familyCompactInterpolation C' h) (g := Prod.fst) q
      mdifferentiableAt_fst (hf.mdifferentiableAt (by simp))
    have hg := mfderiv_comp (f := fun z : ℝ × (ℝ × (D.domain.boundary.Point × ℝ)) => z.2)
      (g := Prod.fst) q
      (mdifferentiableAt_fst (I := 𝓘(ℝ, ℝ))
        (I' := (𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      (mdifferentiableAt_snd (I := 𝓘(ℝ, ℝ))
        (I' := (𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
    rw [mfderiv_fst] at hc
    rw [mfderiv_fst, mfderiv_snd] at hg
    have he := congrArg (fun L => L (1, (0, (0, 0)))) (hc.symm.trans hg)
    rw [CollarFamilyExtension.EmbeddedIsotopy.velocity, dite_eq_left hp]
    exact he
  · simp only [CollarFamilyExtension.EmbeddedIsotopy.velocity, dite_eq_right hp,
      Prod.fst_zero]

set_option backward.isDefEq.respectTransparency false in
theorem velocity_boundary (s t : ℝ) (y : E.domain.boundary.Point) :
    A.toEmbeddedIsotopy.velocity (s, (t, E.domain.boundaryInclusion.map y)) = 0 := by
  let p := (s, (t, E.domain.boundaryInclusion.map y))
  by_cases hp : p ∈ A.toEmbeddedIsotopy.target
  · let z : A.toEmbeddedIsotopy.target := ⟨p, hp⟩
    have he := A.toEmbeddedIsotopy.apply_coordinates z
    have hs : (A.toEmbeddedIsotopy.coordinates z).1 = s := congrArg Prod.fst he
    have ht : (A.toEmbeddedIsotopy.coordinates z).2.1 = t := congrArg (fun a => a.2.1) he
    have hseam := A.seam_mem _ (A.toEmbeddedIsotopy.coordinates_mem z) ((h t).boundaryEquiv.symm y)
    rw [hs, ht] at hseam
    have hf : C.familyCompactInterpolation C' h (s, (t, ((h t).boundaryEquiv.symm y, 0))) =
        (t, E.domain.boundaryInclusion.map y) := by
      simp [familyCompactInterpolation, C.compactPresentationInterpolation_boundary]
    have hc : A.toEmbeddedIsotopy.coordinates z = (s, (t, ((h t).boundaryEquiv.symm y, 0))) := by
      simpa only [hf] using A.toEmbeddedIsotopy.coordinates_apply
        (s, (t, ((h t).boundaryEquiv.symm y, 0))) hseam
    rw [CollarFamilyExtension.EmbeddedIsotopy.velocity, dite_eq_left hp]
    change mfderiv _ _ _ (A.toEmbeddedIsotopy.coordinates z) _ = 0
    rw [hc]
    have hi : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
        (fun u : ℝ => (u, (t, ((h t).boundaryEquiv.symm y, (0 : ℝ))))) s :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hf' := (A.smooth.contMDiffAt (A.source.isOpen.mem_nhds hseam)).mdifferentiableAt (by simp)
    have hm := mfderiv_comp (f := fun u : ℝ => (u, (t, ((h t).boundaryEquiv.symm y, (0 : ℝ)))))
      (g := C.familyCompactInterpolation C' h) s hf' hi
    have hz : (fun u : ℝ => C.familyCompactInterpolation C' h
        (u, (t, ((h t).boundaryEquiv.symm y, 0)))) = fun _ =>
          (t, E.domain.boundaryInclusion.map y) := by
      funext u
      simp [familyCompactInterpolation, C.compactPresentationInterpolation_boundary]
    change mfderiv _ _ (fun u : ℝ => C.familyCompactInterpolation C' h
      (u, (t, ((h t).boundaryEquiv.symm y, 0)))) s = _ at hm
    rw [hz, mfderiv_const, mfderiv_prod_left] at hm
    exact (congrArg (fun L => L (1 : ℝ)) hm).symm
  · dsimp only [p] at hp
    simp only [CollarFamilyExtension.EmbeddedIsotopy.velocity, dite_eq_right hp]

end EmbeddedFamilyCollar

set_option backward.isDefEq.respectTransparency false in
/-- One cutoff produces the actual collar velocity for every raw compact
presentation in the fixed-completion family. The family coordinate has
zero velocity. The interpolation ODE holds on a common two-sided collar
and on an open interval containing both correction-time endpoints. -/
theorem exists_compactlySupported_familyCollarVelocity
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
      ∃ (Z : ℝ → (p : ℝ × E.domain.extension.Point) →
          TangentSpace ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) p)
        (K : Set (ℝ × (ℝ × E.domain.extension.Point))),
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
          (((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)).tangent) ∞
          (fun p : ℝ × (ℝ × E.domain.extension.Point) => (⟨p.2, Z p.1 p.2⟩ :
            TangentBundle ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (ℝ × E.domain.extension.Point))) ∧
        IsCompact K ∧ (∀ p ∉ K, Z p.1 p.2 = 0) ∧
        (∀ s p, (Z s p).1 = 0) ∧
        (∀ s t (y : E.domain.boundary.Point), Z s (t, E.domain.boundaryInclusion.map y) = 0) ∧
        ∀ s ∈ Ioo (-ε) (1 + ε), ∀ t ∈ Icc (0 : ℝ) 1,
          ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
            HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
              (fun u => C.familyCompactInterpolation C' h (u, (t, q))) s
              ((1 : ℝ →L[ℝ] ℝ).smulRight
                (Z s (C.familyCompactInterpolation C' h (s, (t, q))))) := by
  let A := C.embeddedFamilyCollar C' h hh
  let B : Set (ℝ × (ℝ × E.domain.extension.Point)) :=
    Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ (E.domain.boundaryInclusion.map '' univ))
  have hB : IsCompact B := isCompact_Icc.prod (isCompact_Icc.prod
    (E.domain.isCompact_boundary.image E.domain.boundaryInclusion.map.contMDiff.continuous))
  have hBA : B ⊆ A.toEmbeddedIsotopy.target := by
    rintro ⟨s, t, z⟩ ⟨hs, ht, y, _, rfl⟩
    have hp : (s, (t, ((h t).boundaryEquiv.symm y, (0 : ℝ)))) ∈ A.source :=
      A.seam ⟨hs, ht, mem_univ _, mem_singleton 0⟩
    refine ⟨⟨(s, (t, ((h t).boundaryEquiv.symm y, 0))), hp⟩, ?_⟩
    simp [familyCompactInterpolation, C.compactPresentationInterpolation_boundary]
  let : LocallyCompactSpace (ModelProd ℝ (ModelProd ℝ (Model d))) := by
    change LocallyCompactSpace (ℝ × (ℝ × Model d))
    infer_instance
  obtain ⟨χ, V, hχ, hBV, hχone, hχcompact, hχsupp⟩ :=
    CollarExtension.exists_smooth_compact_cutoff
      (I := (𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) hB
      A.toEmbeddedIsotopy.target.isOpen hBA
  let U : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :=
    A.source ∩ (fun p => (p.1, C.familyCompactInterpolation C' h p)) ⁻¹' V
  have hU : IsOpen U := (contMDiff_fst.contMDiffOn.prodMk A.smooth).continuousOn
    |>.isOpen_inter_preimage A.source.isOpen V.isOpen
  let g : ℝ × ((Parameter × D.domain.boundary.Point) × ℝ) →
      ℝ × (ℝ × (D.domain.boundary.Point × ℝ)) :=
    fun p => (p.1, (p.2.1.1.val, (p.2.1.2, p.2.2)))
  have hg : Continuous g := by fun_prop
  have hseam : Icc (0 : ℝ) 1 ×ˢ
      ((univ : Set (Parameter × D.domain.boundary.Point)) ×ˢ ({0} : Set ℝ)) ⊆ g ⁻¹' U := by
    rintro ⟨s, ⟨t, x⟩, r⟩ ⟨hs, _, hr⟩
    have hr0 : r = 0 := hr
    subst r
    refine ⟨A.seam ⟨hs, t.property, mem_univ x, mem_singleton 0⟩, ?_⟩
    change (s, (t.val, C.compactPresentationInterpolation C' (h t.val) (s, (x, 0)))) ∈ V
    rw [C.compactPresentationInterpolation_boundary]
    exact hBV ⟨hs, t.property, ⟨(h t.val).boundaryEquiv x, mem_univ _, rfl⟩⟩
  obtain ⟨ε, hε, δ, hδ, hw⟩ := CollarExtension.exists_uniform_time_width
    (by simpa only [univ_prod_univ] using
      (isCompact_univ : IsCompact (univ : Set Parameter)).prod D.domain.isCompact_boundary)
    (hU.preimage hg) hseam
  let Z := fun s p => A.toEmbeddedIsotopy.supportedVelocity χ (s, p)
  refine ⟨ε, hε, δ, hδ, Z, tsupport χ,
    A.toEmbeddedIsotopy.contMDiff_supportedVelocity χ hχ hχsupp, hχcompact, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Z, CollarFamilyExtension.EmbeddedIsotopy.supportedVelocity,
      image_eq_zero_of_notMem_tsupport hp, zero_smul]
  · intro s p
    change χ (s, p) * (A.toEmbeddedIsotopy.velocity (s, p)).1 = 0
    rw [A.velocity_fst_zero, mul_zero]
  · intro s t y
    simp only [Z, CollarFamilyExtension.EmbeddedIsotopy.supportedVelocity,
      A.velocity_boundary, smul_zero]
  · intro s hs t ht q hq
    have hp : (s, (t, q)) ∈ U :=
      hw (show (s, ((⟨t, ht⟩, q.1), q.2)) ∈ Ioo (-ε) (1 + ε) ×ˢ
        ((univ : Set (Parameter × D.domain.boundary.Point)) ×ˢ Ioo (-δ) δ) from
          ⟨hs, mem_univ _, hq.2⟩)
    have he : Z s (C.familyCompactInterpolation C' h (s, (t, q))) =
        A.toEmbeddedIsotopy.velocity (s, C.familyCompactInterpolation C' h (s, (t, q))) := by
      dsimp only [Z, CollarFamilyExtension.EmbeddedIsotopy.supportedVelocity]
      rw [hχone _ hp.2, one_smul]
    rw [he]
    exact A.toEmbeddedIsotopy.hasMFDerivAt_apply s (t, q) hp.1

end Completion
end FsFltz.Geometry
