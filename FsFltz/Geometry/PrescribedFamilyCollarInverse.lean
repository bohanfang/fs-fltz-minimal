import FsFltz.Geometry.PrescribedFamilyCollarGerms
import FsFltz.Geometry.LocalInverse

/-!
# Parametric inverse germs for prescribed completion collars

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. The actual transported end map in a smooth
completed family has jointly smooth germs. Its spatial derivative is
invertible because each original slice is a diffeomorphism followed by
the actual completion end parametrization. Retaining the parameter gives
a triangular invertible derivative and hence an actual smooth local inverse.
An interval collar square then produces target-valued neighborhood germs
of that same comparison, on both sides of the seam. No negative-radius
reference end square or joint inverse is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

/-- An invertible spatial derivative makes the parameter-retaining map a
local diffeomorphism. The full derivative is triangular, and its dimension
equality follows from the supplied spatial isomorphism. -/
theorem isLocalDiffeomorphAt_parameterMap_of_bijective_slice
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, F) ∞ N]
    (g : ℝ × M → N)
    (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ g)
    (t : ℝ) (x : M)
    (hd : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y => g (t, y)) x)) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ∞ (fun q : ℝ × M => (q.1, g q)) (t, x) := by
  have hgd := (hg (t, x)).mdifferentiableAt (by simp)
  have hinj : Function.Injective (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F))
      (fun q : ℝ × M => (q.1, g q)) (t, x)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ he
    rw [mfderiv_prodMk mdifferentiableAt_fst hgd, mfderiv_fst] at he
    have hu : u = 0 := congrArg Prod.fst he
    subst u
    have hv := congrArg Prod.snd he
    have hm := mfderiv_comp (f := fun y : M => (t, y)) (g := g) x hgd
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    rw [mfderiv_prod_right] at hm
    have hv' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y => g (t, y)) x v = 0 :=
      (congrArg (fun A => A v) hm).trans hv
    exact Prod.ext rfl (hd.1 (hv'.trans (map_zero _).symm))
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F :=
    (LinearEquiv.ofBijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F)
      (fun y => g (t, y)) x).toLinearMap hd).finrank_eq
  have hbij : Function.Bijective (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F))
      (fun q : ℝ × M => (q.1, g q)) (t, x)) := by
    refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
    change Module.finrank ℝ (ℝ × E) = Module.finrank ℝ (ℝ × F)
    simp only [Module.finrank_prod, Module.finrank_self, hdim]
  have hsm := contMDiff_fst.prodMk hg
  have hM : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ∞ (ℝ × M) := inferInstance
  have hN : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ∞ (ℝ × N) := inferInstance
  let : ChartedSpace (ℝ × E) (ℝ × M) := prodChartedSpace ℝ ℝ E M
  let : ChartedSpace (ℝ × F) (ℝ × N) := prodChartedSpace ℝ ℝ F N
  simp only [← modelWithCornersSelf_prod] at hsm hbij hM hN ⊢
  exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    isOpen_univ hsm.contMDiffOn (mem_univ _) hbij

namespace CompletionPresentationEquiv

variable {d : ℕ} {D E : LiouvilleDomain d}
  {C : Completion D} {C' : Completion E}
  {h : DomainPresentationEquiv D.domain E.domain}

/-- Every prescribed transported end slice is a local diffeomorphism at
every real radius, from the actual end parametrization and presentation
diffeomorphisms. No family regularity is used in this spatial calculation. -/
theorem isLocalDiffeomorph_prescribedEndMap
    (p : CompletionPresentationEquiv C C' h) :
    IsLocalDiffeomorph ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ p.prescribedEndMap := by
  let B := h.boundaryEquiv.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  intro q
  exact ((B.isLocalDiffeomorph q).comp 𝓘(ℝ, Model d) C'.ambient.manifold.Point
    (C'.endMap_isLocalDiffeomorph (B q))).comp 𝓘(ℝ, Model d) C.ambient.manifold.Point
      (p.equiv.symm.isLocalDiffeomorph (C'.endMap (B q)))

end CompletionPresentationEquiv

namespace Completion

/-- A smooth target collar square produces genuine neighborhood germs of
the same interval comparison on both sides of the source completion seam.
The jointly smooth source collar and its parameter-dependent inverse are
constructed from the original transported completed primitive family.
Neither joint comparison-map smoothness nor a joint inverse is an input. -/
theorem exists_familyMap_germ_on_end_of_collar_square {d e : ℕ}
    {D : LiouvilleDomain d} (C : Completion D)
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (hα : C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive))
    (N : SmoothManifold e)
    (f : Parameter → C.ambient.manifold.Point → N.Point)
    (β : ℝ → D.domain.boundary.Point × ℝ → N.Point)
    (hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × (D.domain.boundary.Point × ℝ) => β q.1 q.2))
    (δ : ℝ) (hδ : 0 < δ)
    (hsquare : ∀ (t : Parameter) b r, r ∈ Ioo (-δ) δ →
      f t ((p t).prescribedEndMap (b, r)) = β t.val (b, r)) :
    ∀ (t : Parameter) b,
      ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
        (t.val, C.endMap (b, 0)) ∈ U ∧ ∃ a : U → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a ∧
          ∀ (s : Parameter) z (hz : (s.val, z) ∈ U),
            a ⟨(s.val, z), hz⟩ = f s z := by
  obtain ⟨ε, hε, γ, hγ, heγ⟩ := C.exists_prescribedFamily_collar_germ E C' h p hα
  intro t b
  have heq : (fun q : D.domain.boundary.Point × ℝ => γ t.val q) =ᶠ[𝓝 (b, 0)]
      (p t).prescribedEndMap := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩))] with q hq
    exact heγ t q.1 q.2 hq
  have hbij : Function.Bijective (mfderiv
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (fun q : D.domain.boundary.Point × ℝ => γ t.val q) (b, 0)) := by
    rw [heq.mfderiv_eq]
    exact (tangentSpaceCast 𝓘(ℝ, Model d) ((p t).prescribedEndMap (b, 0))
      (γ t.val (b, 0))).bijective.comp
      ((((p t).isLocalDiffeomorph_prescribedEndMap (b, 0)).mfderivToContinuousLinearEquiv
        (by simp)).bijective)
  let G : ℝ × (D.domain.boundary.Point × ℝ) → ℝ × C.ambient.manifold.Point :=
    fun q => (q.1, γ q.1 q.2)
  have hl : IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ G (t.val, (b, 0)) := by
    have hM : IsManifold ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
        (D.domain.boundary.Point × ℝ) := inferInstance
    let : ChartedSpace (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ) :=
      prodChartedSpace (Model (d - 1)) D.domain.boundary.Point ℝ ℝ
    rw [← modelWithCornersSelf_prod] at hM hγ hbij ⊢
    exact isLocalDiffeomorphAt_parameterMap_of_bijective_slice
      (fun q : ℝ × (D.domain.boundary.Point × ℝ) => γ q.1 q.2) hγ t.val (b, 0) hbij
  let ρ := min ε δ
  have hρ : 0 < ρ := lt_min hε hδ
  let A : Set (ℝ × (D.domain.boundary.Point × ℝ)) := univ ×ˢ (univ ×ˢ Ioo (-ρ) ρ)
  have hA : IsOpen A := isOpen_univ.prod (isOpen_univ.prod isOpen_Ioo)
  let U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
    ⟨hl.localInverse.source ∩ hl.localInverse ⁻¹' A,
      hl.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
        hl.localInverse.open_source hA⟩
  have hzero : G (t.val, (b, 0)) = (t.val, C.endMap (b, 0)) := by
    dsimp only [G]
    rw [heγ t b 0 ⟨by linarith, hε⟩,
      (p t).prescribedEndMap_nonnegative b 0 (le_refl _)]
  have hpU : (t.val, C.endMap (b, 0)) ∈ U := by
    rw [← hzero]
    refine ⟨hl.localInverse_mem_source, ?_⟩
    change hl.localInverse (G (t.val, (b, 0))) ∈ A
    rw [hl.localInverse_left_inv hl.localInverse_mem_target]
    exact ⟨mem_univ _, mem_univ _, by linarith, hρ⟩
  let a : U → N.Point := fun q =>
    β (hl.localInverse q.val).1 (hl.localInverse q.val).2
  have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a := by
    intro q
    exact (hβ _).comp q
      ((hl.localInverse_contMDiffOn.contMDiffAt
        (hl.localInverse.open_source.mem_nhds q.property.1)).comp q
          contMDiff_subtype_val.contMDiffAt)
  refine ⟨U, hpU, a, ha, ?_⟩
  intro s z hz
  let v := hl.localInverse (s.val, z)
  have hv : G v = (s.val, z) := hl.localInverse_right_inv hz.1
  have ht : v.1 = s.val := congrArg Prod.fst hv
  have hz' : γ s.val v.2 = z := by
    have hh := congrArg Prod.snd hv
    change γ v.1 v.2 = z at hh
    rwa [ht] at hh
  have hrρ : v.2.2 ∈ Ioo (-ρ) ρ := hz.2.2.2
  have hrε : v.2.2 ∈ Ioo (-ε) ε := by
    constructor <;> linarith [min_le_left ε δ, hrρ.1, hrρ.2]
  have hrδ : v.2.2 ∈ Ioo (-δ) δ := by
    constructor <;> linarith [min_le_right ε δ, hrρ.1, hrρ.2]
  change β v.1 v.2 = f s z
  rw [ht]
  have hpz : (p s).prescribedEndMap v.2 = z := (heγ s v.2.1 v.2.2 hrε).symm.trans hz'
  rw [← hsquare s v.2.1 v.2.2 hrδ, hpz]

end Completion
end FsFltz.Geometry
