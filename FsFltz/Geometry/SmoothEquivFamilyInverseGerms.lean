import FsFltz.Geometry.IntrinsicBundleNativeData
import FsFltz.Geometry.ParameterGraphImmersion
import FsFltz.Geometry.LocalInverse

/-!
# Smooth inverse germs for a family of diffeomorphisms

Source: `geometric-part-fsf-proof.tex`, marked deformation, lines 1288–1303.
The parameter graph inverse function theorem gives real smooth germs for
the inverses of the very same slice maps, including both interval endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicSmoothBundle
open SmoothManifold

/-- Joint real smooth germs of a family of diffeomorphisms imply joint
real smooth germs of its actual inverse family. -/
theorem HasSmoothManifoldTargetFamilyOn.inverse {d : ℕ}
    (M N : SmoothManifold d) (e : Parameter → M.SmoothEquiv N)
    (hf : HasSmoothManifoldTargetFamilyOn M N univ (fun t => e t)) :
    HasSmoothManifoldTargetFamilyOn N M univ (fun t => (e t).symm) := by
  classical
  intro t _ y
  let x := (e t).symm y
  obtain ⟨U, hpU, β, hβ, heβ⟩ := hf t (mem_univ _) x
  let f : ℝ → M.Point → N.Point := fun s z =>
    if h : (s, z) ∈ U then β ⟨(s, z), h⟩ else e parameterZero z
  have hfU : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × M.Point => f p.1 p.2) U := by
    intro p hp
    have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun q : U => f q.val.1 q.val.2) := by
      convert hβ using 1
      funext q
      exact dite_eq_left q.property
    exact ((contMDiffAt_subtype_iff
      (f := fun p : ℝ × M.Point => f p.1 p.2) (x := (⟨p, hp⟩ : U))).mp
      hs.contMDiffAt).contMDiffWithinAt
  have hfe (s : Parameter) (z : M.Point) (hz : (s.val, z) ∈ U) :
      f s.val z = e s z := by
    rw [show f s.val z = β ⟨(s.val, z), hz⟩ from dite_eq_left hz]
    exact heβ s (mem_univ _) z hz
  have hslice : f t.val =ᶠ[𝓝 x] e t := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (U.isOpen.mem_nhds hpU)] with z hz
    exact hfe t z hz
  have hd := hslice.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, Model d))
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (f t.val) x =
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (e t) x at hd
  let g : ℝ × M.Point → ℝ × N.Point := fun p => (p.1, f p.1 p.2)
  have hgs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ g U := contMDiff_fst.contMDiffOn.prodMk hfU
  have hgi : Function.Injective (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) g (t.val, x)) := by
    apply (M.injective_mfderiv_parameterGraph_iff N
      ((hfU.contMDiffAt (U.isOpen.mem_nhds hpU)).mdifferentiableAt (by simp))).mpr
    rw [hd]
    exact ((e t).isInvertible_mfderiv (x := x) (by simp)).injective
  have hgb : Function.Bijective (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) g (t.val, x)) :=
    ⟨hgi, LinearMap.injective_iff_surjective.mp hgi⟩
  have hlocal : IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ g (t.val, x) := by
    have hM : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ (ℝ × M.Point) := inferInstance
    have hN : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ (ℝ × N.Point) := inferInstance
    let : ChartedSpace (ℝ × Model d) (ℝ × M.Point) := prodChartedSpace ℝ ℝ (Model d) M.Point
    let : ChartedSpace (ℝ × Model d) (ℝ × N.Point) := prodChartedSpace ℝ ℝ (Model d) N.Point
    rw [← modelWithCornersSelf_prod] at hM hN
    let : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × M.Point) := hM
    let : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × N.Point) := hN
    rw [← modelWithCornersSelf_prod] at hgs hgb ⊢
    exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold U.isOpen hgs hpU hgb
  have hgy : g (t.val, x) = (t.val, y) := by
    change (t.val, f t.val x) = _
    rw [hfe t x hpU]
    exact Prod.ext rfl ((e t).apply_symm_apply y)
  let l := hlocal.localInverse
  let V : TopologicalSpace.Opens (ℝ × N.Point) :=
    ⟨l.source ∩ l ⁻¹' U,
      hlocal.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
        l.open_source U.isOpen⟩
  have hyV : (t.val, y) ∈ V := by
    rw [← hgy]
    refine ⟨hlocal.localInverse_mem_source, ?_⟩
    change hlocal.localInverse (g (t.val, x)) ∈ U
    rw [hlocal.localInverse_left_inv hlocal.localInverse_mem_target]
    exact hpU
  let a : V → M.Point := fun p => (l p.val).2
  have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ a := by
    intro p
    exact (contMDiffAt_snd.comp p.val
      (hlocal.localInverse_contMDiffOn.contMDiffAt
        (l.open_source.mem_nhds p.property.1))).comp p contMDiff_subtype_val.contMDiffAt
  refine ⟨V, hyV, a, ha, ?_⟩
  intro s _ z hz
  have hr : g (l (s.val, z)) = (s.val, z) := hlocal.localInverse_right_inv hz.1
  have ht : (l (s.val, z)).1 = s.val := congrArg Prod.fst hr
  have hv : f s.val (l (s.val, z)).2 = z := by
    have h := congrArg Prod.snd hr
    change f (l (s.val, z)).1 (l (s.val, z)).2 = z at h
    rwa [ht] at h
  have hmem : (s.val, (l (s.val, z)).2) ∈ U := by
    have h := hz.2
    change ((l (s.val, z)).1, (l (s.val, z)).2) ∈ U at h
    rwa [ht] at h
  change (l (s.val, z)).2 = (e s).symm z
  apply (e s).injective
  change e s (l (s.val, z)).2 = e s ((e s).symm z)
  rw [(e s).apply_symm_apply, ← hfe s _ hmem]
  exact hv

end FsFltz.Geometry.IntrinsicSmoothBundle
