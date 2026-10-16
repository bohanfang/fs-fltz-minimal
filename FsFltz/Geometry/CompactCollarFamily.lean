import FsFltz.Geometry.CollarSmoothEvolution
import FsFltz.Geometry.CompletionFamilyCollar

/-!
# Coherent collar correction for compact presentation families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. All assertions in this module are conditional
foundations for supplied completions. They do not assert any toric target.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry

set_option backward.isDefEq.respectTransparency false in
private theorem retainingParameter_mfderiv_bijective
    {P M N A B F HP HM HN : Type}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace HP] [TopologicalSpace HM] [TopologicalSpace HN]
    {IP : ModelWithCorners ℝ A HP} {IM : ModelWithCorners ℝ B HM}
    {IN : ModelWithCorners ℝ F HN}
    [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    [TopologicalSpace N] [ChartedSpace HN N]
    {f : P × M → N} {p : P} {x : M}
    (hdf : MDifferentiableAt (IP.prod IM) IN f (p, x))
    (hd : Function.Bijective (mfderiv IM IN (fun y => f (p, y)) x)) :
    Function.Bijective (mfderiv (IP.prod IM) (IP.prod IN)
      (fun q => (q.1, f q)) (p, x)) := by
  let L : A × B →L[ℝ] F := mfderiv (IP.prod IM) IN f (p, x)
  have he : ∀ v : B, L (0, v) = mfderiv IM IN (fun y => f (p, y)) x v := by
    intro v
    have hm := mfderiv_comp (f := fun y : M => (p, y)) (g := f) x hdf
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    rw [mfderiv_prod_right] at hm
    exact (congrArg (fun K => K v) hm).symm
  rw [mfderiv_prodMk mdifferentiableAt_fst hdf, mfderiv_fst]
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have ha : a = a' := congrArg Prod.fst hab
    subst a'
    have hh : L (0, b - b') = 0 := by
      have hv := congrArg Prod.snd hab
      change L (a, b) = L (a, b') at hv
      have hz := sub_eq_zero.mpr hv
      rw [← map_sub] at hz
      have hs : (a, b) - (a, b') = (0, b - b') := by ext <;> simp
      rwa [hs] at hz
    have hb : b = b' := sub_eq_zero.mp (hd.1
      ((he (b - b')).symm.trans (hh.trans (map_zero _).symm)))
    exact Prod.ext rfl hb
  · rintro ⟨a, z⟩
    change A at a
    change F at z
    obtain ⟨b, hb⟩ := hd.2 (z - L (a, 0))
    refine ⟨(a, b), Prod.ext rfl ?_⟩
    change L (a, b) = z
    have hs : (a, b) = (a, 0) + (0, b) := by simp
    rw [hs, map_add, he, hb]
    exact add_sub_cancel _ _

set_option backward.isDefEq.respectTransparency false in
/-- A jointly smooth family with invertible spatial differential has a
jointly smooth local inverse after retaining the parameter. -/
theorem isLocalDiffeomorphAt_retainingParameter
    {P M N A B F : Type}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace P] [ChartedSpace A P] [IsManifold 𝓘(ℝ, A) ∞ P]
    [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    {f : P × M → N} {U : Set (P × M)} {p : P} {x : M}
    (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, A)).prod 𝓘(ℝ, B)) 𝓘(ℝ, F) ∞ f U)
    (hp : (p, x) ∈ U)
    (hd : Function.Bijective (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, F)
      (fun y => f (p, y)) x)) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, A)).prod 𝓘(ℝ, B))
      ((𝓘(ℝ, A)).prod 𝓘(ℝ, F)) ∞ (fun q => (q.1, f q)) (p, x) := by
  have hdf := (hf.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  have hbij := retainingParameter_mfderiv_bijective hdf hd
  have hpM : IsManifold ((𝓘(ℝ, A)).prod 𝓘(ℝ, B)) ∞ (P × M) := inferInstance
  have hpN : IsManifold ((𝓘(ℝ, A)).prod 𝓘(ℝ, F)) ∞ (P × N) := inferInstance
  let : ChartedSpace (A × B) (P × M) := prodChartedSpace A P B M
  let : ChartedSpace (A × F) (P × N) := prodChartedSpace A P F N
  have hg := contMDiff_fst.contMDiffOn.prodMk hf
  simp only [← modelWithCornersSelf_prod] at hg hbij hpM hpN ⊢
  exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold hU hg hp hbij

namespace Completion
open SmoothManifold

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : ℝ → DomainPresentationEquiv D.domain E.domain)

/-- The actual transition of every supplied presentation. -/
def familyCollarTransition (p : ℝ × (D.domain.boundary.Point × ℝ)) :
    E.domain.boundary.Point × ℝ := C.presentationCollarTransition C' (h p.1) p.2

def familyCollarTransitionDomain
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ)) where
  carrier := (fun p => p.2) ⁻¹' C.presentationCollarSourceDomain ∩
    (fun p => C'.inclusion.map ((h p.1).extensionEquiv
      (C.presentationCollarPoint p.2))) ⁻¹' C'.escapingBasin
  is_open' := by
    have hc : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × (D.domain.boundary.Point × ℝ) => C.presentationCollarPoint p.2)
        ((fun p : ℝ × (D.domain.boundary.Point × ℝ) => p.2) ⁻¹'
          C.presentationCollarSourceDomain) := C.contMDiffOn_presentationCollarPoint.comp
      contMDiff_snd.contMDiffOn (fun _ hp => hp)
    exact (C'.inclusion.map.contMDiff.comp_contMDiffOn
      (hh.comp_contMDiffOn (contMDiff_fst.contMDiffOn.prodMk hc))).continuousOn
      |>.isOpen_inter_preimage
        (C.presentationCollarSourceDomain.isOpen.preimage continuous_snd) C'.escapingBasin.isOpen

theorem mem_familyCollarTransitionDomain_boundary
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2))
    (t : ℝ) (x : D.domain.boundary.Point) :
    (t, (x, 0)) ∈ C.familyCollarTransitionDomain C' h hh :=
  C.mem_presentationCollarTransitionDomain_zero C' (h t) x

theorem contMDiffOn_familyCollarTransition
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.familyCollarTransition C' h) (C.familyCollarTransitionDomain C' h hh) := by
  let U := C.familyCollarTransitionDomain C' h hh
  have hc : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
      (fun p : U => C.presentationCollarPoint p.val.2) := by
    intro p
    exact (C.contMDiffOn_presentationCollarPoint.contMDiffAt
      (C.presentationCollarSourceDomain.isOpen.mem_nhds p.property.1)).comp p
      ((contMDiff_snd (I := 𝓘(ℝ, ℝ))).comp contMDiff_subtype_val p)
  have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : U => C'.endCoordinates
        ⟨C'.inclusion.map ((h p.val.1).extensionEquiv
          (C.presentationCollarPoint p.val.2)), p.property.2⟩) := by
    apply C'.contMDiff_endCoordinates.comp
    apply (ContMDiff.subtypeVal_comp_iff C'.escapingBasin _).mp
    exact C'.inclusion.map.contMDiff.comp
      (hh.comp ((contMDiff_fst.comp contMDiff_subtype_val).prodMk hc))
  have he : (fun p : U => C'.endCoordinates
      ⟨C'.inclusion.map ((h p.val.1).extensionEquiv
        (C.presentationCollarPoint p.val.2)), p.property.2⟩) =
      (fun p : U => C.familyCollarTransition C' h p.val) := by
    funext p
    have hz : C'.inclusion.map ((h p.val.1).extensionEquiv
        (C.presentationCollarPoint p.val.2)) ∈ C'.escapingBasin := p.property.2
    simp only [familyCollarTransition, presentationCollarTransition,
      dite_eq_left hz]
  rw [he] at hs
  intro p hp
  exact (contMDiffAt_subtype_iff.mp (hs ⟨p, hp⟩)).contMDiffWithinAt

/-- Two real coordinates are kept distinct: `s` is correction time and
`t` is the original compact-family parameter. -/
def familyCollarInterpolation (p : ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :
    E.domain.boundary.Point × ℝ :=
  C.presentationCollarInterpolation C' (h p.2.1) (p.1, p.2.2)

def familyCollarInterpolationDomain
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    TopologicalSpace.Opens (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) where
  carrier := (fun p => (p.2.1, (p.2.2.1, p.1 * p.2.2.2))) ⁻¹'
    C.familyCollarTransitionDomain C' h hh
  is_open' := (C.familyCollarTransitionDomain C' h hh).isOpen.preimage (by fun_prop)

theorem contMDiffOn_familyCollarInterpolation
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.familyCollarInterpolation C' h) (C.familyCollarInterpolationDomain C' h hh) := by
  have hi : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      (fun p : ℝ × (ℝ × (D.domain.boundary.Point × ℝ)) =>
        (p.2.1, (p.2.2.1, p.1 * p.2.2.2))) :=
    contMDiff_snd.fst.prodMk (contMDiff_snd.snd.fst.prodMk
      (contMDiff_fst.mul contMDiff_snd.snd.snd))
  have hf := (C.contMDiffOn_familyCollarTransition C' h hh).comp hi.contMDiffOn
    (fun _ hp => hp)
  intro p hp
  exact (hf p hp).fst.prodMk
    (((contMDiffWithinAt_const.sub (contMDiff_fst p).contMDiffWithinAt).mul
      (contMDiff_snd.snd.snd p).contMDiffWithinAt).add (hf p hp).snd)

def familyCompactInterpolation (p : ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :
    ℝ × E.domain.extension.Point :=
  (p.2.1, C.compactPresentationInterpolation C' (h p.2.1) (p.1, p.2.2))

def familyCompactInterpolationDomain
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    TopologicalSpace.Opens (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) where
  carrier := C.familyCollarInterpolationDomain C' h hh ∩
    (C.familyCollarInterpolation C' h) ⁻¹' C'.presentationCollarSourceDomain
  is_open' := (C.contMDiffOn_familyCollarInterpolation C' h hh).continuousOn
    |>.isOpen_inter_preimage (C.familyCollarInterpolationDomain C' h hh).isOpen
      C'.presentationCollarSourceDomain.isOpen

theorem mem_familyCompactInterpolationDomain_boundary
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2))
    (s t : ℝ) (x : D.domain.boundary.Point) :
    (s, (t, (x, 0))) ∈ C.familyCompactInterpolationDomain C' h hh := by
  refine ⟨?_, ?_⟩
  · change (t, (x, s * 0)) ∈ C.familyCollarTransitionDomain C' h hh
    simpa using C.mem_familyCollarTransitionDomain_boundary C' h hh t x
  · change C.presentationCollarInterpolation C' (h t) (s, (x, 0)) ∈
      C'.presentationCollarSourceDomain
    rw [C.presentationCollarInterpolation_boundary]
    exact ⟨E.domain.boundaryInclusion.map ((h t).boundaryEquiv x),
      (C'.endMap_zero _).symm⟩

theorem contMDiffOn_familyCompactInterpolation
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (C.familyCompactInterpolation C' h) (C.familyCompactInterpolationDomain C' h hh) :=
  contMDiff_snd.fst.contMDiffOn.prodMk (C'.contMDiffOn_presentationCollarPoint.comp
    ((C.contMDiffOn_familyCollarInterpolation C' h hh).mono inter_subset_left)
    (fun _ hp => hp.2))

set_option backward.isDefEq.respectTransparency false in
private theorem presentationCollarPoint_mfderiv_bijective
    {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) (x : D.domain.boundary.Point) :
    Function.Bijective (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) C.presentationCollarPoint (x, 0)) := by
  let l := C.inclusion_isLocalDiffeomorph (D.domain.boundaryInclusion.map x)
  have hs : IsLocalDiffeomorphAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ (C.compactCollarAt x) (x, 0) := by
    apply (C.endMap_isLocalDiffeomorph (x, 0)).comp
      𝓘(ℝ, Model d) D.domain.extension.Point
    apply l.localInverse.isLocalDiffeomorphAt
    rw [C.endMap_zero]
    exact l.localInverse_mem_source
  have he : C.presentationCollarPoint =ᶠ[𝓝 (x, (0 : ℝ))] C.compactCollarAt x := by
    have ht : Tendsto C.endMap (𝓝 (x, (0 : ℝ)))
        (𝓝 (C.inclusion.map (D.domain.boundaryInclusion.map x))) := by
      rw [← C.endMap_zero]
      exact C.smooth_endMap.continuous.continuousAt
    filter_upwards [l.localInverse_eventuallyEq_right.comp_tendsto ht] with q hq
    have hp : q ∈ C.presentationCollarSourceDomain := ⟨C.compactCollarAt x q, hq⟩
    apply C.inclusion.embedding.injective
    exact (C.inclusionMap_presentationCollarPoint q hp).trans hq.symm
  rw [he.mfderiv_eq]
  exact hs.mfderivToContinuousLinearEquiv (by simp) |>.bijective

set_option backward.isDefEq.respectTransparency false in
private theorem familyCompactInterpolation_slice_mfderiv_bijective
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) (x : D.domain.boundary.Point) :
    Function.Bijective (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d)
      (fun q => C.compactPresentationInterpolation C' (h t) (s, q)) (x, 0)) := by
  have hi := C.isLocalDiffeomorphAt_presentationCollarInterpolation C' (h t) s hs x
  have hc := C'.contMDiffOn_presentationCollarPoint.contMDiffAt
    (C'.presentationCollarSourceDomain.isOpen.mem_nhds
      (show ((h t).boundaryEquiv x, (0 : ℝ)) ∈ C'.presentationCollarSourceDomain from
        ⟨E.domain.boundaryInclusion.map _, (C'.endMap_zero _).symm⟩))
  have hcomp := mfderiv_comp (f := fun q => C.presentationCollarInterpolation C' (h t) (s, q))
    (g := C'.presentationCollarPoint) (x, 0)
    (by simpa only [C.presentationCollarInterpolation_boundary] using
      hc.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  change Function.Bijective (mfderiv _ _
    (C'.presentationCollarPoint ∘ (fun q => C.presentationCollarInterpolation C' (h t) (s, q))) _)
  rw [hcomp, C.presentationCollarInterpolation_boundary]
  exact (presentationCollarPoint_mfderiv_bijective C' _).comp
    (hi.mfderivToContinuousLinearEquiv (by simp)).bijective

/-- Retain correction time as well as the original family parameter. -/
def familyCompactInterpolationWithTime
    (p : ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :
    ℝ × (ℝ × E.domain.extension.Point) :=
  (p.1, C.familyCompactInterpolation C' h p)

set_option backward.isDefEq.respectTransparency false in
theorem isLocalDiffeomorphAt_familyCompactInterpolationWithTime
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) (x : D.domain.boundary.Point) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞
      (C.familyCompactInterpolationWithTime C' h) (s, (t, (x, 0))) := by
  let U := C.familyCompactInterpolationDomain C' h hh
  have hf := C.contMDiffOn_familyCompactInterpolation C' h hh
  let V : Set (ℝ × (D.domain.boundary.Point × ℝ)) := (fun q => (s, q)) ⁻¹' U
  have hV : IsOpen V := U.isOpen.preimage (continuous_const.prodMk continuous_id)
  have hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
      (fun q => (C.familyCompactInterpolation C' h (s, q)).2) V :=
    (contMDiff_snd.comp_contMDiffOn hf).comp
    (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    (fun _ hp => hp)
  have hp := C.mem_familyCompactInterpolationDomain_boundary C' h hh s t x
  have hi : IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun q => C.familyCompactInterpolation C' h (s, q)) (t, (x, 0)) := by
    have hq := C.familyCompactInterpolation_slice_mfderiv_bijective C' h s hs t x
    have hpB : IsManifold ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
        (D.domain.boundary.Point × ℝ) := inferInstance
    let : ChartedSpace (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ) :=
      prodChartedSpace (Model (d - 1)) D.domain.boundary.Point ℝ ℝ
    rw [← modelWithCornersSelf_prod] at hpB hg hq ⊢
    exact isLocalDiffeomorphAt_retainingParameter hV hg hp hq
  have hdf := (hf.contMDiffAt (U.isOpen.mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := retainingParameter_mfderiv_bijective hdf
    (hi.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hg := contMDiff_fst.contMDiffOn.prodMk hf
  have hpB : IsManifold ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))) ∞
      (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) := inferInstance
  have hpE : IsManifold ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞
      (ℝ × (ℝ × E.domain.extension.Point)) := inferInstance
  let : ChartedSpace (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ) :=
    prodChartedSpace (Model (d - 1)) D.domain.boundary.Point ℝ ℝ
  let : ChartedSpace (ℝ × (Model (d - 1) × ℝ)) (ℝ × (D.domain.boundary.Point × ℝ)) :=
    prodChartedSpace ℝ ℝ (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ)
  let : ChartedSpace (ℝ × Model d) (ℝ × E.domain.extension.Point) :=
    prodChartedSpace ℝ ℝ (Model d) E.domain.extension.Point
  let : ChartedSpace (ℝ × (ℝ × (Model (d - 1) × ℝ)))
      (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :=
    prodChartedSpace ℝ ℝ (ℝ × (Model (d - 1) × ℝ)) (ℝ × (D.domain.boundary.Point × ℝ))
  let : ChartedSpace (ℝ × (ℝ × Model d)) (ℝ × (ℝ × E.domain.extension.Point)) :=
    prodChartedSpace ℝ ℝ (ℝ × Model d) (ℝ × E.domain.extension.Point)
  simp only [← modelWithCornersSelf_prod] at hg hd hpB hpE ⊢
  exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold U.isOpen hg hp hd

theorem exists_embedded_familyCompactInterpolation
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ∃ U : TopologicalSpace.Opens (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))),
      (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ
        ((univ : Set D.domain.boundary.Point) ×ˢ ({0} : Set ℝ)))) ⊆
          (U : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ)))) ∧
      (U : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ)))) ⊆
        (C.familyCompactInterpolationDomain C' h hh : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ)))) ∧
      (∀ p ∈ U, ∀ x : D.domain.boundary.Point, (p.1, (p.2.1, (x, 0))) ∈ U) ∧
      Topology.IsOpenEmbedding (fun p : U => C.familyCompactInterpolationWithTime C' h p.val) ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
        ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞
        (C.familyCompactInterpolationWithTime C' h) U := by
  let K : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :=
    Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ ({0} : Set ℝ)))
  have hK : IsCompact K := isCompact_Icc.prod
    (isCompact_Icc.prod (D.domain.isCompact_boundary.prod isCompact_singleton))
  have hloc : ∀ p ∈ K, IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞
      (C.familyCompactInterpolationWithTime C' h) p := by
    rintro ⟨s, t, x, r⟩ hp
    have hr : r = 0 := hp.2.2.2
    subst r
    exact C.isLocalDiffeomorphAt_familyCompactInterpolationWithTime C' h hh s hp.1 t x
  have hinj : InjOn (C.familyCompactInterpolationWithTime C' h) K := by
    rintro ⟨s, t, x, r⟩ hp ⟨u, v, y, a⟩ hq he
    have hr : r = 0 := hp.2.2.2
    have ha : a = 0 := hq.2.2.2
    subst r
    subst a
    have hs : s = u := congrArg Prod.fst he
    have ht : t = v := congrArg (fun z => z.2.1) he
    subst u
    subst v
    have hx := congrArg (fun z => z.2.2) he
    change C.compactPresentationInterpolation C' (h t) (s, (x, 0)) =
      C.compactPresentationInterpolation C' (h t) (s, (y, 0)) at hx
    rw [C.compactPresentationInterpolation_boundary,
      C.compactPresentationInterpolation_boundary] at hx
    have hxy := (h t).boundaryEquiv.injective (E.domain.boundaryInclusion.embedding.injective hx)
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext hxy rfl))
  obtain ⟨V, hV, hKV, hVi⟩ := hinj.exists_isOpen_superset hK
    (fun p hp => (hloc p hp).contMDiffAt.continuousAt) (by
      intro p hp
      obtain ⟨e, he, heq⟩ := hloc p hp
      refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
      intro a ha b hb hab
      exact e.toPartialEquiv.injOn ha hb ((heq ha).symm.trans (hab.trans (heq hb))))
  let L : TopologicalSpace.Opens (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :=
    { carrier := {p | IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
        ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞
        (C.familyCompactInterpolationWithTime C' h) p}
      is_open' := by
        apply isOpen_iff_mem_nhds.mpr
        rintro p ⟨e, hp, he⟩
        exact mem_of_superset (e.open_source.mem_nhds hp) (fun q hq => ⟨e, hq, he⟩) }
  let W : TopologicalSpace.Opens (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :=
    ⟨V ∩ (C.familyCompactInterpolationDomain C' h hh ∩ L),
      hV.inter ((C.familyCompactInterpolationDomain C' h hh).isOpen.inter L.isOpen)⟩
  have hKW : K ⊆ W := by
    rintro ⟨s, t, x, r⟩ hp
    have hr : r = 0 := hp.2.2.2
    subst r
    exact ⟨hKV hp, C.mem_familyCompactInterpolationDomain_boundary C' h hh s t x,
      hloc _ hp⟩
  obtain ⟨S, T, hS, hT, hIS, hKT, hST⟩ := generalized_tube_lemma isCompact_Icc
    (isCompact_Icc.prod (D.domain.isCompact_boundary.prod isCompact_singleton)) W.isOpen hKW
  obtain ⟨A, B, hA, _, hIA, hBB, hAB⟩ := generalized_tube_lemma isCompact_Icc
    (D.domain.isCompact_boundary.prod isCompact_singleton) hT hKT
  let U : TopologicalSpace.Opens (ℝ × (ℝ × (D.domain.boundary.Point × ℝ))) :=
    ⟨W ∩ (S ×ˢ (A ×ˢ univ)), W.isOpen.inter (hS.prod (hA.prod isOpen_univ))⟩
  have hUW : (U : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ)))) ⊆
      (W : Set (ℝ × (ℝ × (D.domain.boundary.Point × ℝ)))) := inter_subset_left
  have hd : IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞
      (C.familyCompactInterpolationWithTime C' h) U := fun p => (hUW p.property).2.2
  have hl : IsLocalHomeomorph (fun p : U => C.familyCompactInterpolationWithTime C' h p.val) := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact hd.isLocalHomeomorphOn.comp U.isOpenEmbedding'.isLocalHomeomorph.isLocalHomeomorphOn
      (fun p _ => p.property)
  refine ⟨U, ?_, (fun p hp => (hUW hp).2.1), ?_,
    hl.isOpenEmbedding_of_injective (Set.injOn_iff_injective.mp
      (hVi.mono (hUW.trans inter_subset_left))), hd⟩
  · intro p hp
    exact ⟨hKW hp, hIS hp.1, hIA hp.2.1, mem_univ _⟩
  · intro p hp x
    exact ⟨hST ⟨hp.2.1, hAB ⟨hp.2.2.1, hBB ⟨mem_univ x, mem_singleton 0⟩⟩⟩,
      hp.2.1, hp.2.2.1, mem_univ _⟩

end Completion
end FsFltz.Geometry
