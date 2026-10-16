import FsFltz.Geometry.CompactCollarNormalization
import FsFltz.Geometry.LocalInverse
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Smooth interpolation of an existing compact collar presentation

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and `sec:lean`,
lines 788–814. The supplied compact presentation determines the transition.
Coherent inverse maps on the actual open images produce a single transition
representative near the whole boundary. The interpolation
`H(t,x,r) = (f₁(x,t*r), (1-t)*r + f₂(x,t*r))` is jointly smooth and connects
the intrinsic radius-preserving comparison to the supplied presentation.

The collar-interior extension and relative choices for varying completions
remain separate foundations. A common open neighborhood of the whole compact
parameter-boundary seam is produced on which the augmented interpolation is
an open embedding, with smooth local inverses. No geometric endpoint theorem
is asserted.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : DomainPresentationEquiv D.domain E.domain)

/-- The coherent inverse of the compact inclusion on its actual open image.
The boundary inclusion is only a total-function fallback outside that image. -/
def presentationCollarPoint (q : D.domain.boundary.Point × ℝ) :
    D.domain.extension.Point :=
  if hq : C.endMap q ∈ C.inclusionImage then
    C.inclusionCoordinates ⟨C.endMap q, hq⟩
  else D.domain.boundaryInclusion.map q.1

@[simp] theorem presentationCollarPoint_zero (x : D.domain.boundary.Point) :
    C.presentationCollarPoint (x, 0) = D.domain.boundaryInclusion.map x := by
  have hx : C.endMap (x, 0) ∈ C.inclusionImage :=
    ⟨D.domain.boundaryInclusion.map x, (C.endMap_zero x).symm⟩
  rw [presentationCollarPoint, dite_eq_left hx]
  apply C.inclusion.embedding.injective
  rw [C.inclusionMap_inclusionCoordinates]
  exact C.endMap_zero x

/-- The actual open domain of the coherent compact collar inverse. -/
def presentationCollarSourceDomain : TopologicalSpace.Opens (D.domain.boundary.Point × ℝ) where
  carrier := C.endMap ⁻¹' C.inclusionImage
  is_open' := C.inclusionImage.isOpen.preimage C.smooth_endMap.continuous

theorem contMDiffOn_presentationCollarPoint :
    ContMDiffOn ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
      C.presentationCollarPoint C.presentationCollarSourceDomain := by
  have hs : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞
      (fun q : C.presentationCollarSourceDomain =>
        C.inclusionCoordinates ⟨C.endMap q.val, q.property⟩) := by
    apply C.contMDiff_inclusionCoordinates.comp
    apply (ContMDiff.subtypeVal_comp_iff C.inclusionImage _).mp
    exact C.smooth_endMap.comp contMDiff_subtype_val
  have he : (fun q : C.presentationCollarSourceDomain =>
      C.inclusionCoordinates ⟨C.endMap q.val, q.property⟩) =
      (fun q : C.presentationCollarSourceDomain => C.presentationCollarPoint q.val) := by
    funext q
    have hq : C.endMap q.val ∈ C.inclusionImage := q.property
    simp only [presentationCollarPoint, dite_eq_left hq]
  rw [he] at hs
  intro q hq
  exact (contMDiffAt_subtype_iff.mp (hs ⟨q, hq⟩)).contMDiffWithinAt

theorem inclusionMap_presentationCollarPoint
    (q : D.domain.boundary.Point × ℝ) (hq : q ∈ C.presentationCollarSourceDomain) :
    C.inclusion.map (C.presentationCollarPoint q) = C.endMap q := by
  have hp : C.endMap q ∈ C.inclusionImage := hq
  rw [presentationCollarPoint, dite_eq_left hp, C.inclusionMap_inclusionCoordinates]

/-- One coherent transition representative, using the unique inverse end
coordinates wherever they are defined. All claims concern its proved open
neighborhood of the boundary, rather than the fallback outside that set. -/
def presentationCollarTransition (q : D.domain.boundary.Point × ℝ) :
    E.domain.boundary.Point × ℝ :=
  let z := C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint q))
  if hz : z ∈ C'.escapingBasin then C'.endCoordinates ⟨z, hz⟩
  else (h.boundaryEquiv q.1, 0)

/-- The transition's open domain is constructed from the two actual inverse
images. It contains the entire boundary and needs no collar compatibility
hypothesis on the original compact presentation. -/
def presentationCollarTransitionDomain :
    TopologicalSpace.Opens (D.domain.boundary.Point × ℝ) where
  carrier := C.presentationCollarSourceDomain ∩
    (fun q => C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint q))) ⁻¹'
      C'.escapingBasin
  is_open' := (C'.inclusion.map.contMDiff.comp_contMDiffOn
      (h.extensionEquiv.contMDiff.comp_contMDiffOn C.contMDiffOn_presentationCollarPoint)).continuousOn
    |>.isOpen_inter_preimage C.presentationCollarSourceDomain.isOpen C'.escapingBasin.isOpen

theorem mem_presentationCollarTransitionDomain_zero (x : D.domain.boundary.Point) :
    (x, 0) ∈ C.presentationCollarTransitionDomain C' h := by
  constructor
  · exact ⟨D.domain.boundaryInclusion.map x, (C.endMap_zero x).symm⟩
  · change C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint (x, 0))) ∈
      C'.escapingBasin
    rw [C.presentationCollarPoint_zero, h.boundary_square]
    exact ⟨(h.boundaryEquiv x, 0), C'.endMap_zero (h.boundaryEquiv x)⟩

theorem endMap_presentationCollarTransition (q : D.domain.boundary.Point × ℝ)
    (hq : q ∈ C.presentationCollarTransitionDomain C' h) :
    C'.endMap (C.presentationCollarTransition C' h q) =
      C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint q)) := by
  have hz : C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint q)) ∈
      C'.escapingBasin := hq.2
  rw [presentationCollarTransition, dite_eq_left hz, C'.endMap_endCoordinates]

theorem contMDiffOn_presentationCollarTransition :
    ContMDiffOn ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.presentationCollarTransition C' h) (C.presentationCollarTransitionDomain C' h) := by
  let U := C.presentationCollarTransitionDomain C' h
  have hp : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
      (fun q : U => C.presentationCollarPoint q.val) := by
    intro q
    exact (C.contMDiffOn_presentationCollarPoint.contMDiffAt
      (C.presentationCollarSourceDomain.isOpen.mem_nhds q.property.1)).comp q
        (contMDiff_subtype_val q)
  have hs : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : U => C'.endCoordinates
        ⟨C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint q.val)), q.property.2⟩) := by
    apply C'.contMDiff_endCoordinates.comp
    apply (ContMDiff.subtypeVal_comp_iff C'.escapingBasin _).mp
    exact C'.inclusion.map.contMDiff.comp (h.extensionEquiv.contMDiff.comp hp)
  have he : (fun q : U => C'.endCoordinates
      ⟨C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint q.val)), q.property.2⟩) =
      (fun q : U => C.presentationCollarTransition C' h q.val) := by
    funext q
    have hq : C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint q.val)) ∈
        C'.escapingBasin := q.property.2
    simp only [presentationCollarTransition, dite_eq_left hq]
  rw [he] at hs
  intro q hq
  exact (contMDiffAt_subtype_iff.mp (hs ⟨q, hq⟩)).contMDiffWithinAt

/-- Carrier preservation gives the exact side equation on the whole
constructed open collar domain, rather than only a first-order condition. -/
theorem presentationCollarTransition_side (q : D.domain.boundary.Point × ℝ)
    (hq : q ∈ C.presentationCollarTransitionDomain C' h) :
    (C.presentationCollarTransition C' h q).2 ≤ 0 ↔ q.2 ≤ 0 := by
  rw [← C'.endMap_mem_compact_iff, C.endMap_presentationCollarTransition C' h q hq]
  rw [C'.inclusion.embedding.injective.mem_set_image, h.mem_carrier_iff]
  rw [← C.inclusion.embedding.injective.mem_set_image,
    C.inclusionMap_presentationCollarPoint q hq.1, C.endMap_mem_compact_iff]

@[simp] theorem presentationCollarTransition_zero (x : D.domain.boundary.Point) :
    C.presentationCollarTransition C' h (x, 0) = (h.boundaryEquiv x, 0) := by
  have hz : C'.inclusion.map (h.extensionEquiv
      (C.presentationCollarPoint (x, 0))) ∈ C'.escapingBasin := by
    rw [C.presentationCollarPoint_zero, h.boundary_square]
    exact ⟨(h.boundaryEquiv x, 0), C'.endMap_zero (h.boundaryEquiv x)⟩
  rw [presentationCollarTransition, dite_eq_left hz]
  apply C'.endMap_injective
  rw [C'.endMap_endCoordinates]
  change C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint (x, 0))) = _
  rw [C.presentationCollarPoint_zero, h.boundary_square, C'.endMap_zero]

/-- The single coherent inverse representative equals every previously
constructed local germ near its basepoint. -/
theorem presentationCollarTransition_eventuallyEq (x : D.domain.boundary.Point) :
    C.presentationCollarTransition C' h =ᶠ[𝓝 (x, (0 : ℝ))]
      C.compactCollarTransitionAt C' h x := by
  filter_upwards [C.compactCollarTransitionAt_equations_eventually C' h x] with q hq
  have hm : C.endMap q ∈ C.inclusionImage := ⟨C.compactCollarAt x q, hq.1⟩
  have hp : C.presentationCollarPoint q = C.compactCollarAt x q := by
    rw [presentationCollarPoint, dite_eq_left hm]
    apply C.inclusion.embedding.injective
    rw [C.inclusionMap_inclusionCoordinates, hq.1]
  have hz : C'.inclusion.map (h.extensionEquiv
      (C.presentationCollarPoint q)) ∈ C'.escapingBasin := by
    rw [hp]
    exact ⟨C.compactCollarTransitionAt C' h x q, hq.2⟩
  rw [presentationCollarTransition, dite_eq_left hz]
  apply C'.endMap_injective
  rw [C'.endMap_endCoordinates]
  change C'.inclusion.map (h.extensionEquiv (C.presentationCollarPoint q)) = _
  rw [hp, hq.2]

theorem contMDiffAt_presentationCollarTransition (x : D.domain.boundary.Point) :
    ContMDiffAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.presentationCollarTransition C' h) (x, 0) :=
  (C.contMDiffAt_compactCollarTransitionAt C' h x).congr_of_eventuallyEq
    (C.presentationCollarTransition_eventuallyEq C' h x)

theorem presentationCollarTransition_side_eventually (x : D.domain.boundary.Point) :
    ∀ᶠ q in 𝓝 (x, (0 : ℝ)),
      (C.presentationCollarTransition C' h q).2 ≤ 0 ↔ q.2 ≤ 0 := by
  filter_upwards [C.presentationCollarTransition_eventuallyEq C' h x,
    C.compactCollarTransitionAt_side_eventually C' h x] with q he hs
  rwa [he]

/-- Smooth interpolation of the coherent transition. It is the exact
intrinsic collar comparison at parameter zero and the exact supplied
transition at parameter one. -/
def presentationCollarInterpolation (p : ℝ × (D.domain.boundary.Point × ℝ)) :
    E.domain.boundary.Point × ℝ :=
  let z := C.presentationCollarTransition C' h (p.2.1, p.1 * p.2.2)
  (z.1, (1 - p.1) * p.2.2 + z.2)

@[simp] theorem presentationCollarInterpolation_zero (q : D.domain.boundary.Point × ℝ) :
    C.presentationCollarInterpolation C' h (0, q) = (h.boundaryEquiv q.1, q.2) := by
  simp [presentationCollarInterpolation]

@[simp] theorem presentationCollarInterpolation_one (q : D.domain.boundary.Point × ℝ) :
    C.presentationCollarInterpolation C' h (1, q) =
      C.presentationCollarTransition C' h q := by
  simp [presentationCollarInterpolation]

@[simp] theorem presentationCollarInterpolation_boundary
    (t : ℝ) (x : D.domain.boundary.Point) :
    C.presentationCollarInterpolation C' h (t, (x, 0)) = (h.boundaryEquiv x, 0) := by
  simp [presentationCollarInterpolation]

theorem contMDiffAt_presentationCollarInterpolation
    (t : ℝ) (x : D.domain.boundary.Point) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.presentationCollarInterpolation C' h) (t, (x, 0)) := by
  have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × (D.domain.boundary.Point × ℝ) => (p.2.1, p.1 * p.2.2)) :=
    contMDiff_snd.fst.prodMk (contMDiff_fst.mul contMDiff_snd.snd)
  have hc : ContMDiffAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.presentationCollarTransition C' h) (x, t * 0) := by
    simpa using C.contMDiffAt_presentationCollarTransition C' h x
  have hf := hc.comp
    (t, (x, 0)) (hs (t, (x, 0)))
  exact hf.fst.prodMk
    (((contMDiffAt_const.sub contMDiffAt_fst).mul contMDiffAt_snd.snd).add hf.snd)

private theorem contMDiff_collarRescale :
    ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × (D.domain.boundary.Point × ℝ) => (p.2.1, p.1 * p.2.2)) :=
  contMDiff_snd.fst.prodMk (contMDiff_fst.mul contMDiff_snd.snd)

/-- An actual open joint domain containing every real-parameter boundary
slice, with smooth extension across the closed interval's endpoints. -/
def presentationCollarInterpolationDomain :
    TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ)) where
  carrier := (fun p => (p.2.1, p.1 * p.2.2)) ⁻¹' C.presentationCollarTransitionDomain C' h
  is_open' := (C.presentationCollarTransitionDomain C' h).isOpen.preimage
    (contMDiff_collarRescale (D := D)).continuous

theorem mem_presentationCollarInterpolationDomain_boundary
    (t : ℝ) (x : D.domain.boundary.Point) :
    (t, (x, 0)) ∈ C.presentationCollarInterpolationDomain C' h := by
  change (x, t * 0) ∈ C.presentationCollarTransitionDomain C' h
  simpa using C.mem_presentationCollarTransitionDomain_zero C' h x

theorem contMDiffOn_presentationCollarInterpolation :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.presentationCollarInterpolation C' h) (C.presentationCollarInterpolationDomain C' h) := by
  have hf := C.contMDiffOn_presentationCollarTransition C' h |>.comp
    (contMDiff_collarRescale (D := D)).contMDiffOn (fun _ hq => hq)
  intro p hp
  exact (hf p hp).fst.prodMk
    (((contMDiffWithinAt_const.sub (contMDiff_fst p).contMDiffWithinAt).mul
      (contMDiff_snd.snd p).contMDiffWithinAt).add (hf p hp).snd)

/-- Every slice preserves the compact side wherever the interpolation is
defined. The endpoint `t=0` is included directly. -/
theorem presentationCollarInterpolation_side
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (q : D.domain.boundary.Point × ℝ)
    (hq : (t, q) ∈ C.presentationCollarInterpolationDomain C' h) :
    (C.presentationCollarInterpolation C' h (t, q)).2 ≤ 0 ↔ q.2 ≤ 0 := by
  by_cases ht0 : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hs := C.presentationCollarTransition_side C' h (q.1, t * q.2) hq
  change (1 - t) * q.2 + (C.presentationCollarTransition C' h (q.1, t * q.2)).2 ≤ 0 ↔ _
  constructor
  · intro he
    by_contra hn
    have hr : 0 < q.2 := lt_of_not_ge hn
    have hf : 0 < (C.presentationCollarTransition C' h (q.1, t * q.2)).2 :=
      lt_of_not_ge (fun hf => (not_le_of_gt (mul_pos htpos hr)) (hs.mp hf))
    have hh : 0 ≤ (1 - t) * q.2 := mul_nonneg (sub_nonneg.mpr ht.2) (le_of_lt hr)
    linarith
  · intro hr
    have hf := hs.mpr (mul_nonpos_of_nonneg_of_nonpos ht.1 hr)
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hr) hf

/-- The joint domain on which the interpolation lifts to actual points in
the target compact extension. -/
def compactPresentationInterpolationDomain :
    TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ)) where
  carrier := C.presentationCollarInterpolationDomain C' h ∩
    (C.presentationCollarInterpolation C' h) ⁻¹' C'.presentationCollarSourceDomain
  is_open' := (C.contMDiffOn_presentationCollarInterpolation C' h).continuousOn
    |>.isOpen_inter_preimage (C.presentationCollarInterpolationDomain C' h).isOpen
      C'.presentationCollarSourceDomain.isOpen

theorem mem_compactPresentationInterpolationDomain_boundary
    (t : ℝ) (x : D.domain.boundary.Point) :
    (t, (x, 0)) ∈ C.compactPresentationInterpolationDomain C' h := by
  refine ⟨C.mem_presentationCollarInterpolationDomain_boundary C' h t x, ?_⟩
  change C.presentationCollarInterpolation C' h (t, (x, 0)) ∈ C'.presentationCollarSourceDomain
  rw [C.presentationCollarInterpolation_boundary]
  exact ⟨E.domain.boundaryInclusion.map (h.boundaryEquiv x),
    (C'.endMap_zero (h.boundaryEquiv x)).symm⟩

/-- Actual compact-extension maps obtained from the smooth collar
interpolation; their endpoint-one equation recovers the original compact
presentation on an open collar. -/
def compactPresentationInterpolation (p : ℝ × (D.domain.boundary.Point × ℝ)) :
    E.domain.extension.Point :=
  C'.presentationCollarPoint (C.presentationCollarInterpolation C' h p)

theorem contMDiffOn_compactPresentationInterpolation :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
      (C.compactPresentationInterpolation C' h) (C.compactPresentationInterpolationDomain C' h) :=
  C'.contMDiffOn_presentationCollarPoint.comp
    ((C.contMDiffOn_presentationCollarInterpolation C' h).mono inter_subset_left)
    (fun _ hq => hq.2)

/-- The actual compact-extension interpolation preserves the compact side
at every parameter in the prescribed closed interval. -/
theorem compactPresentationInterpolation_mem_carrier_iff
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (q : D.domain.boundary.Point × ℝ)
    (hq : (t, q) ∈ C.compactPresentationInterpolationDomain C' h) :
    C.compactPresentationInterpolation C' h (t, q) ∈ E.domain.carrier ↔ q.2 ≤ 0 := by
  rw [← C'.inclusion.embedding.injective.mem_set_image]
  change C'.inclusion.map
    (C'.presentationCollarPoint (C.presentationCollarInterpolation C' h (t, q))) ∈ _ ↔ _
  rw [C'.inclusionMap_presentationCollarPoint _ hq.2, C'.endMap_mem_compact_iff]
  exact C.presentationCollarInterpolation_side C' h t ht q hq.1

theorem compactPresentationInterpolation_one (q : D.domain.boundary.Point × ℝ)
    (hq : (1, q) ∈ C.compactPresentationInterpolationDomain C' h) :
    C.compactPresentationInterpolation C' h (1, q) =
      h.extensionEquiv (C.presentationCollarPoint q) := by
  apply C'.inclusion.embedding.injective
  rw [compactPresentationInterpolation, C'.inclusionMap_presentationCollarPoint _ hq.2,
    C.presentationCollarInterpolation_one]
  exact C.endMap_presentationCollarTransition C' h q (by
    have hu : (q.1, 1 * q.2) ∈ C.presentationCollarTransitionDomain C' h := hq.1
    simpa only [one_mul, Prod.eta] using hu)

@[simp] theorem compactPresentationInterpolation_zero (q : D.domain.boundary.Point × ℝ) :
    C.compactPresentationInterpolation C' h (0, q) =
      C'.presentationCollarPoint (h.boundaryEquiv q.1, q.2) := by
  rw [compactPresentationInterpolation, C.presentationCollarInterpolation_zero]

/-- Compactness gives one positive collar width for the entire closed
parameter interval, with the actual compact-extension maps jointly smooth
on a containing open neighborhood. -/
theorem exists_common_compactPresentationInterpolationWidth :
    ∃ δ : ℝ, 0 < δ ∧
      Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ Ioo (-δ) δ) ⊆
        (C.compactPresentationInterpolationDomain C' h :
          Set (ℝ × (D.domain.boundary.Point × ℝ))) := by
  have hb : Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ ({0} : Set ℝ)) ⊆
      (C.compactPresentationInterpolationDomain C' h :
        Set (ℝ × (D.domain.boundary.Point × ℝ))) := by
    rintro ⟨t, x, r⟩ ⟨_, _, hr⟩
    have hr' : r = 0 := hr
    subst r
    exact C.mem_compactPresentationInterpolationDomain_boundary C' h t x
  obtain ⟨U, V, _, hV, hIU, hBV, hUV⟩ := generalized_tube_lemma isCompact_Icc
    (D.domain.isCompact_boundary.prod isCompact_singleton)
    (C.compactPresentationInterpolationDomain C' h).isOpen hb
  obtain ⟨A, B, _, hB, hA, hzeroB, hAB⟩ := generalized_tube_lemma
    D.domain.isCompact_boundary isCompact_singleton hV hBV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds (hzeroB (mem_singleton 0)))
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨t, x, r⟩ ⟨ht, _, hr⟩
  apply hUV
  refine ⟨hIU ht, hAB ⟨hA (mem_univ x), hball ?_⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hr

set_option backward.isDefEq.respectTransparency false in
private theorem presentationCollarTransition_tangent
    (x : D.domain.boundary.Point) (v : Model (d - 1)) :
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (C.presentationCollarTransition C' h) (x, 0) (v, 0) =
      (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 1)) h.boundaryEquiv x v, 0) := by
  have he : (fun y : D.domain.boundary.Point =>
      C.presentationCollarTransition C' h (y, 0)) =
      (fun y => (h.boundaryEquiv y, (0 : ℝ))) := by
    funext y
    exact C.presentationCollarTransition_zero C' h y
  have hc := mfderiv_comp (f := fun y : D.domain.boundary.Point => (y, (0 : ℝ)))
    (g := C.presentationCollarTransition C' h) x
    ((C.contMDiffAt_presentationCollarTransition C' h x).mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  change mfderiv 𝓘(ℝ, Model (d - 1))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    (fun y => C.presentationCollarTransition C' h (y, 0)) x = _ at hc
  rw [he, mfderiv_prodMk (h.boundaryEquiv.contMDiff.mdifferentiableAt (by simp))
    mdifferentiableAt_const, mfderiv_const, mfderiv_prod_left] at hc
  exact (congrArg (fun L => L v) hc).symm

theorem presentationCollarTransition_normal_pos (x : D.domain.boundary.Point) :
    0 < (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (C.presentationCollarTransition C' h) (x, 0) (0, 1)).2 := by
  rw [(C.presentationCollarTransition_eventuallyEq C' h x).mfderiv_eq]
  exact C.compactCollarTransitionAt_normal_derivative_pos C' h x

set_option backward.isDefEq.respectTransparency false in
private theorem presentationCollarInterpolation_mfderiv
    (t : ℝ) (x : D.domain.boundary.Point) (v : Model (d - 1)) (s : ℝ) :
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (fun q => C.presentationCollarInterpolation C' h (t, q)) (x, 0) (v, s) =
      ((mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
          (C.presentationCollarTransition C' h) (x, 0) (v, t * s)).1,
        (1 - t) * s + (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
          (C.presentationCollarTransition C' h) (x, 0) (v, t * s)).2) := by
  let f := C.presentationCollarTransition C' h
  let L := mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) f (x, 0)
  let R : D.domain.boundary.Point × ℝ → D.domain.boundary.Point × ℝ :=
    fun q => (q.1, t • q.2)
  have hR := (hasMFDerivAt_fst (I := 𝓘(ℝ, Model (d - 1)))
    (I' := 𝓘(ℝ, ℝ)) (x, (0 : ℝ))).prodMk
    ((hasMFDerivAt_snd (I := 𝓘(ℝ, Model (d - 1)))
      (I' := 𝓘(ℝ, ℝ)) (x, (0 : ℝ))).const_smul t)
  have hf : HasMFDerivAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) f (R (x, 0)) L := by
    have hz : R (x, 0) = (x, 0) := by
      change (x, t • (0 : ℝ)) = (x, 0)
      rw [smul_zero]
    rw [hz]
    exact (C.contMDiffAt_presentationCollarTransition C' h x).mdifferentiableAt (by simp)
      |>.hasMFDerivAt
  have hg := hf.comp (x, 0) hR
  have hfst := (hasMFDerivAt_fst (I := 𝓘(ℝ, Model (d - 1)))
    (I' := 𝓘(ℝ, ℝ)) (f (R (x, 0)))).comp (x, 0) hg
  have hsnd := (hasMFDerivAt_snd (I := 𝓘(ℝ, Model (d - 1)))
    (I' := 𝓘(ℝ, ℝ)) (f (R (x, 0)))).comp (x, 0) hg
  have hrad := (hasMFDerivAt_snd (I := 𝓘(ℝ, Model (d - 1)))
    (I' := 𝓘(ℝ, ℝ)) (x, (0 : ℝ))).const_smul (1 - t)
  have hm := hfst.prodMk (hrad.add hsnd)
  have he := congrArg (fun A => A (v, s)) hm.mfderiv
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- The differential of every interpolation slice is an isomorphism at
every boundary point. Its normal coefficient is the positive convex
combination `(1-t)+t*a`, while its tangential block is the original boundary
diffeomorphism's differential. -/
theorem presentationCollarInterpolation_mfderiv_bijective
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : D.domain.boundary.Point) :
    Function.Bijective (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (fun q => C.presentationCollarInterpolation C' h (t, q)) (x, 0)) := by
  let L := mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    (C.presentationCollarTransition C' h) (x, 0)
  have ha : 0 < (L (0, 1)).2 := C.presentationCollarTransition_normal_pos C' h x
  have hβ : 0 < (1 - t) + t * (L (0, 1)).2 := by
    by_cases ht0 : t = 0
    · subst t
      norm_num
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hpos := mul_pos htp ha
      linarith [ht.2]
  have hinj : Function.Injective (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (fun q => C.presentationCollarInterpolation C' h (t, q)) (x, 0)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨v, s⟩ he
    change mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (fun q => C.presentationCollarInterpolation C' h (t, q)) (x, 0) (v, s) = (0, 0) at he
    have hs := congrArg Prod.snd he
    rw [C.presentationCollarInterpolation_mfderiv C' h t x v s] at hs
    have hsplit : (v, t * s) = (v, 0) + (t * s) • (0, 1) := by ext <;> simp
    change (1 - t) * s + (L (v, t * s)).2 = 0 at hs
    rw [hsplit, map_add, map_smul] at hs
    have htan := C.presentationCollarTransition_tangent C' h x v
    change L (v, 0) = _ at htan
    rw [htan] at hs
    change (1 - t) * s + (0 + (t * s) * (L (0, 1)).2) = 0 at hs
    have hs0 : s = 0 := (mul_eq_zero.mp (show
      ((1 - t) + t * (L (0, 1)).2) * s = 0 by nlinarith [hs])).resolve_left (ne_of_gt hβ)
    subst s
    rw [C.presentationCollarInterpolation_mfderiv C' h t x v 0] at he
    simp only [mul_zero, zero_add] at he
    change ((L (v, 0)).1, (L (v, 0)).2) = (0, 0) at he
    rw [htan] at he
    have hv := congrArg Prod.fst he
    have hv0 := (h.boundaryEquiv.mfderivToContinuousLinearEquiv (by simp) x).injective
      (hv.trans (map_zero _).symm)
    exact Prod.ext hv0 rfl
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Every interpolation slice is an actual smooth local diffeomorphism at
the entire seam. This consumes the constructed open joint smooth domain
and the proved slice differential isomorphism. -/
theorem isLocalDiffeomorphAt_presentationCollarInterpolation
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : D.domain.boundary.Point) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (fun q => C.presentationCollarInterpolation C' h (t, q)) (x, 0) := by
  let U : Set (D.domain.boundary.Point × ℝ) :=
    (fun q => (t, q)) ⁻¹' C.presentationCollarInterpolationDomain C' h
  have hU : IsOpen U := (C.presentationCollarInterpolationDomain C' h).isOpen.preimage
    (continuous_const.prodMk continuous_id)
  have hf : ContMDiffOn ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (fun q => C.presentationCollarInterpolation C' h (t, q)) U :=
    (C.contMDiffOn_presentationCollarInterpolation C' h).comp
      (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hq => hq)
  have hd := C.presentationCollarInterpolation_mfderiv_bijective C' h t ht x
  have hp : IsManifold ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (D.domain.boundary.Point × ℝ) := inferInstance
  have hp' : IsManifold ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (E.domain.boundary.Point × ℝ) := inferInstance
  let : ChartedSpace (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ) :=
    prodChartedSpace (Model (d - 1)) D.domain.boundary.Point ℝ ℝ
  let : ChartedSpace (Model (d - 1) × ℝ) (E.domain.boundary.Point × ℝ) :=
    prodChartedSpace (Model (d - 1)) E.domain.boundary.Point ℝ ℝ
  rw [← modelWithCornersSelf_prod] at hf hd hp hp' ⊢
  exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold hU hf
    (C.mem_presentationCollarInterpolationDomain_boundary C' h t x) hd

/-- Retaining the parameter gives a map whose inverse-function-theorem
inverse is jointly smooth in both the parameter and collar coordinates. -/
def presentationCollarInterpolationWithParameter
    (p : ℝ × (D.domain.boundary.Point × ℝ)) : ℝ × (E.domain.boundary.Point × ℝ) :=
  (p.1, C.presentationCollarInterpolation C' h p)

theorem contMDiffOn_presentationCollarInterpolationWithParameter :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      (C.presentationCollarInterpolationWithParameter C' h)
      (C.presentationCollarInterpolationDomain C' h) := by
  intro p hp
  exact (contMDiff_fst p).contMDiffWithinAt.prodMk
    (C.contMDiffOn_presentationCollarInterpolation C' h p hp)

set_option backward.isDefEq.respectTransparency false in
/-- This is the parameter-dependent local inverse statement, rather than
only independent inverses of the individual slices. Uniform collar
injectivity is established below; the compact-interior cutoff extension
remains separate. -/
theorem isLocalDiffeomorphAt_presentationCollarInterpolationWithParameter
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : D.domain.boundary.Point) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      (C.presentationCollarInterpolationWithParameter C' h) (t, (x, 0)) := by
  have hf := C.contMDiffOn_presentationCollarInterpolationWithParameter C' h
  have hc := C.contMDiffAt_presentationCollarInterpolation C' h t x
  have hdH := hc.mdifferentiableAt (by simp)
  have hinj : Function.Injective (mfderiv ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      (C.presentationCollarInterpolationWithParameter C' h) (t, (x, 0))) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨u, v, s⟩ he
    change mfderiv ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      (fun p => (p.1, C.presentationCollarInterpolation C' h p))
        (t, (x, 0)) (u, (v, s)) = (0, (0, 0)) at he
    rw [mfderiv_prodMk mdifferentiableAt_fst hdH, mfderiv_fst] at he
    have hu : u = 0 := congrArg Prod.fst he
    subst u
    have hv := congrArg Prod.snd he
    have hm := mfderiv_comp (f := fun q : D.domain.boundary.Point × ℝ => (t, q))
      (g := C.presentationCollarInterpolation C' h) (x, 0) hdH
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    rw [mfderiv_prod_right] at hm
    have hm' := congrArg (fun A => A (v, s)) hm
    have hs : mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        (fun q => C.presentationCollarInterpolation C' h (t, q)) (x, 0) (v, s) = 0 :=
      hm'.trans hv
    have hvs := (C.presentationCollarInterpolation_mfderiv_bijective C' h t ht x).1
      (hs.trans (map_zero _).symm)
    exact Prod.ext rfl hvs
  have hd : Function.Bijective (mfderiv ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      (C.presentationCollarInterpolationWithParameter C' h) (t, (x, 0))) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hp : IsManifold ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      (ℝ × (D.domain.boundary.Point × ℝ)) := inferInstance
  have hp' : IsManifold ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      (ℝ × (E.domain.boundary.Point × ℝ)) := inferInstance
  let : ChartedSpace (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ) :=
    prodChartedSpace (Model (d - 1)) D.domain.boundary.Point ℝ ℝ
  let : ChartedSpace (Model (d - 1) × ℝ) (E.domain.boundary.Point × ℝ) :=
    prodChartedSpace (Model (d - 1)) E.domain.boundary.Point ℝ ℝ
  let : ChartedSpace (ℝ × (Model (d - 1) × ℝ)) (ℝ × (D.domain.boundary.Point × ℝ)) :=
    prodChartedSpace ℝ ℝ (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ)
  let : ChartedSpace (ℝ × (Model (d - 1) × ℝ)) (ℝ × (E.domain.boundary.Point × ℝ)) :=
    prodChartedSpace ℝ ℝ (Model (d - 1) × ℝ) (E.domain.boundary.Point × ℝ)
  simp only [← modelWithCornersSelf_prod] at hf hd hp hp' ⊢
  exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    (C.presentationCollarInterpolationDomain C' h).isOpen hf
    (C.mem_presentationCollarInterpolationDomain_boundary C' h t x) hd

/-- The actual local-diffeomorphism locus is open: a certificate at one
point serves every point in its open source. -/
def presentationCollarLocalDiffeomorphDomain :
    TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ)) where
  carrier := {p | IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
    ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
    (C.presentationCollarInterpolationWithParameter C' h) p}
  is_open' := by
    apply isOpen_iff_mem_nhds.mpr
    rintro p ⟨e, hp, he⟩
    apply mem_of_superset (e.open_source.mem_nhds hp)
    intro q hq
    exact ⟨e, hq, he⟩

/-- A single open neighborhood of the full compact parameter-boundary seam
has both injectivity and smooth local inverses at every point. The positive
width covers all slices and retains the actual compact-extension domain. -/
theorem exists_common_injective_collarInterpolation :
    ∃ (U : TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ))) (δ : ℝ),
      0 < δ ∧ Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ Ioo (-δ) δ) ⊆
        (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) ∧
      (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) ⊆
        C.compactPresentationInterpolationDomain C' h ∧
      InjOn (C.presentationCollarInterpolationWithParameter C' h) U ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
        (C.presentationCollarInterpolationWithParameter C' h) U := by
  let K : Set (ℝ × (D.domain.boundary.Point × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ ({0} : Set ℝ))
  have hK : IsCompact K := isCompact_Icc.prod
    (D.domain.isCompact_boundary.prod isCompact_singleton)
  have hinj : InjOn (C.presentationCollarInterpolationWithParameter C' h) K := by
    rintro ⟨t, x, r⟩ ⟨_, _, hr⟩ ⟨s, y, u⟩ ⟨_, _, hu⟩ he
    have hr0 : r = 0 := hr
    have hu0 : u = 0 := hu
    subst r
    subst u
    change (t, C.presentationCollarInterpolation C' h (t, (x, 0))) =
      (s, C.presentationCollarInterpolation C' h (s, (y, 0))) at he
    rw [C.presentationCollarInterpolation_boundary,
      C.presentationCollarInterpolation_boundary] at he
    have htEq : t = s := congrArg Prod.fst he
    have hxEq : x = y := h.boundaryEquiv.injective (congrArg (fun p => p.2.1) he)
    exact Prod.ext htEq (Prod.ext hxEq rfl)
  have hloc (p : ℝ × (D.domain.boundary.Point × ℝ)) (hp : p ∈ K) :
      IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
        (C.presentationCollarInterpolationWithParameter C' h) p := by
    obtain ⟨t, x, r⟩ := p
    have hr : r = 0 := hp.2.2
    subst r
    exact C.isLocalDiffeomorphAt_presentationCollarInterpolationWithParameter C' h t hp.1 x
  obtain ⟨V, hVo, hKV, hVi⟩ := hinj.exists_isOpen_superset hK
    (fun p hp => (hloc p hp).contMDiffAt.continuousAt) (by
      intro p hp
      obtain ⟨e, he, heq⟩ := hloc p hp
      refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
      intro a ha b hb hab
      apply e.toPartialEquiv.injOn ha hb
      rw [← heq ha, ← heq hb]
      exact hab)
  let U : TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ)) :=
    ⟨V ∩ (C.compactPresentationInterpolationDomain C' h ∩
      C.presentationCollarLocalDiffeomorphDomain C' h),
      hVo.inter ((C.compactPresentationInterpolationDomain C' h).isOpen.inter
        (C.presentationCollarLocalDiffeomorphDomain C' h).isOpen)⟩
  have hKU : K ⊆ U := by
    rintro ⟨t, x, r⟩ hp
    have hr : r = 0 := hp.2.2
    subst r
    exact ⟨hKV hp, C.mem_compactPresentationInterpolationDomain_boundary C' h t x,
      hloc (t, (x, 0)) hp⟩
  obtain ⟨A, B, _, hB, hKA, hKB, hAB⟩ := generalized_tube_lemma isCompact_Icc
    (D.domain.isCompact_boundary.prod isCompact_singleton) U.isOpen hKU
  obtain ⟨P, Q, _, hQ, hBP, hzeroQ, hPQ⟩ := generalized_tube_lemma
    D.domain.isCompact_boundary isCompact_singleton hB hKB
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds (hzeroQ (mem_singleton 0)))
  refine ⟨U, δ, hδ, ?_, (fun _ hp => hp.2.1), hVi.mono inter_subset_left,
    (fun p => p.property.2.2)⟩
  rintro ⟨t, x, r⟩ ⟨ht, _, hr⟩
  apply hAB
  refine ⟨hKA ht, hPQ ⟨hBP (mem_univ x), hball ?_⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hr

/-- The injective local-diffeomorphism neighborhood is an actual open
embedding, with one common positive collar width for the full parameter
interval. This is the geometric collar interpolation producer; its smooth
compact-extension endpoint equations were proved above. -/
theorem exists_common_embedded_collarInterpolation :
    ∃ (U : TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ))) (δ : ℝ),
      0 < δ ∧ Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ Ioo (-δ) δ) ⊆
        (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) ∧
      (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) ⊆
        C.compactPresentationInterpolationDomain C' h ∧
      Topology.IsOpenEmbedding (fun p : U =>
        C.presentationCollarInterpolationWithParameter C' h p.val) ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
        (C.presentationCollarInterpolationWithParameter C' h) U := by
  obtain ⟨U, δ, hδ, hw, hU, hinj, hdiff⟩ :=
    C.exists_common_injective_collarInterpolation C' h
  refine ⟨U, δ, hδ, hw, hU, ?_, hdiff⟩
  have hloc : IsLocalHomeomorph (fun p : U =>
      C.presentationCollarInterpolationWithParameter C' h p.val) := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact hdiff.isLocalHomeomorphOn.comp
      U.isOpenEmbedding'.isLocalHomeomorph.isLocalHomeomorphOn (by
        intro p _
        exact p.property)
  exact hloc.isOpenEmbedding_of_injective (Set.injOn_iff_injective.mp hinj)

/-- The produced common collar embedding makes the actual compact-extension
maps injective on one positive-width collar for every parameter, rather than
only constructing an injective family of abstract collar coordinates. -/
theorem exists_common_injective_compactPresentationInterpolation :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      InjOn (fun q => C.compactPresentationInterpolation C' h (t, q))
        (univ ×ˢ Ioo (-δ) δ) := by
  obtain ⟨U, δ, hδ, hw, hU, hemb, _⟩ :=
    C.exists_common_embedded_collarInterpolation C' h
  refine ⟨δ, hδ, ?_⟩
  intro t ht q hq q' hq' he
  have hp : (t, q) ∈ U := hw ⟨ht, hq⟩
  have hp' : (t, q') ∈ U := hw ⟨ht, hq'⟩
  have hc := congrArg C'.inclusion.map he
  change C'.inclusion.map
      (C'.presentationCollarPoint (C.presentationCollarInterpolation C' h (t, q))) =
    C'.inclusion.map
      (C'.presentationCollarPoint (C.presentationCollarInterpolation C' h (t, q'))) at hc
  rw [C'.inclusionMap_presentationCollarPoint _ (hU hp).2,
    C'.inclusionMap_presentationCollarPoint _ (hU hp').2] at hc
  have hc' := C'.endMap_injective hc
  have he' : (⟨(t, q), hp⟩ : U) = ⟨(t, q'), hp'⟩ :=
    hemb.injective (Prod.ext rfl hc')
  exact congrArg (fun p : U => p.val.2) he'

end Completion
end FsFltz.Geometry
