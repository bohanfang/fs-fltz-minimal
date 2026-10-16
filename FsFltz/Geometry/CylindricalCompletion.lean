import FsFltz.Geometry.CylindricalCompleteFlow
import FsFltz.Geometry.LiouvilleFlowPrimitive
import FsFltz.Geometry.LiouvilleLocalCollar
import FsFltz.Geometry.CylindricalLiouville
import FsFltz.Geometry.CylindricalEnd
import FsFltz.Geometry.CylindricalEndFlow

/-!
# Assembly of a cylindrical Liouville completion

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, especially the
completion and all-real flow in lines 142–158; `sec:lean`, lines 766–836,
especially the required collar and complete-flow bridges in lines 805–814.
The explicit stretched primitive and cylindrical end produce a complete
flow by compact-interior continuation. Its boundary orbit map has the
required immersion and exponential primitive for every real time,
including negative time. Uniqueness identifies the nonnegative end with
the constructed radial chart, proving the exterior and covering equations.

The output is a `Completion` of the localized presentation, whose extension
contains only the compact interior and the constructed collar. The compact
carrier, original primitive and boundary form are preserved by the native
open-subset inclusions. No completion or complete flow is an input, and no
part of the geometric comparison target is asserted.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function

namespace FsFltz.Geometry
open SmoothManifold

namespace CompleteLiouvilleFlow

variable {d : ℕ} (D : CompactDomain d)
  {Z : (x : D.extension.Point) → D.extension.Tangent x}
  (F : CompleteLiouvilleFlow D.extension Z)

/-- The boundary parametrization for all real times of the actual complete flow. -/
def boundaryOrbitMap (p : D.boundary.Point × ℝ) : D.extension.Point :=
  F.flow p.2 (D.boundaryInclusion.map p.1)

theorem smooth_boundaryOrbitMap : ContMDiff
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
    (F.boundaryOrbitMap D) :=
  F.smooth_action.comp (contMDiff_snd.prodMk
    (D.boundaryInclusion.map.contMDiff.comp contMDiff_fst))

@[simp] theorem boundaryOrbitMap_zero (x : D.boundary.Point) :
    F.boundaryOrbitMap D (x, 0) = D.boundaryInclusion.map x :=
  F.flow.map_zero_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Cartan's formula, in its proved pullback form, gives the complete
exponential end primitive on the whole boundary orbit map. -/
theorem boundaryOrbitMap_primitive (α : D.extension.Form 1)
    (hα : D.extension.IsSmoothForm α)
    (hZ : ∀ z, D.extension.LiouvilleEquation α z (Z z))
    (x : D.boundary.Point) (r : ℝ) (v : Model (d - 1)) (s : ℝ) :
    evalOne α (F.boundaryOrbitMap D (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        (F.boundaryOrbitMap D) (x, r) (v, s)) =
      Real.exp r * evalOne (D.boundaryForm α) x v := by
  let B := D.boundary
  let M := D.extension
  let j := D.boundaryInclusion.map
  let c := F.boundaryOrbitMap D
  have hc := F.smooth_boundaryOrbitMap D
  have hct : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1)))
      𝓘(ℝ, Model d) ∞ (fun p : ℝ × B.Point => F.flow p.1 (j p.2)) :=
    F.smooth_action.comp (contMDiff_fst.prodMk (j.contMDiff.comp contMDiff_snd))
  have hp := LiouvilleFlowPrimitive.pullback_slice_eq_exp_smul M B α hα Z hZ
    (fun p : ℝ × B.Point => F.flow p.1 (j p.2)) hct isOpen_univ isPreconnected_univ
    isOpen_univ (fun y _ t _ => F.isMIntegralCurve (j y) t)
    (mem_univ r) (mem_univ 0) (mem_univ x)
  have hinit : (fun y : B.Point => F.flow 0 (j y)) = j :=
    funext (fun y => F.flow.map_zero_apply _)
  rw [hinit, sub_zero] at hp
  have hval := congrArg (fun a => a (fun _ : Fin 1 => v)) hp
  have hi : HasMFDerivAt 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (fun y : B.Point => (y, r)) x
      ((ContinuousLinearMap.id ℝ (Model (d - 1))).prod 0) :=
    (hasMFDerivAt_id x).prodMk (hasMFDerivAt_const r x)
  have hspace := mfderiv_comp_apply (f := fun y : B.Point => (y, r)) (g := c) x
    (hc.mdifferentiableAt (by simp)) hi.mdifferentiableAt v
  rw [hi.mfderiv] at hspace
  change mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) (fun y => F.flow r (j y)) x v =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (v, 0)
      at hspace
  have ht : HasMFDerivAt 𝓘(ℝ, ℝ)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (fun t : ℝ => (x, t)) r
      ((0 : ℝ →L[ℝ] Model (d - 1)).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const x r).prodMk (hasMFDerivAt_id r)
  have htime := mfderiv_comp_apply (f := fun t : ℝ => (x, t)) (g := c) r
    (hc.mdifferentiableAt (by simp)) ht.mdifferentiableAt (1 : ℝ)
  rw [ht.mfderiv] at htime
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun t => F.flow t (j x)) r (1 : ℝ) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (0, 1)
      at htime
  rw [(F.isMIntegralCurve (j x) r).mfderiv] at htime
  change (1 : ℝ) • Z (F.flow r (j x)) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (0, 1)
      at htime
  rw [one_smul] at htime
  have hsplit : (v, s) = (v, (0 : ℝ)) + s • (0, (1 : ℝ)) := by simp
  change evalOne α (F.flow r (j x))
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (v, s)) = _
  rw [hsplit, map_add, map_smul, ← hspace, ← htime, evalOne_add, evalOne_smul,
    M.evalOne_eq_zero_of_liouvilleEquation _ _ _ (hZ _), mul_zero, add_zero]
  exact hval

set_option backward.isDefEq.respectTransparency false in
/-- A smooth all-real action has an injective differential at every fixed
time, since the negative-time action is its smooth inverse. -/
theorem mfderiv_timeMap_injective (t : ℝ) (x : D.extension.Point) :
    Function.Injective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow t) x) := by
  have ht : MDifferentiable 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow t) :=
    (F.smooth_action.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp)
  have hn : MDifferentiable 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow (-t)) :=
    (F.smooth_action.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp)
  have heq : F.flow (-t) ∘ F.flow t = id := by
    funext z
    simp only [comp_apply, ← F.flow.map_add, neg_add_cancel, F.flow.map_zero_apply, id_eq]
  have hd := mfderiv_comp x (hn (F.flow t x)) (ht x)
  rw [heq, mfderiv_id] at hd
  intro u v huv
  have hu := congrArg (fun A => A u) hd
  have hv := congrArg (fun A => A v) hd
  change u = mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow (-t)) (F.flow t x)
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow t) x u) at hu
  change v = mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow (-t)) (F.flow t x)
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow t) x v) at hv
  rw [huv] at hu
  exact hu.trans hv.symm

set_option backward.isDefEq.respectTransparency false in
/-- Outward boundary transversality and the smooth action prove immersion
of the complete boundary orbit map at every real radius. -/
theorem boundaryOrbitMap_immersion (L : LiouvilleStructure D)
    (hboundary : ∀ x : D.boundary.Point,
      Z (D.boundaryInclusion.map x) = L.field (D.boundaryInclusion.map x))
    (p : D.boundary.Point × ℝ) : Function.Injective
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        (F.boundaryOrbitMap D) p) := by
  let c := F.boundaryOrbitMap D
  have hc := F.smooth_boundaryOrbitMap D
  have hzero : Function.Injective
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (p.1, 0)) := by
    apply (L.boundaryFlow_mfderiv_zero_bijective c p.1
      (hc.mdifferentiableAt (by simp)) (F.boundaryOrbitMap_zero D) ?_).injective
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun t => F.flow t (D.boundaryInclusion.map p.1)) 0 (1 : ℝ) = _
    rw [(F.isMIntegralCurve (D.boundaryInclusion.map p.1) 0).mfderiv]
    change (1 : ℝ) • Z (F.flow 0 (D.boundaryInclusion.map p.1)) = _
    rw [one_smul, F.flow.map_zero_apply, hboundary]
  let q : D.boundary.Point × ℝ → D.boundary.Point × ℝ :=
    fun y => (y.1, y.2 - p.2)
  have hq : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ q :=
    contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
  have hqp : q p = (p.1, 0) := by simp [q]
  have hdq : mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) q p =
      ContinuousLinearMap.id ℝ (Model (d - 1) × ℝ) := by
    dsimp [q]
    erw [mfderiv_prodMk mdifferentiableAt_fst
      (mdifferentiableAt_snd.sub mdifferentiableAt_const),
      mfderiv_sub mdifferentiableAt_snd mdifferentiableAt_const,
      mfderiv_fst, mfderiv_snd, mfderiv_const, sub_zero]
    rfl
  have heq : F.flow p.2 ∘ c ∘ q = c := by
    funext y
    simp only [c, boundaryOrbitMap, q, comp_apply, ← F.flow.map_add]
    congr 1
    ring
  have ht : MDifferentiable 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow p.2) :=
    (F.smooth_action.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp)
  have hd := mfderiv_comp p (ht (c (q p)))
    ((hc.comp hq).mdifferentiableAt (by simp))
  erw [mfderiv_comp p (hc.mdifferentiableAt (by simp))
    (hq.mdifferentiableAt (by simp)), hdq, ContinuousLinearMap.comp_id, heq, hqp] at hd
  rw [hd]
  change Function.Injective (fun w =>
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (F.flow p.2) (c (q p))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (p.1, 0) w))
  rw [hqp]
  exact (F.mfderiv_timeMap_injective D p.2 (c (p.1, 0))).comp hzero

set_option backward.isDefEq.respectTransparency false in
/-- Native uniqueness identifies the boundary orbit with a cylindrical
curve on its two-sided open source, including the positive infinite end. -/
theorem boundaryOrbitMap_eq_of_isMIntegralCurveOn (hZ : D.extension.IsSmoothVectorField Z)
    {δ : ℝ} (hδ : 0 < δ) (e : D.boundary.Point × ℝ → D.extension.Point)
    (hradial : ∀ x, IsMIntegralCurveOn (fun r => e (x, r)) Z (Ioi (-δ)))
    (hzero : ∀ x, e (x, 0) = D.boundaryInclusion.map x)
    (p : D.boundary.Point × ℝ) (hp : -δ < p.2) :
    F.boundaryOrbitMap D p = e p := by
  let b : ℝ := max p.2 0 + 1
  have hb₀ : 0 < b := by dsimp [b]; linarith [le_max_right p.2 0]
  have hbr : p.2 < b := by dsimp [b]; linarith [le_max_left p.2 0]
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) (a := -δ) (b := b) ⟨neg_lt_zero.mpr hδ, hb₀⟩
    (hZ.contMDiff_section.of_le (by simp))
    ((F.isMIntegralCurve (D.boundaryInclusion.map p.1)).isMIntegralCurveOn _)
    ((hradial p.1).mono (fun _ ht => ht.1))
    (by rw [F.flow.map_zero_apply, hzero])
  exact heq ⟨hp, hbr⟩

end CompleteLiouvilleFlow

namespace LiouvilleDomain.FlowCollar

variable {d : ℕ} {D : LiouvilleDomain d} (C : FlowCollar D)

set_option backward.isDefEq.respectTransparency false in
/-- Stretching retains the old compact-domain boundary primitive exactly.
The comparison is evaluated at the actual boundary inclusion, which lies
in the original compact carrier. -/
theorem stretched_boundaryForm :
    C.localizedDomain.domain.boundaryForm C.stretchedPrimitive =
      C.localizedDomain.domain.boundaryForm C.localizedDomain.liouville.primitive := by
  funext x
  have hx := C.localizedDomain.domain.compact.isClosed.frontier_subset
    (C.localizedDomain.domain.boundaryInclusion_mem_frontier x)
  unfold CompactDomain.boundaryForm SmoothManifold.pullback
  rw [C.stretchedPrimitive_carrier _ hx]

/-- The boundary coefficient in the new cylindrical end is literally the
original supplied domain's boundary restriction. -/
theorem stretched_original_boundaryForm :
    C.localizedDomain.domain.boundaryForm C.stretchedPrimitive =
      D.domain.boundaryForm D.liouville.primitive :=
  C.stretched_boundaryForm.trans C.localized_boundaryForm

/-- Compact-interior continuation and the constructed radial curves
produce the complete flow of the actual stretched Liouville field. -/
def cylindricalCompleteFlow : CompleteLiouvilleFlow C.localizedDomain.domain.extension
    C.stretchedField :=
  Classical.choice (C.localizedDomain.domain.extension.exists_completeLiouvilleFlow_of_cylindricalEnd
    C.stretchedField C.smooth_stretchedField C.isCompact_enlargedCompact
    (fun x r => C.endMap (x, r))
    (fun x => (C.endMap_isMIntegralCurveOn x).mono
      (fun _ hr => lt_trans (neg_lt_zero.mpr C.positive_width) hr))
    C.endMap_covers_outside_enlargedCompact)

/-- The actual complete ambient on the localized open manifold. Its
primitive and field are the constructed stretched data. -/
def cylindricalAmbient : CompleteLiouvilleManifold d where
  manifold := C.localizedDomain.domain.extension
  primitive := C.stretchedPrimitive
  smooth_primitive := C.smooth_stretchedPrimitive
  symplectic := C.stretched_symplectic
  field := C.stretchedField
  smooth_field := C.smooth_stretchedField
  contraction := C.stretchedField_contraction
  completeFlow := C.cylindricalCompleteFlow

/-- Extend the end through every negative time using the very complete
flow constructed by compact-interior continuation. -/
def cylindricalFlowEndMap : D.neighborhoodDomain.boundary.Point × ℝ →
    C.localizedDomain.domain.extension.Point :=
  C.cylindricalCompleteFlow.boundaryOrbitMap C.localizedDomain.domain

/-- Uniqueness identifies the all-real orbit parametrization with the
actual stretched collar wherever the latter is defined. -/
theorem cylindricalFlowEndMap_eq_endMap (p : D.neighborhoodDomain.boundary.Point × ℝ)
    (hp : -C.width < p.2) : C.cylindricalFlowEndMap p = C.endMap p :=
  C.cylindricalCompleteFlow.boundaryOrbitMap_eq_of_isMIntegralCurveOn
    C.localizedDomain.domain C.smooth_stretchedField C.positive_width C.endMap
    C.endMap_isMIntegralCurveOn C.endMap_zero p hp

set_option backward.isDefEq.respectTransparency false in
/-- An actual completion of the localized presentation, with identity
inclusion, all-real end immersion and primitive, and the constructed
positive cylindrical exterior. No completion is supplied as a hypothesis. -/
def cylindricalCompletion : Completion C.localizedDomain where
  ambient := C.cylindricalAmbient
  inclusion :=
    { map := ContMDiffMap.id
      embedding := Topology.IsEmbedding.id
      immersion := fun x => by
        change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) id x)
        rw [mfderiv_id]
        exact Function.injective_id }
  primitive_on_domain := by
    intro x hx
    exact (congrFun (C.localizedDomain.domain.extension.pullback_id C.stretchedPrimitive) x).trans
      (C.stretchedPrimitive_carrier x hx)
  field_on_domain := by
    intro x hx
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) id x
      (C.localizedDomain.liouville.field x) = C.stretchedField x
    rw [mfderiv_id]
    exact (C.stretchedField_carrier x hx).symm
  endMap := C.cylindricalFlowEndMap
  smooth_endMap := C.cylindricalCompleteFlow.smooth_boundaryOrbitMap C.localizedDomain.domain
  end_flow := fun _ _ => rfl
  end_embedding := by
    let i : D.neighborhoodDomain.boundary.Point × Ici (0 : ℝ) →
        {p : D.neighborhoodDomain.boundary.Point × ℝ // 0 ≤ p.2} :=
      fun p => ⟨(p.1, p.2.val), p.2.property⟩
    have hi : Topology.IsEmbedding i :=
      (Topology.IsEmbedding.subtypeVal.of_comp_iff).mp
        (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal)
    have heq : (fun p : D.neighborhoodDomain.boundary.Point × Ici (0 : ℝ) =>
        C.cylindricalFlowEndMap (p.1, p.2.val)) = C.nonnegativeEndMap ∘ i := by
      funext p
      exact C.cylindricalFlowEndMap_eq_endMap _
        (lt_of_lt_of_le (neg_lt_zero.mpr C.positive_width) p.2.property)
    erw [heq]
    exact C.isEmbedding_nonnegativeEndMap.comp hi
  end_immersion := C.cylindricalCompleteFlow.boundaryOrbitMap_immersion C.localizedDomain.domain
    C.localizedDomain.liouville (fun x => C.stretchedField_carrier _
      (C.localizedDomain.domain.compact.isClosed.frontier_subset
        (C.localizedDomain.domain.boundaryInclusion_mem_frontier x)))
  end_primitive := by
    intro x r v s
    have h := C.cylindricalCompleteFlow.boundaryOrbitMap_primitive C.localizedDomain.domain
      C.stretchedPrimitive C.smooth_stretchedPrimitive C.stretchedField_contraction x r v s
    rw [C.stretched_boundaryForm] at h
    exact h
  covering := by
    change id '' C.localizedDomain.domain.carrier ∪
      C.cylindricalFlowEndMap '' (univ ×ˢ Ici (0 : ℝ)) = univ
    rw [image_id, image_congr (fun p hp => C.cylindricalFlowEndMap_eq_endMap p
      (lt_of_lt_of_le (neg_lt_zero.mpr C.positive_width) hp.2))]
    exact C.endMap_covering
  overlap := by
    intro x r hr
    change C.cylindricalFlowEndMap (x, r) ∉ id '' C.localizedDomain.domain.carrier
    rw [image_id, C.cylindricalFlowEndMap_eq_endMap _
      (lt_trans (neg_lt_zero.mpr C.positive_width) hr),
      C.endMap_mem_carrier_iff _ (lt_trans (neg_lt_zero.mpr C.positive_width) hr)]
    exact not_le_of_gt hr

/-- The collar and complete-flow foundations construct an actual completion
for every dimension of the localized domain, including dimension zero. -/
theorem nonempty_cylindricalCompletion : Nonempty (Completion C.localizedDomain) :=
  ⟨C.cylindricalCompletion⟩

@[simp] theorem cylindricalCompletion_inclusion (z : C.localizedDomain.domain.extension.Point) :
    C.cylindricalCompletion.inclusion.map z = z := rfl

/-- The actual compact carrier is the original domain under both native
open-subset inclusions, with its unchanged compact topology. -/
def cylindricalCompactHomeomorph : C.localizedDomain.domain.Point ≃ₜ D.domain.Point :=
  C.compactHomeomorph.trans
    (D.domain.restrictPointHomeomorph D.symplecticNeighborhood
      D.carrier_subset_symplecticNeighborhood)

@[simp] theorem cylindricalCompactHomeomorph_val (z : C.localizedDomain.domain.Point) :
    (C.cylindricalCompactHomeomorph z).val = z.val.val.val := rfl

/-- The completed primitive at every compact point is precisely the
original supplied primitive under the two actual open-subset inclusions. -/
theorem cylindricalCompletion_original_primitive (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    C.cylindricalCompletion.ambient.primitive z = D.liouville.primitive z.val.val :=
  (C.stretchedPrimitive_carrier z hz).trans
    ((D.neighborhoodStructure.restrict_primitive C.neighborhood
      C.carrier_subset_neighborhood z).trans (D.neighborhood_primitive z.val))

/-- The completed field is the actual original field at compact points. -/
theorem cylindricalCompletion_original_field (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    C.cylindricalCompletion.ambient.field z = D.liouville.field z.val.val :=
  C.stretchedField_original_carrier z hz

/-- The all-real exponential end identity uses exactly the supplied
original boundary form, including at negative radii. -/
theorem cylindricalCompletion_original_end_primitive
    (x : D.domain.boundary.Point) (r : ℝ) (v : Model (d - 1)) (s : ℝ) :
    evalOne C.cylindricalCompletion.ambient.primitive (C.cylindricalCompletion.endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.cylindricalCompletion.endMap (x, r) (v, s)) =
      Real.exp r * evalOne (D.domain.boundaryForm D.liouville.primitive) x v := by
  have h := C.cylindricalCompletion.end_primitive x r v s
  rw [C.localized_boundaryForm] at h
  exact h

end LiouvilleDomain.FlowCollar

namespace LiouvilleDomain

/-- A supplied compact Liouville domain constructs its own collar and
completion on the resulting localized presentation. No collar or completed
ambient is required from the caller. -/
def cylindricalCompletion {d : ℕ} (D : LiouvilleDomain d) :
    Completion D.flowCollar.localizedDomain :=
  D.flowCollar.cylindricalCompletion

theorem nonempty_cylindricalCompletion {d : ℕ} (D : LiouvilleDomain d) :
    Nonempty (Completion D.flowCollar.localizedDomain) :=
  ⟨D.cylindricalCompletion⟩

end LiouvilleDomain
end FsFltz.Geometry
