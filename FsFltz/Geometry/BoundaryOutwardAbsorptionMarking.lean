import FsFltz.Geometry.FlowAbsorptionMarking
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Inclusion completion markings from boundary outwardness and absorption

Source: `geometric-part-fsf-proof.tex`, `lem:absorption`, lines 444–468,
and `prop:allinitial`, lines 915–948; `geoemtric-part-fsf.tex`,
`g:initial`, lines 374–384, and `sec:lean`, lines 805–814.
Only the derivative on the defining zero level must be positive. A scalar
barrier proves single boundary crossing, while finite negative entry gives
coverage of the exterior. The native boundary-flow local diffeomorphism and
primitive identities then construct the actual inclusion completion marking.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function

namespace FsFltz.Geometry.BoundaryOutwardAbsorptionMarking
open SmoothManifold

/-- Boundary-positive derivatives prevent a scalar trajectory from crossing
downward through a level. No derivative sign is required above the level. -/
theorem level_le_on_Icc {f q : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (q t) t)
    {A a b : ℝ} (hpos : ∀ t, f t = A → 0 < q t) (ha : A ≤ f a) :
    ∀ t ∈ Icc a b, A ≤ f t := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun t => (hderiv t).continuousAt)
  have hb := image_le_of_deriv_right_lt_deriv_boundary
    (a := a) (b := b) (f := fun t => -f t) (f' := fun t => -q t)
    hf.neg.continuousOn (fun t _ => (hderiv t).neg.hasDerivWithinAt)
    (B := fun _ => -A) (B' := fun _ => 0) (by linarith)
    (fun t => hasDerivAt_const t (-A)) (fun t _ he => by
      have hp := hpos t (by linarith)
      linarith)
  intro t ht
  have h := hb ht
  linarith

/-- Every later time is strictly above a boundary-positive level, even if
the scalar trajectory has nonpositive derivatives away from that level.
A return to the level would be a local minimum with a positive derivative. -/
theorem level_lt_of_boundary_deriv_pos {f q : ℝ → ℝ}
    (hderiv : ∀ t, HasDerivAt f (q t) t) {A a b : ℝ}
    (hpos : ∀ t, f t = A → 0 < q t) (ha : A ≤ f a) (hab : a < b) :
    A < f b := by
  have hb : A ≤ f b := level_le_on_Icc hderiv hpos ha b ⟨hab.le, le_rfl⟩
  by_contra hnot
  have he : f b = A := le_antisymm (le_of_not_gt hnot) hb
  have hmin : IsLocalMin f b := by
    filter_upwards [Ioi_mem_nhds hab] with t ht
    rw [he]
    exact level_le_on_Icc hderiv hpos ha t ⟨ht.le, le_rfl⟩
  have hz := hmin.hasDerivAt_eq_zero (hderiv b)
  have hp := hpos b he
  linarith

section ScalarFlow

variable {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (ρ q : X → ℝ)
  (hderiv : ∀ x t, HasDerivAt (fun s => ρ (F s x)) (q (F t x)) t)
  {A : ℝ} (hpos : ∀ x, ρ x = A → 0 < q x)

include hderiv hpos

/-- A boundary orbit lies strictly outside the sublevel at every positive
time, using only its derivative sign on the boundary. -/
theorem scalar_flow_pos {x : X} (hx : ρ x = A) {t : ℝ} (ht : 0 < t) :
    A < ρ (F t x) :=
  level_lt_of_boundary_deriv_pos (hderiv x) (fun s => hpos (F s x))
    (show A ≤ ρ (F 0 x) by rw [F.map_zero_apply, hx]) ht

/-- A boundary orbit lies strictly inside the sublevel at every negative
time. A point on or above the level cannot later return to it. -/
theorem scalar_flow_neg {x : X} (hx : ρ x = A) {t : ℝ} (ht : t < 0) :
    ρ (F t x) < A := by
  by_contra hnot
  have h := level_lt_of_boundary_deriv_pos (hderiv x) (fun s => hpos (F s x))
    (le_of_not_gt hnot) ht
  rw [F.map_zero_apply, hx] at h
  exact (lt_irrefl A) h

/-- Boundary positivity gives exactly one crossing time for every boundary
orbit, with no positivity hypothesis on the rest of the superlevel. -/
theorem scalar_flow_eq_level_iff {x : X} (hx : ρ x = A) (t : ℝ) :
    ρ (F t x) = A ↔ t = 0 := by
  constructor
  · intro he
    rcases lt_trichotomy t 0 with ht | ht | ht
    · exact False.elim ((scalar_flow_neg F ρ q hderiv hpos hx ht).ne he)
    · exact ht
    · exact False.elim ((scalar_flow_pos F ρ q hderiv hpos hx ht).ne' he)
  · rintro rfl
    rw [F.map_zero_apply, hx]

end ScalarFlow

section Sublevel

variable {d : ℕ} (D : LiouvilleDomain d)
  (P : CompletePrimitive D.domain.extension D.liouville.primitive)
  (ρ : D.domain.extension.Point → ℝ)
  (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
  {A : ℝ} (hfrontier : frontier D.domain.carrier = {x | ρ x = A})
  (hpos : ∀ x, ρ x = A →
    0 < D.domain.extension.scalarDerivative ρ x
      (D.domain.extension.liouvilleVector D.liouville.primitive x))

include hρ hfrontier hpos

omit hρ hpos in
private theorem boundary_level (b : D.domain.boundary.Point) :
    ρ (D.domain.boundaryInclusion.map b) = A := by
  have hb := D.domain.boundaryInclusion_mem_frontier b
  rwa [hfrontier] at hb

/-- The native all-real boundary-flow map is injective because boundary
outwardness rules out every second crossing of the same level. -/
theorem boundaryOrbitMap_injective : Function.Injective
    (P.completeFlow.boundaryOrbitMap D.domain) := by
  intro p q he
  let F := P.completeFlow.flow
  let z := fun b => D.domain.boundaryInclusion.map b
  change F p.2 (z p.1) = F q.2 (z q.1) at he
  have hshift : F (q.2 - p.2) (z q.1) = z p.1 := by
    calc
      F (q.2 - p.2) (z q.1) = F (-p.2) (F q.2 (z q.1)) := by
        rw [← F.map_add]
        congr 1
        ring
      _ = F (-p.2) (F p.2 (z p.1)) := congrArg (F (-p.2)) he.symm
      _ = z p.1 := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have ht : q.2 - p.2 = 0 := by
    apply (scalar_flow_eq_level_iff F ρ
      (fun x => D.domain.extension.scalarDerivative ρ x
        (D.domain.extension.liouvilleVector D.liouville.primitive x))
      (P.completeFlow.hasDerivAt_scalar_orbit ρ hρ) hpos
      (boundary_level D ρ hfrontier q.1) (q.2 - p.2)).mp
    rw [hshift]
    exact boundary_level D ρ hfrontier p.1
  have hpq : p.2 = q.2 := by linarith
  have hb : p.1 = q.1 := by
    apply D.domain.boundaryInclusion.embedding.injective
    apply (F.toHomeomorph p.2).injective
    change F p.2 (z p.1) = F p.2 (z q.1)
    simpa only [hpq] using he
  exact Prod.ext hb hpq

/-- The actual boundary-flow map is an open smooth embedding. Native
transversality supplies local inverse regularity; single crossing supplies
global injectivity using only the derivative sign on the boundary. -/
theorem boundaryOrbitMap_isOpenEmbedding : Topology.IsOpenEmbedding
    (P.completeFlow.boundaryOrbitMap D.domain) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (P.completeFlow.smooth_boundaryOrbitMap D.domain).continuous
    (boundaryOrbitMap_injective D P ρ hρ hfrontier hpos)
    (FlowAbsorptionMarking.boundaryOrbitMap_isLocalDiffeomorph D P).isOpenMap

variable (hcarrier : D.domain.carrier = {x | ρ x ≤ A})
  (habsorb : ∀ x : D.domain.extension.Point, ∃ T : ℝ, 0 ≤ T ∧
    ρ (P.completeFlow.flow (-T) x) ≤ A)

include hcarrier habsorb

set_option backward.isDefEq.respectTransparency false in
/-- Boundary outwardness and finite negative entry construct the prescribed
ambient as an actual completion, with identity inclusion and native boundary
flow. Exterior coverage uses the absorption IVT; overlap uses single crossing. -/
def completionOfBoundaryOutwardAbsorption : Completion D where
  ambient := P.toCompleteLiouvilleManifold
  inclusion :=
    { map := ContMDiffMap.id
      embedding := Topology.IsEmbedding.id
      immersion := fun x => by
        change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) id x)
        rw [mfderiv_id]
        exact Function.injective_id }
  primitive_on_domain := fun x _ =>
    congrFun (D.domain.extension.pullback_id D.liouville.primitive) x
  field_on_domain := by
    intro x hx
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) id x (D.liouville.field x) =
      D.domain.extension.liouvilleVector D.liouville.primitive x
    rw [mfderiv_id]
    exact D.liouville.field_eq_liouvilleVector x hx
  endMap := P.completeFlow.boundaryOrbitMap D.domain
  smooth_endMap := P.completeFlow.smooth_boundaryOrbitMap D.domain
  end_flow := fun _ _ => rfl
  end_embedding :=
    (boundaryOrbitMap_isOpenEmbedding D P ρ hρ hfrontier hpos).isEmbedding.comp
      (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal)
  end_immersion := P.completeFlow.boundaryOrbitMap_immersion D.domain D.liouville
    (fun b => (D.liouville.field_eq_liouvilleVector _
      (D.domain.boundaryInclusion_mem_carrier b)).symm)
  end_primitive := P.completeFlow.boundaryOrbitMap_primitive D.domain
    D.liouville.primitive P.smooth_primitive P.contraction
  covering := by
    change id '' D.domain.carrier ∪
      P.completeFlow.boundaryOrbitMap D.domain '' (univ ×ˢ Ici (0 : ℝ)) = univ
    rw [image_id]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ D.domain.carrier
    · exact Or.inl hx
    · obtain ⟨b, r, hr, he⟩ := FlowAbsorptionMarking.exists_boundaryOrbitMap_of_notMem
        D P ρ hρ hfrontier hcarrier habsorb hx
      exact Or.inr ⟨(b, r), ⟨mem_univ _, hr⟩, he⟩
  overlap := by
    intro b r hr
    change P.completeFlow.boundaryOrbitMap D.domain (b, r) ∉ id '' D.domain.carrier
    rw [image_id, hcarrier]
    exact not_le_of_gt (scalar_flow_pos P.completeFlow.flow ρ
      (fun x => D.domain.extension.scalarDerivative ρ x
        (D.domain.extension.liouvilleVector D.liouville.primitive x))
      (P.completeFlow.hasDerivAt_scalar_orbit ρ hρ) hpos
      (boundary_level D ρ hfrontier b) hr)

/-- The constructed completion's inclusion marking is the identity smooth
equivalence of the prescribed ambient, with literal primitive preservation. -/
def identityInclusionMarking : InclusionMarking
    (completionOfBoundaryOutwardAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb)
    P.toCompleteLiouvilleManifold (fun x => x.val) where
  equiv := Diffeomorph.refl 𝓘(ℝ, Model d) D.domain.extension.Point ∞
  primitive := D.domain.extension.pullback_id D.liouville.primitive
  inclusion := fun _ => rfl
  flow_induced := fun _ _ => rfl

/-- Boundary outwardness and finite negative entry construct the actual
primitive-preserving inclusion marking from any chosen native completion. -/
def inclusionMarkingOfBoundaryOutwardAbsorption (C : Completion D) :
    InclusionMarking C P.toCompleteLiouvilleManifold (fun x => x.val) :=
  C.transportInclusionMarking
    (completionOfBoundaryOutwardAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb)
    P.toCompleteLiouvilleManifold (fun x => x.val)
    (identityInclusionMarking D P ρ hρ hfrontier hpos hcarrier habsorb)

/-- The constructed identity marking proves finite type of the actual
ambient primitive, with the supplied literal sublevel as compact domain. -/
def finiteTypeOfBoundaryOutwardAbsorption :
    FiniteTypePrimitive D.domain.extension D.liouville.primitive where
  complete := P
  compactDomain := D
  completion := completionOfBoundaryOutwardAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb
  compactEmbedding :=
    (completionOfBoundaryOutwardAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb).inclusion
  marking := identityInclusionMarking D P ρ hρ hfrontier hpos hcarrier habsorb

/-- The inclusion marking yields an actual primitive-preserving smooth
diffeomorphism with the prescribed compact inclusion and all-real boundary
flow formula, without derivative positivity away from the boundary. -/
theorem exists_diffeomorph_of_boundary_outward_absorption (C : Completion D) :
    ∃ e : C.ambient.manifold.SmoothEquiv D.domain.extension,
      C.ambient.manifold.pullback D.domain.extension e D.liouville.primitive =
        C.ambient.primitive ∧
      (∀ x : D.domain.Point, e (C.inclusion.map x.val) = x.val) ∧
      (∀ b r, e (C.endMap (b, r)) =
        P.completeFlow.flow r (D.domain.boundaryInclusion.map b)) := by
  let Q := inclusionMarkingOfBoundaryOutwardAbsorption D P ρ hρ
    hfrontier hpos hcarrier habsorb C
  refine ⟨Q.equiv, Q.primitive, Q.inclusion, ?_⟩
  intro b r
  have h := Q.flow_induced b r
  rw [Q.inclusion ⟨D.domain.boundaryInclusion.map b,
    D.domain.boundaryInclusion_mem_carrier b⟩] at h
  exact h

end Sublevel

end FsFltz.Geometry.BoundaryOutwardAbsorptionMarking
