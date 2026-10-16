import FsFltz.Geometry.FlowAbsorption
import FsFltz.Geometry.CylindricalCompletion
import FsFltz.Geometry.CompletionComparison
import FsFltz.Geometry.FixedAmbient

/-!
# Actual inclusion completion markings from flow absorption

Source: `geometric-part-fsf-proof.tex`, `lem:absorption`, lines 444–468;
`geoemtric-part-fsf.tex`, `g:initial`, lines 374–384, and `sec:lean`,
lines 805–814. A complete Liouville flow crosses an outward exhaustion
level exactly once. Negative entry supplies the exterior coverage. The
native boundary-orbit immersion and primitive identities then realize the
specified ambient as a completion; the existing strict completion comparison
constructs the actual inclusion marking from any chosen completion.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function

namespace FsFltz.Geometry.FlowAbsorptionMarking
open SmoothManifold

/-- A positive derivative at and above a level makes its superlevel
forward invariant. The scalar barrier theorem handles possible level crossings. -/
theorem level_le_on_Icc {f q : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (q t) t)
    {A a b : ℝ} (hpos : ∀ t, A ≤ f t → 0 < q t) (ha : A ≤ f a) :
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

/-- Once the orbit is at or above an outward level, its exhaustion
strictly increases at every later time. -/
theorem scalar_lt_of_level_le {f q : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (q t) t)
    {A a b : ℝ} (hpos : ∀ t, A ≤ f t → 0 < q t)
    (ha : A ≤ f a) (hab : a < b) : f a < f b := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun t => (hderiv t).continuousAt)
  have hm : StrictMonoOn f (Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b)
    hf.continuousOn (fun t ht => by
      rw [(hderiv t).deriv]
      exact hpos t (level_le_on_Icc hderiv hpos ha t (interior_subset ht)))
  exact hm (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab

section ScalarFlow

variable {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (ρ q : X → ℝ)
  (hderiv : ∀ x t, HasDerivAt (fun s => ρ (F s x)) (q (F t x)) t)
  {A : ℝ} (hpos : ∀ x, A ≤ ρ x → 0 < q x)

include hderiv hpos

/-- A boundary trajectory is strictly outside the sublevel at every
positive time. -/
theorem scalar_flow_pos {x : X} (hx : ρ x = A) {t : ℝ} (ht : 0 < t) :
    A < ρ (F t x) := by
  have h := scalar_lt_of_level_le (hderiv x) (fun s => hpos (F s x))
    (show A ≤ ρ (F 0 x) by rw [F.map_zero_apply, hx]) ht
  simpa only [F.map_zero_apply, hx] using h

/-- The same boundary trajectory is strictly inside the sublevel at
every negative time. This proves absence of return crossings. -/
theorem scalar_flow_neg {x : X} (hx : ρ x = A) {t : ℝ} (ht : t < 0) :
    ρ (F t x) < A := by
  by_contra h
  have h' := scalar_lt_of_level_le (hderiv x) (fun s => hpos (F s x))
    (le_of_not_gt h) ht
  rw [F.map_zero_apply, hx] at h'
  linarith

/-- The only time at which a boundary orbit meets this level is zero. -/
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
  (hpos : ∀ x, A ≤ ρ x →
    0 < D.domain.extension.scalarDerivative ρ x
      (D.domain.extension.liouvilleVector D.liouville.primitive x))

include hρ hfrontier hpos

omit hρ hpos in
private theorem boundary_level (b : D.domain.boundary.Point) :
    ρ (D.domain.boundaryInclusion.map b) = A := by
  have hb := D.domain.boundaryInclusion_mem_frontier b
  rwa [hfrontier] at hb

/-- The actual all-real boundary-orbit map is injective. A coincidence
would produce a second crossing of the same exhaustion level. -/
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

omit hρ hfrontier hpos in
set_option backward.isDefEq.respectTransparency false in
/-- Outward boundary transversality gives local smooth inverses of the
actual boundary-orbit map, before any completion has been constructed. -/
theorem boundaryOrbitMap_isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ (P.completeFlow.boundaryOrbitMap D.domain) := by
  by_cases hd₀ : d = 0
  · subst d
    have : IsEmpty D.domain.boundary.Point := D.domain.zero_boundary rfl
    intro p
    exact isEmptyElim p.1
  · have hprod : IsManifold ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
        (D.domain.boundary.Point × ℝ) := inferInstance
    rw [← modelWithCornersSelf_prod]
    let : ChartedSpace (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ) :=
      prodChartedSpace (Model (d - 1)) D.domain.boundary.Point ℝ ℝ
    have : IsManifold 𝓘(ℝ, Model (d - 1) × ℝ) ∞ (D.domain.boundary.Point × ℝ) := by
      rw [← modelWithCornersSelf_prod] at hprod
      exact hprod
    apply isLocalDiffeomorph_of_bijective_mfderiv_manifold
    · have hs := P.completeFlow.smooth_boundaryOrbitMap D.domain
      rw [← modelWithCornersSelf_prod] at hs
      exact hs
    · intro p
      have heq : Module.finrank ℝ (Model (d - 1) × ℝ) = Module.finrank ℝ (Model d) := by
        simp only [Module.finrank_prod, Model, finrank_euclideanSpace_fin, Module.finrank_self]
        omega
      have hi := P.completeFlow.boundaryOrbitMap_immersion D.domain D.liouville
        (fun b => (D.liouville.field_eq_liouvilleVector _
          (D.domain.boundaryInclusion_mem_carrier b)).symm) p
      rw [← modelWithCornersSelf_prod] at hi
      exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hi⟩

/-- The actual all-real boundary-orbit map is an open smooth embedding.
Its inverse regularity follows from transversality, and injectivity from
the proved single-crossing property. -/
theorem boundaryOrbitMap_isOpenEmbedding : Topology.IsOpenEmbedding
    (P.completeFlow.boundaryOrbitMap D.domain) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (P.completeFlow.smooth_boundaryOrbitMap D.domain).continuous
    (boundaryOrbitMap_injective D P ρ hρ hfrontier hpos)
    (boundaryOrbitMap_isLocalDiffeomorph D P).isOpenMap

variable (hcarrier : D.domain.carrier = {x | ρ x ≤ A})
  (habsorb : ∀ x : D.domain.extension.Point, ∃ T : ℝ, 0 ≤ T ∧
    ρ (P.completeFlow.flow (-T) x) ≤ A)

include hcarrier habsorb

omit hpos in
/-- Negative entry gives an actual nonnegative boundary representative of
every exterior point, using the intermediate value theorem along its orbit. -/
theorem exists_boundaryOrbitMap_of_notMem {x : D.domain.extension.Point}
    (hx : x ∉ D.domain.carrier) :
    ∃ (b : D.domain.boundary.Point) (r : ℝ), 0 ≤ r ∧
      P.completeFlow.boundaryOrbitMap D.domain (b, r) = x := by
  obtain ⟨T, hT, hentry⟩ := habsorb x
  have hxlevel : A < ρ x := by
    have hnot : ¬ ρ x ≤ A := by simpa only [hcarrier, mem_ofPred_eq] using hx
    exact lt_of_not_ge hnot
  have hc : Continuous (fun s => ρ (P.completeFlow.flow s x)) :=
    continuous_iff_continuousAt.mpr
      (fun t => (P.completeFlow.hasDerivAt_scalar_orbit ρ hρ x t).continuousAt)
  obtain ⟨t, ht, hlevel⟩ := intermediate_value_Icc (by linarith : -T ≤ 0)
    hc.continuousOn (show A ∈ Icc (ρ (P.completeFlow.flow (-T) x))
      (ρ (P.completeFlow.flow 0 x)) from
      ⟨hentry, by simpa only [Flow.map_zero_apply] using hxlevel.le⟩)
  have hb : P.completeFlow.flow t x ∈ frontier D.domain.carrier := by
    rw [hfrontier]
    exact hlevel
  rw [← D.domain.boundary_range] at hb
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, -t, by linarith [ht.2], ?_⟩
  change P.completeFlow.flow (-t) (D.domain.boundaryInclusion.map b) = x
  rw [hb, ← P.completeFlow.flow.map_add, neg_add_cancel, Flow.map_zero_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The given complete ambient, with its actual identity inclusion and
boundary flow, is a completion of the sublevel domain. The exterior
embedding, covering and overlap are proved from outwardness and negative
entry; no completion map or inverse is supplied. -/
def completionOfSublevelAbsorption : Completion D where
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
    · obtain ⟨b, r, hr, he⟩ := exists_boundaryOrbitMap_of_notMem D P ρ hρ
        hfrontier hcarrier habsorb hx
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

/-- The constructed ambient completion has its actual inclusion marking
given by the identity diffeomorphism. -/
def identityInclusionMarking : InclusionMarking
    (completionOfSublevelAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb)
    P.toCompleteLiouvilleManifold (fun x => x.val) where
  equiv := Diffeomorph.refl 𝓘(ℝ, Model d) D.domain.extension.Point ∞
  primitive := D.domain.extension.pullback_id D.liouville.primitive
  inclusion := fun _ => rfl
  flow_induced := fun _ _ => rfl

/-- Negative absorption constructs a primitive-preserving smooth marking
from any chosen native completion onto this prescribed ambient, restricting
to the literal inclusion of the compact domain. -/
def inclusionMarkingOfSublevelAbsorption (C : Completion D) :
    InclusionMarking C P.toCompleteLiouvilleManifold (fun x => x.val) :=
  C.transportInclusionMarking
    (completionOfSublevelAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb)
    P.toCompleteLiouvilleManifold (fun x => x.val)
    (identityInclusionMarking D P ρ hρ hfrontier hpos hcarrier habsorb)

/-- The completion and actual identity marking produce finite type of the
prescribed ambient primitive. In particular the compact domain is the
supplied literal sublevel and the ambient is unchanged. -/
def finiteTypeOfSublevelAbsorption :
    FiniteTypePrimitive D.domain.extension D.liouville.primitive where
  complete := P
  compactDomain := D
  completion := completionOfSublevelAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb
  compactEmbedding :=
    (completionOfSublevelAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb).inclusion
  marking := identityInclusionMarking D P ρ hρ hfrontier hpos hcarrier habsorb

/-- An actual primitive-preserving smooth diffeomorphism from an arbitrary
completion, with the prescribed compact inclusion and all-real boundary
flow formula, is a consequence of the constructed marking. -/
theorem exists_diffeomorph_of_sublevel_absorption (C : Completion D) :
    ∃ e : C.ambient.manifold.SmoothEquiv D.domain.extension,
      C.ambient.manifold.pullback D.domain.extension e D.liouville.primitive =
        C.ambient.primitive ∧
      (∀ x : D.domain.Point, e (C.inclusion.map x.val) = x.val) ∧
      (∀ b r, e (C.endMap (b, r)) =
        P.completeFlow.flow r (D.domain.boundaryInclusion.map b)) := by
  let Q := inclusionMarkingOfSublevelAbsorption D P ρ hρ hfrontier hpos hcarrier habsorb C
  refine ⟨Q.equiv, Q.primitive, Q.inclusion, ?_⟩
  intro b r
  have h := Q.flow_induced b r
  rw [Q.inclusion ⟨D.domain.boundaryInclusion.map b,
    D.domain.boundaryInclusion_mem_carrier b⟩] at h
  exact h

end Sublevel

end FsFltz.Geometry.FlowAbsorptionMarking
