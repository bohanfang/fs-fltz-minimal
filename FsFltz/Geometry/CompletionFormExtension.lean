import FsFltz.Geometry.CompletionFamilyFields

/-!
# Constructing a one-form on a fixed completion

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.

The compact interior and nonnegative cylinder partition a completion. Push
the compact form through the inverse inclusion differential on the first
piece, and push `exp(r)` times its boundary restriction through the inverse
end differential on the second. Injectivity makes the chosen coordinates
unique. This constructs the raw completed form without a completed-form
witness as input. In dimension zero the end case is empty.

For a family, the compact/end overlap equation is an explicit hypothesis on
an open parameter-dependent cylinder neighborhood. Tangent surjectivity
turns that equation into the cylindrical coefficient formula for the
constructed form even at negative radii. The existing compact/cylinder
regularity theorem then proves joint smoothness. The presentation squares
identify this output with the actual transported completion primitives;
their contraction equations give regularity of the actual transported fields.

This is a conditional foundation producer. It does not construct a Liouville
collar, parameter-dependent collar presentations, or the geometric objects
asserted by `thm:target` (lines 352–415).
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

private def inclusionTangentEquiv (x : D.domain.extension.Point) :
    Model d ≃L[ℝ] Model d :=
  (LinearEquiv.ofBijective
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x).toLinearMap
    ⟨C.inclusion.immersion x,
      LinearMap.injective_iff_surjective.mp (C.inclusion.immersion x)⟩).toContinuousLinearEquiv

private def endTangentEquiv (q : D.domain.boundary.Point × ℝ) :
    (Model (d - 1) × ℝ) ≃L[ℝ] Model d :=
  (C.endMap_isLocalDiffeomorph q).mfderivToContinuousLinearEquiv (by simp)

private def pushCompactForm (α : D.domain.extension.Form 1)
    (x : D.domain.extension.Point) : Model d [⋀^Fin 1]→L[ℝ] ℝ :=
  (α x).compContinuousLinearMap (C.inclusionTangentEquiv x).symm.toContinuousLinearMap

private def pushEndForm (α : D.domain.extension.Form 1)
    (q : D.domain.boundary.Point × ℝ) : Model d [⋀^Fin 1]→L[ℝ] ℝ :=
  Real.exp q.2 • (D.domain.boundaryForm α q.1).compContinuousLinearMap
    ((ContinuousLinearMap.fst ℝ (Model (d - 1)) ℝ).comp
      (C.endTangentEquiv q).symm.toContinuousLinearMap)

private def nonnegativeEndCoordinates (z : C.ambient.manifold.Point)
    (hz : z ∉ C.inclusion.map '' interior D.domain.carrier) :
    D.domain.boundary.Point × Ici (0 : ℝ) :=
  (show z ∈ range (fun q : D.domain.boundary.Point × Ici (0 : ℝ) =>
      C.endMap (q.1, q.2)) by rw [C.range_nonnegative_endMap]; exact hz).choose

private theorem nonnegativeEndCoordinates_spec (z : C.ambient.manifold.Point)
    (hz : z ∉ C.inclusion.map '' interior D.domain.carrier) :
    C.endMap ((C.nonnegativeEndCoordinates z hz).1,
      (C.nonnegativeEndCoordinates z hz).2) = z :=
  (show z ∈ range (fun q : D.domain.boundary.Point × Ici (0 : ℝ) =>
      C.endMap (q.1, q.2)) by rw [C.range_nonnegative_endMap]; exact hz).choose_spec

/-- A raw completed one-form built from the compact coefficients and their
actual boundary restriction. Smoothness requires the explicit overlap equation
in `isSmoothFormFamily_extendCompactForm`. -/
def extendCompactForm (α : D.domain.extension.Form 1) : C.ambient.manifold.Form 1 := by
  classical
  exact fun z => if hz : z ∈ C.inclusion.map '' interior D.domain.carrier then
    C.pushCompactForm α hz.choose
  else
    C.pushEndForm α ((C.nonnegativeEndCoordinates z hz).1,
      (C.nonnegativeEndCoordinates z hz).2)

set_option backward.isDefEq.respectTransparency false in
private theorem extendCompactForm_inclusion (α : D.domain.extension.Form 1)
    (x : D.domain.extension.Point) (hx : x ∈ interior D.domain.carrier) :
    C.extendCompactForm α (C.inclusion.map x) = C.pushCompactForm α x := by
  classical
  have hz : C.inclusion.map x ∈ C.inclusion.map '' interior D.domain.carrier := ⟨x, hx, rfl⟩
  have he : hz.choose = x := C.inclusion.embedding.injective hz.choose_spec.2
  simp only [extendCompactForm, dite_eq_left hz, he]

set_option backward.isDefEq.respectTransparency false in
/-- The constructed form has exactly the supplied compact coefficients on
the compact interior. No regularity or overlap assumption is needed. -/
theorem extendCompactForm_compact_interior (α : D.domain.extension.Form 1)
    (x : D.domain.extension.Point) (hx : x ∈ interior D.domain.carrier) :
    D.domain.extension.pullback C.ambient.manifold C.inclusion.map
      (C.extendCompactForm α) x = α x := by
  unfold pullback
  rw [C.extendCompactForm_inclusion α x hx]
  ext vs
  change α x (fun i => (C.inclusionTangentEquiv x).symm
    ((C.inclusionTangentEquiv x) (vs i))) = α x vs
  simp only [ContinuousLinearEquiv.symm_apply_apply]

private theorem extendCompactForm_eval_inclusion (α : D.domain.extension.Form 1)
    (x : D.domain.extension.Point) (hx : x ∈ interior D.domain.carrier) (w : Model d) :
    evalOne (C.extendCompactForm α) (C.inclusion.map x)
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w) = evalOne α x w :=
  congrArg (fun A => A (fun _ => w)) (C.extendCompactForm_compact_interior α x hx)

set_option backward.isDefEq.respectTransparency false in
private theorem pushEndForm_eval (α : D.domain.extension.Form 1)
    (q : D.domain.boundary.Point × ℝ) (v : Model (d - 1)) (s : ℝ) :
    C.pushEndForm α q (fun _ =>
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap q (v, s)) = Real.exp q.2 * evalOne (D.domain.boundaryForm α) q.1 v := by
  change Real.exp q.2 * (D.domain.boundaryForm α q.1) (fun _ =>
    ((C.endTangentEquiv q).symm ((C.endTangentEquiv q) (v, s))).1) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The nonnegative-end equation of the constructed form, including radius
zero, follows from unique end coordinates and inversion of its differential. -/
theorem extendCompactForm_end (α : D.domain.extension.Form 1)
    (x : D.domain.boundary.Point) (r : ℝ) (hr : 0 ≤ r)
    (v : Model (d - 1)) (s : ℝ) :
    evalOne (C.extendCompactForm α) (C.endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s)) =
      Real.exp r * evalOne (D.domain.boundaryForm α) x v := by
  classical
  have hz : C.endMap (x, r) ∉ C.inclusion.map '' interior D.domain.carrier := by
    change C.endMap (x, r) ∈ (C.inclusion.map '' interior D.domain.carrier)ᶜ
    rw [← C.range_nonnegative_endMap]
    exact ⟨(x, ⟨r, hr⟩), rfl⟩
  have he : ((C.nonnegativeEndCoordinates (C.endMap (x, r)) hz).1,
      ((C.nonnegativeEndCoordinates (C.endMap (x, r)) hz).2 : ℝ)) = (x, r) :=
    C.endMap_injective (C.nonnegativeEndCoordinates_spec (C.endMap (x, r)) hz)
  unfold evalOne extendCompactForm
  rw [dite_eq_right hz, he]
  exact C.pushEndForm_eval α (x, r) v s

set_option backward.isDefEq.respectTransparency false in
/-- The same cylindrical equation holds at an arbitrary real radius when
the compact coefficients agree with it wherever the two presentations meet.
Thus negative-radius collar coefficients need no completed-form witness. -/
theorem extendCompactForm_end_of_overlap (α : D.domain.extension.Form 1)
    (q : D.domain.boundary.Point × ℝ)
    (hcompat : ∀ x ∈ interior D.domain.carrier, C.inclusion.map x = C.endMap q →
      ∀ (w : Model d) (v : Model (d - 1)) (s : ℝ),
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
          mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
            C.endMap q (v, s) →
        evalOne α x w = Real.exp q.2 * evalOne (D.domain.boundaryForm α) q.1 v)
    (v : Model (d - 1)) (s : ℝ) :
    evalOne (C.extendCompactForm α) (C.endMap q)
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap q (v, s)) =
      Real.exp q.2 * evalOne (D.domain.boundaryForm α) q.1 v := by
  by_cases hz : C.endMap q ∈ C.inclusion.map '' interior D.domain.carrier
  · obtain ⟨x, hx, he⟩ := hz
    have hs := LinearMap.injective_iff_surjective.mp (C.inclusion.immersion x)
    obtain ⟨w, hw⟩ := hs
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap q (v, s))
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w = _ at hw
    calc
      _ = evalOne (C.extendCompactForm α) (C.inclusion.map x)
          (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w) := by
        let a : C.ambient.manifold.Point → Model d [⋀^Fin 1]→L[ℝ] ℝ := C.extendCompactForm α
        change a (C.endMap q) (fun _ => _) = a (C.inclusion.map x) (fun _ => _)
        rw [he]
        exact congrArg (fun u : Model d => a (C.endMap q) (fun _ => u)) hw.symm
      _ = evalOne α x w := C.extendCompactForm_eval_inclusion α x hx w
      _ = _ := hcompat x hx he w v s hw
  · have he := C.endMap_injective (C.nonnegativeEndCoordinates_spec (C.endMap q) hz)
    have hr : 0 ≤ q.2 := by
      rw [← he]
      exact (C.nonnegativeEndCoordinates (C.endMap q) hz).2.property
    exact C.extendCompactForm_end α q.1 q.2 hr v s

/-- Explicit compact/collar coefficient compatibility makes the constructed
completed family jointly smooth. The open set contains the entire nonnegative
cylinder over the parameter interval, and may extend only locally to negative
radii and beyond the interval endpoints. -/
theorem isSmoothFormFamily_extendCompactForm
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) (hU : IsOpen U)
    (hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U)
    (hcompat : ∀ q ∈ U, ∀ x ∈ interior D.domain.carrier,
      C.inclusion.map x = C.endMap q.2 →
      ∀ (w : Model d) (v : Model (d - 1)) (s : ℝ),
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
          mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
            C.endMap q.2 (v, s) →
        evalOne (α q.1) x w = Real.exp q.2.2 *
          evalOne (D.domain.boundaryForm (α q.1)) q.2.1 v) :
    C.ambient.manifold.IsSmoothFormFamily (fun t => C.extendCompactForm (α t)) := by
  apply C.isSmoothFormFamily_of_compact_boundary
    (fun t => C.extendCompactForm (α t)) α hα
    (fun t x hx => C.extendCompactForm_compact_interior (α t) x hx) U hU hpos
  intro q hq v s
  exact C.extendCompactForm_end_of_overlap (α q.1) q.2 (hcompat q hq) v s

/-- Compatible compact coefficients alone produce the real completed form
extension for the actual presented primitive family. The uniqueness theorem
uses both presentation squares, so identification with those primitives is a
conclusion. No raw completed-form extension is supplied as a hypothesis. -/
theorem isSmoothIntervalFormFamily_pullback_of_compact_overlap
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val =
      D.domain.extension.pullback (E t).domain.extension (h t).extensionEquiv
        (E t).liouville.primitive)
    (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) (hU : IsOpen U)
    (hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U)
    (hcompat : ∀ q ∈ U, ∀ x ∈ interior D.domain.carrier,
      C.inclusion.map x = C.endMap q.2 →
      ∀ (w : Model d) (v : Model (d - 1)) (s : ℝ),
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
          mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
            C.endMap q.2 (v, s) →
        evalOne (α q.1) x w = Real.exp q.2.2 *
          evalOne (D.domain.boundaryForm (α q.1)) q.2.1 v) :
    C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive) := by
  refine ⟨fun t => C.extendCompactForm (α t),
    C.isSmoothFormFamily_extendCompactForm α hα U hU hpos hcompat, ?_⟩
  intro t
  apply C.form_eq_pullback_of_compactInterior_end (C' t) (h t) (p t)
  · intro x hx
    rw [C.extendCompactForm_compact_interior (α t.val) x hx, hαeq t]
  · intro x r hr v s
    simpa only [hαeq t] using C.extendCompactForm_end (α t.val) x r hr v s

/-- Applying the construction to the defining compact primitive recovers
the actual primitive of this completion by compact/end coefficient uniqueness. -/
theorem extendCompactForm_primitive :
    C.extendCompactForm D.liouville.primitive = C.ambient.primitive := by
  apply C.form_eq_of_compactInterior_end
  · intro x hx
    rw [C.extendCompactForm_compact_interior D.liouville.primitive x hx,
      C.primitive_on_domain x (interior_subset hx)]
  · intro x r hr v s
    rw [C.extendCompactForm_end D.liouville.primitive x r hr v s, C.end_primitive x r v s]

/-- The constructed extension proves regularity of the actual transported
completion primitives and Liouville fields together. Field regularity uses
their symplecticity and contraction equation through the proved field bridge;
the hypotheses contain only compact regularity and explicit local overlap
coefficients, besides the geometric presentation data. -/
theorem isSmoothIntervalPrimitiveAndFieldFamily_of_compact_overlap
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val =
      D.domain.extension.pullback (E t).domain.extension (h t).extensionEquiv
        (E t).liouville.primitive)
    (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) (hU : IsOpen U)
    (hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U)
    (hcompat : ∀ q ∈ U, ∀ x ∈ interior D.domain.carrier,
      C.inclusion.map x = C.endMap q.2 →
      ∀ (w : Model d) (v : Model (d - 1)) (s : ℝ),
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
          mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
            C.endMap q.2 (v, s) →
        evalOne (α q.1) x w = Real.exp q.2.2 *
          evalOne (D.domain.boundaryForm (α q.1)) q.2.1 v) :
    C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive) ∧
    C.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
      C.ambient.manifold.pullbackVectorField (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.field) := by
  have hp := C.isSmoothIntervalFormFamily_pullback_of_compact_overlap
    E C' h p α hα hαeq U hU hpos hcompat
  exact ⟨hp, C.isSmoothIntervalVectorFieldFamily_pullback_of_primitive_smooth E C' h p hp⟩

end Completion
end FsFltz.Geometry
