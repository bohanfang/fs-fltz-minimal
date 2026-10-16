import FsFltz.Geometry.CompletionFamily
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Coefficient equations from completion presentation squares

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. The compact and nonnegative cylindrical
equations of transported completion primitives follow from the actual
presentation squares and the strict primitive formulas of the completions.
The cylinder calculation includes radius zero, using uniqueness of the
derivative on the closed half-cylinder. A completed form is uniquely
determined by these coefficients and its compact interior coefficients.
This identifies compatible raw extensions with the actual transported
primitive family, removing a separately supplied identification from the
regularity bridge. It does not assert agreement on negative radii or
construct parameter extensions.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

private theorem mfderiv_eq_of_eqOn {a b : ℕ}
    (M : SmoothManifold a) (N : SmoothManifold b)
    (f g : M.Point → N.Point) (S : Set M.Point) (hS : UniqueMDiffOn 𝓘(ℝ, Model a) S)
    (heq : EqOn f g S) (x : M.Point) (hx : x ∈ S)
    (hf : MDifferentiableAt 𝓘(ℝ, Model a) 𝓘(ℝ, Model b) f x)
    (hg : MDifferentiableAt 𝓘(ℝ, Model a) 𝓘(ℝ, Model b) g x) :
    mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model b) f x =
      mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model b) g x := by
  have h := mfderivWithin_congr (I := 𝓘(ℝ, Model a)) (I' := 𝓘(ℝ, Model b))
    (fun _ hy => heq hy) (heq hx)
  rw [mfderivWithin_eq_mfderiv (hS x hx) hf,
    mfderivWithin_eq_mfderiv (hS x hx) hg] at h
  ext v
  exact congrArg (fun L => L v) h

namespace DomainPresentationEquiv

/-- The boundary of the transported compact primitive is its actual
boundary restriction transported through the specified boundary map. -/
theorem boundaryForm_pullback {d : ℕ} {D E : CompactDomain d}
    (h : DomainPresentationEquiv D E) (α : E.extension.Form 1) :
    D.boundaryForm (D.extension.pullback E.extension h.extensionEquiv α) =
      D.boundary.pullback E.boundary h.boundaryEquiv (E.boundaryForm α) := by
  rw [CompactDomain.boundaryForm,
    ← D.boundary.pullback_comp D.extension E.extension
      (fun x => D.boundaryInclusion.map.contMDiff.mdifferentiableAt (by simp))
      (fun x => h.extensionEquiv.contMDiff.mdifferentiableAt (by simp))]
  have hs : (h.extensionEquiv ∘ D.boundaryInclusion.map : D.boundary.Point → E.extension.Point) =
      E.boundaryInclusion.map ∘ h.boundaryEquiv := funext h.boundary_square
  rw [hs, D.boundary.pullback_comp E.boundary E.extension
    (fun x => h.boundaryEquiv.contMDiff.mdifferentiableAt (by simp))
    (fun x => E.boundaryInclusion.map.contMDiff.mdifferentiableAt (by simp))]
  rfl

end DomainPresentationEquiv

namespace CompletionPresentationEquiv

variable {d : ℕ} {D E : LiouvilleDomain d}
  {C : Completion D} {C' : Completion E}
  {h : DomainPresentationEquiv D.domain E.domain}

/-- Transport of the completed primitive restricts to transport of the
compact primitive on the actual interior, with no coefficient equation
assumed independently of the presentation square. -/
theorem compact_primitive_interior (p : CompletionPresentationEquiv C C' h)
    (x : D.domain.extension.Point) (hx : x ∈ interior D.domain.carrier) :
    D.domain.extension.pullback C.ambient.manifold C.inclusion.map
      (C.ambient.manifold.pullback C'.ambient.manifold p.equiv C'.ambient.primitive) x =
      D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive x := by
  have hs : EqOn (p.equiv ∘ C.inclusion.map)
      (C'.inclusion.map ∘ h.extensionEquiv) (interior D.domain.carrier) :=
    fun y hy => p.compact_square y (interior_subset hy)
  have hd := mfderiv_eq_of_eqOn D.domain.extension C'.ambient.manifold
    _ _ _ isOpen_interior.uniqueMDiffOn hs x hx
    ((p.equiv.contMDiff.comp C.inclusion.map.contMDiff).mdifferentiableAt (by simp))
    ((C'.inclusion.map.contMDiff.comp h.extensionEquiv.contMDiff).mdifferentiableAt (by simp))
  rw [← D.domain.extension.pullback_comp C.ambient.manifold C'.ambient.manifold
    (fun y => C.inclusion.map.contMDiff.mdifferentiableAt (by simp))
    (fun y => p.equiv.contMDiff.mdifferentiableAt (by simp))]
  unfold pullback
  rw [hs hx, hd, mfderiv_comp x
    (C'.inclusion.map.contMDiff.mdifferentiableAt (by simp))
    (h.extensionEquiv.contMDiff.mdifferentiableAt (by simp))]
  have hc := C'.primitive_on_domain (h.extensionEquiv x)
    ((h.mem_carrier_iff x).mpr (interior_subset hx))
  ext vs
  exact congrArg (fun A => A (fun i =>
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.extensionEquiv x (vs i))) hc

/-- The nonnegative cylinder square determines its differential, including
at radius zero; smooth extension does not supply a negative-radius square. -/
theorem end_mfderiv (p : CompletionPresentationEquiv C C' h)
    (x : D.domain.boundary.Point) (r : ℝ) (hr : 0 ≤ r) :
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (p.equiv ∘ C.endMap) (x, r) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (fun q : D.domain.boundary.Point × ℝ => C'.endMap (h.boundaryEquiv q.1, q.2))
      (x, r) := by
  have hS : UniqueMDiffOn ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (univ ×ˢ Ici (0 : ℝ)) :=
    (uniqueMDiffOn_univ (I := 𝓘(ℝ, Model (d - 1)))
      (M := D.domain.boundary.Point)).prod (uniqueDiffOn_Ici (0 : ℝ)).uniqueMDiffOn
  have hs : EqOn (p.equiv ∘ C.endMap)
      (fun q : D.domain.boundary.Point × ℝ => C'.endMap (h.boundaryEquiv q.1, q.2))
      (univ ×ˢ Ici (0 : ℝ)) := fun q hq => p.end_square q.1 q.2 hq.2
  have hsm := C'.smooth_endMap.comp
    ((h.boundaryEquiv.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  change ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
    (fun q : D.domain.boundary.Point × ℝ => C'.endMap (h.boundaryEquiv q.1, q.2)) at hsm
  have he := mfderivWithin_congr
    (I := (𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model d))
    (x := (x, r))
    (fun _ hq => hs hq) (hs ⟨mem_univ _, hr⟩)
  rw [mfderivWithin_eq_mfderiv (hS (x, r) ⟨mem_univ _, hr⟩)
      ((p.equiv.contMDiff.comp C.smooth_endMap).mdifferentiableAt (by simp)),
    mfderivWithin_eq_mfderiv (hS (x, r) ⟨mem_univ _, hr⟩)
      (hsm.mdifferentiableAt (by simp))] at he
  ext v
  exact congrArg (fun L => L v) he

set_option backward.isDefEq.respectTransparency false in
/-- At any real radius, an actual end square and its differential give the
exponential coefficients of the transported completed primitive. The
nonnegative-end and collar results both use this calculation. -/
theorem end_primitive_of_end_mfderiv (p : CompletionPresentationEquiv C C' h)
    (x : D.domain.boundary.Point) (r : ℝ)
    (hsquare : p.equiv (C.endMap (x, r)) = C'.endMap (h.boundaryEquiv x, r))
    (hderiv : mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (p.equiv ∘ C.endMap) (x, r) =
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        (fun q : D.domain.boundary.Point × ℝ => C'.endMap (h.boundaryEquiv q.1, q.2))
        (x, r))
    (v : Model (d - 1)) (s : ℝ) :
    evalOne (C.ambient.manifold.pullback C'.ambient.manifold p.equiv C'.ambient.primitive)
      (C.endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s)) = Real.exp r *
      evalOne (D.domain.boundaryForm
        (D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive)) x v := by
  let B : D.domain.boundary.Point × ℝ → E.domain.boundary.Point × ℝ :=
    fun q => (h.boundaryEquiv q.1, q.2)
  have hB : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ B :=
    (h.boundaryEquiv.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hdB : mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) B (x, r) (v, s) =
      (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 1)) h.boundaryEquiv x v, s) := by
    change (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (fun q => ((h.boundaryEquiv ∘ Prod.fst) q, q.2)) (x, r)) (v, s) = _
    rw [mfderiv_prodMk
      ((h.boundaryEquiv.contMDiff.comp contMDiff_fst).mdifferentiableAt (by simp))
      mdifferentiableAt_snd, mfderiv_comp (x, r)
      (h.boundaryEquiv.contMDiff.mdifferentiableAt (by simp)) mdifferentiableAt_fst,
      mfderiv_fst, mfderiv_snd]
    rfl
  have hd := congrArg (fun L => L (v, s)) hderiv
  change (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (p.equiv ∘ C.endMap) (x, r)) (v, s) =
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (C'.endMap ∘ B) (x, r)) (v, s) at hd
  rw [mfderiv_comp (x, r) (p.equiv.contMDiff.mdifferentiableAt (by simp))
      (C.smooth_endMap.mdifferentiableAt (by simp)),
    mfderiv_comp (x, r) (C'.smooth_endMap.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp))] at hd
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) p.equiv (C.endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s)) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      C'.endMap (B (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) B (x, r) (v, s)) at hd
  rw [hdB] at hd
  let a : C'.ambient.manifold.Point → Model d [⋀^Fin 1]→L[ℝ] ℝ := C'.ambient.primitive
  change a (p.equiv (C.endMap (x, r))) (fun _ =>
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) p.equiv (C.endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s))) = _
  rw [hd, congrArg a hsquare]
  change evalOne C'.ambient.primitive (C'.endMap (h.boundaryEquiv x, r))
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      C'.endMap (h.boundaryEquiv x, r)
      (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 1)) h.boundaryEquiv x v, s)) = _
  rw [C'.end_primitive]
  rw [h.boundaryForm_pullback]
  rfl

/-- The transported completion primitive has the prescribed exponential
boundary coefficients on the whole nonnegative end, including the seam.
Both the square and the strict target completion formula are used. -/
theorem end_primitive (p : CompletionPresentationEquiv C C' h)
    (x : D.domain.boundary.Point) (r : ℝ) (hr : 0 ≤ r)
    (v : Model (d - 1)) (s : ℝ) :
    evalOne (C.ambient.manifold.pullback C'.ambient.manifold p.equiv C'.ambient.primitive)
      (C.endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s)) = Real.exp r *
      evalOne (D.domain.boundaryForm
        (D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive)) x v :=
  p.end_primitive_of_end_mfderiv x r (p.end_square x r hr) (p.end_mfderiv x r hr) v s

end CompletionPresentationEquiv

namespace Completion

set_option backward.isDefEq.respectTransparency false in
/-- An actual completion form is determined by its compact interior and
nonnegative cylindrical pullback coefficients. No smoothness of the two
candidate forms is needed: the parametrization differentials are onto. -/
theorem form_eq_of_compactInterior_end {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (η ξ : C.ambient.manifold.Form 1)
    (hcompact : ∀ x ∈ interior D.domain.carrier,
      D.domain.extension.pullback C.ambient.manifold C.inclusion.map η x =
        D.domain.extension.pullback C.ambient.manifold C.inclusion.map ξ x)
    (hend : ∀ x r, 0 ≤ r → ∀ v s,
      evalOne η (C.endMap (x, r))
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap (x, r) (v, s)) =
      evalOne ξ (C.endMap (x, r))
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap (x, r) (v, s))) : η = ξ := by
  funext z
  ext vs
  have hvs : vs = fun _ : Fin 1 => vs 0 := by
    funext i
    rw [Fin.eq_zero i]
  rw [hvs]
  by_cases hz : z ∈ C.inclusion.map '' interior D.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hz
    have hs := LinearMap.injective_iff_surjective.mp (C.inclusion.immersion x)
    obtain ⟨v, hv⟩ := hs (vs 0)
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x v = vs 0 at hv
    have he := congrArg (fun A => A (fun _ => v)) (hcompact x hx)
    change η (C.inclusion.map x) (fun _ =>
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x v) =
      ξ (C.inclusion.map x) (fun _ =>
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x v) at he
    rwa [hv] at he
  · have hz' : z ∈ range (fun q : D.domain.boundary.Point × Ici (0 : ℝ) =>
        C.endMap (q.1, q.2)) := by
      rw [C.range_nonnegative_endMap]
      exact hz
    obtain ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ := hz'
    have hd : d ≠ 0 := by
      intro hd
      have : IsEmpty D.domain.boundary.Point := D.domain.zero_boundary hd
      exact isEmptyElim x
    have hdim : Module.finrank ℝ (Model (d - 1) × ℝ) =
        Module.finrank ℝ (Model d) := by
      simp only [Module.finrank_prod, Model, finrank_euclideanSpace_fin, Module.finrank_self]
      omega
    have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (C.end_immersion (x, r))
    obtain ⟨⟨v, s⟩, he⟩ := hs (vs 0)
    change mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      C.endMap (x, r) (v, s) = vs 0 at he
    have hp := hend x r hr v s
    change η (C.endMap (x, r)) (fun _ =>
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s)) =
      ξ (C.endMap (x, r)) (fun _ =>
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s)) at hp
    rwa [he] at hp

/-- A raw form with compatible compact and cylindrical coefficients is the
actual transported completion primitive. This derives the identification
from the presentation squares rather than accepting it as another input. -/
theorem form_eq_pullback_of_compactInterior_end {d : ℕ} {D E : LiouvilleDomain d}
    (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain)
    (p : CompletionPresentationEquiv C C' h) (η : C.ambient.manifold.Form 1)
    (hcompact : ∀ x ∈ interior D.domain.carrier,
      D.domain.extension.pullback C.ambient.manifold C.inclusion.map η x =
        D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive x)
    (hend : ∀ x r, 0 ≤ r → ∀ v s,
      evalOne η (C.endMap (x, r))
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap (x, r) (v, s)) = Real.exp r *
      evalOne (D.domain.boundaryForm
        (D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive)) x v) :
    η = C.ambient.manifold.pullback C'.ambient.manifold p.equiv C'.ambient.primitive := by
  apply C.form_eq_of_compactInterior_end
  · intro x hx
    rw [hcompact x hx, p.compact_primitive_interior x hx]
  · intro x r hr v s
    rw [hend x r hr v s, p.end_primitive x r hr v s]

/-- Regularity of the actual transported completion family follows from
compatible raw compact/collar extensions. Agreement of the raw completed
extension with the presentation pullbacks is a conclusion. Constructing
these extensions and the open negative-radius collar remains pending. -/
theorem isSmoothIntervalFormFamily_pullback_of_compatible_extensions
    {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val =
      D.domain.extension.pullback (E t).domain.extension (h t).extensionEquiv
        (E t).liouville.primitive)
    (η : ℝ → C.ambient.manifold.Form 1)
    (hcompact : ∀ t x, x ∈ interior D.domain.carrier →
      D.domain.extension.pullback C.ambient.manifold C.inclusion.map (η t) x = α t x)
    (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) (hU : IsOpen U)
    (hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U)
    (hend : ∀ q ∈ U, ∀ v s,
      evalOne (η q.1) (C.endMap q.2)
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap q.2 (v, s)) = Real.exp q.2.2 *
          evalOne (D.domain.boundaryForm (α q.1)) q.2.1 v) :
    C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive) := by
  refine ⟨η, C.isSmoothFormFamily_of_compact_boundary η α hα hcompact U hU hpos hend, ?_⟩
  intro t
  apply C.form_eq_pullback_of_compactInterior_end (C' t) (h t) (p t)
  · intro x hx
    rw [hcompact t.val x hx, hαeq t]
  · intro x r hr v s
    simpa only [hαeq t] using hend (t.val, (x, r))
      (hpos ⟨t.property, ⟨mem_univ _, hr⟩⟩) v s

end Completion
end FsFltz.Geometry
