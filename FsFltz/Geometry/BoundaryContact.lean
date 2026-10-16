import FsFltz.Geometry.BoundarySmooth

/-!
# Contact primitive of the induced completion boundary map

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 183–189, and `sec:lean`,
lines 805–814. The contact pullback law is derived from the strict ambient
primitive equality and the actual completed end primitive, without supplying
the boundary pullback law as an input.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the completed end primitive along a varying boundary section
depends only on its boundary derivative; its radial derivative contributes zero. -/
theorem endMap_section_primitive {d k : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (M : SmoothManifold k) (ψ : M.Point → D.domain.boundary.Point) (s : M.Point → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model (d - 1)) ∞ ψ)
    (hs : ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, ℝ) ∞ s) (x : M.Point) (v : M.Tangent x) :
    evalOne C.ambient.primitive (C.endMap (ψ x, s x))
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model d) (fun y => C.endMap (ψ y, s y)) x v) =
      Real.exp (s x) * evalOne (D.domain.boundaryForm D.liouville.primitive) (ψ x)
        (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (d - 1)) ψ x v) := by
  have hψ' := hψ.mdifferentiable (by simp) x
  have hs' := hs.mdifferentiable (by simp) x
  have hp := (hψ.prodMk hs).mdifferentiable (by simp) x
  change evalOne C.ambient.primitive (C.endMap (ψ x, s x))
    (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model d)
      (C.endMap ∘ (fun y => (ψ y, s y))) x v) = _
  have hpair : mfderiv 𝓘(ℝ, Model k)
      ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (fun y => (ψ y, s y)) x v =
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (d - 1)) ψ x v,
        mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, ℝ) s x v) := by
    exact congrArg (fun L => L v) (mfderiv_prodMk hψ' hs')
  rw [mfderiv_comp_apply x (C.smooth_endMap.mdifferentiable (by simp) _) hp, hpair]
  exact C.end_primitive (ψ x) (s x)
    (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (d - 1)) ψ x v)
    (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, ℝ) s x v)

set_option backward.isDefEq.respectTransparency false in
/-- The boundary primitive scaling is forced by the strict ambient map and
its end equation. It is derived without using an assumed boundary pullback law. -/
theorem boundary_primitive_of_endMap {d e : ℕ} {D : LiouvilleDomain d}
    {E : LiouvilleDomain e} (C : Completion D) (C' : Completion E)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hprimitive : C.ambient.manifold.pullback C'.ambient.manifold f
      C'.ambient.primitive = C.ambient.primitive)
    (ψ : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (s : D.domain.boundary.Point → ℝ)
    (hs : ContMDiff 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, ℝ) ∞ s)
    (hend : ∀ (x : D.domain.boundary.Point) (r : ℝ),
      f (C.endMap (x, r)) = C'.endMap (ψ x, r + s x)) :
    D.domain.boundary.pullback E.domain.boundary ψ
      (E.domain.boundaryForm E.liouville.primitive) =
      fun x => Real.exp (-s x) • D.domain.boundaryForm D.liouville.primitive x := by
  have hev (x : D.domain.boundary.Point) (v : D.domain.boundary.Tangent x) :
      evalOne (D.domain.boundaryForm D.liouville.primitive) x v =
        Real.exp (s x) * evalOne (E.domain.boundaryForm E.liouville.primitive) (ψ x)
          (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (e - 1)) ψ x v) := by
    let h₀ : D.domain.boundary.Point → C.ambient.manifold.Point :=
      fun y => C.endMap (y, 0)
    have h₀s : ContMDiff 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) ∞ h₀ :=
      C.smooth_endMap.comp (contMDiff_id.prodMk contMDiff_const)
    have hp := congrArg (fun η => evalOne η (h₀ x)
      (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) h₀ x v)) hprimitive
    change evalOne C'.ambient.primitive (f (h₀ x))
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f (h₀ x)
        (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) h₀ x v)) =
      evalOne C.ambient.primitive (h₀ x)
        (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) h₀ x v) at hp
    rw [← mfderiv_comp_apply x (f.contMDiff.mdifferentiable (by simp) (h₀ x))
      (h₀s.mdifferentiable (by simp) x) v] at hp
    have hmap : f ∘ h₀ = fun y => C'.endMap (ψ y, s y) := by
      funext y
      simpa only [h₀, Function.comp_apply, zero_add] using hend y 0
    change evalOne C'.ambient.primitive ((f ∘ h₀) x)
      (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model e) (f ∘ h₀) x v) = _ at hp
    rw [hmap, C'.endMap_section_primitive D.domain.boundary ψ s ψ.contMDiff hs x v] at hp
    have hsource := C.endMap_section_primitive D.domain.boundary id (fun _ => 0)
      contMDiff_id contMDiff_const x v
    simp only [Real.exp_zero, one_mul, mfderiv_id, ContinuousLinearMap.id_apply,
      id_eq] at hsource
    exact (hp.trans hsource).symm
  funext x
  apply ContinuousAlternatingMap.ext
  intro vs
  have hvs : vs = fun _ => vs 0 := by
    funext i
    rw [Fin.eq_zero i]
  rw [hvs]
  change evalOne (E.domain.boundaryForm E.liouville.primitive) (ψ x)
    (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (e - 1)) ψ x (vs 0)) =
      Real.exp (-s x) * evalOne (D.domain.boundaryForm D.liouville.primitive) x (vs 0)
  rw [hev]
  have hexp : Real.exp (-s x) * Real.exp (s x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [← mul_assoc, hexp, one_mul]

/-- A strict completion diffeomorphism produces the smooth boundary
diffeomorphism, smooth shift, all-time end equation, and its required primitive
pullback law together. Boundary contact nondegeneracy remains a separate
intrinsic property of a Liouville domain's boundary form. -/
theorem exists_boundaryEquiv_with_pullback {d e : ℕ} {D : LiouvilleDomain d}
    {E : LiouvilleDomain e} (C : Completion D) (C' : Completion E)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hprimitive : C.ambient.manifold.pullback C'.ambient.manifold f
      C'.ambient.primitive = C.ambient.primitive) :
    ∃ ψ : D.domain.boundary.SmoothEquiv E.domain.boundary,
      ∃ s : D.domain.boundary.Point → ℝ,
        ContMDiff 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, ℝ) ∞ s ∧
        (∀ (x : D.domain.boundary.Point) (r : ℝ),
          f (C.endMap (x, r)) = C'.endMap (ψ x, r + s x)) ∧
        D.domain.boundary.pullback E.domain.boundary ψ
          (E.domain.boundaryForm E.liouville.primitive) =
          fun x => Real.exp (-s x) • D.domain.boundaryForm D.liouville.primitive x := by
  obtain ⟨ψ, s, hs, hend⟩ := C.exists_boundaryEquiv C' f hprimitive
  exact ⟨ψ, s, hs, hend, C.boundary_primitive_of_endMap C' f hprimitive ψ s hs hend⟩

end Completion

end FsFltz.Geometry
