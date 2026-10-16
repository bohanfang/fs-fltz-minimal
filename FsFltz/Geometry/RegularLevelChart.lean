import FsFltz.Geometry.BoundaryCharts

/-!
# Literal level-set charts from local product coordinates

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 910–930,
where regular rounded levels and regular full fibers acquire their actual
manifold structures; `geoemtric-part-fsf.tex`, `g:initial`, lines 371–379,
and `sec:lean`, lines 783–814. A supplied local product normal form is
restricted to the literal level-set subtype. No level-set manifold or
replacement carrier is assumed. Smooth normal forms and atlas compatibility
are separate consumers of this purely topological restriction.
-/

noncomputable section

namespace FsFltz.Geometry

variable {M F K : Type*} [TopologicalSpace M] [TopologicalSpace F] [TopologicalSpace K]

/-- The literal first-coordinate slice is canonically homeomorphic to the
remaining factor. This also covers a zero-dimensional remaining factor. -/
def levelSliceHomeomorph (c : F) : {p : F × K // p.1 = c} ≃ₜ K where
  toFun := fun p => p.val.2
  invFun := fun k => ⟨(c, k), rfl⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact Prod.ext p.property.symm rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

/-- Restrict exact local product coordinates to a literal level set. The
result has the specified open source/target and the actual coordinate maps
in both directions, rather than an unrelated homeomorphic presentation.
It reuses the proved generic corresponding-subtype restriction from
`BoundaryCharts`, followed by the canonical product-slice homeomorphism.
The seed point supplies total values off the chart's target only. -/
theorem exists_restricted_level_chart (f : M → F) (c : F)
    (e : OpenPartialHomeomorph M (F × K))
    (hfirst : ∀ x ∈ e.source, (e x).1 = f x)
    (a : {x : M // f x = c}) :
    ∃ r : OpenPartialHomeomorph {x : M // f x = c} K,
      r.source = Subtype.val ⁻¹' e.source ∧
      r.target = (fun k : K => (c, k)) ⁻¹' e.target ∧
      (∀ x ∈ r.source, r x = (e x.val).2) ∧
      (∀ k ∈ r.target, (r.symm k).val = e.symm (c, k)) := by
  let s : Set M := {x | f x = c}
  let t : Set (F × K) := {p | p.1 = c}
  have himage : e.IsImage s t := by
    intro x hx
    change (e x).1 = c ↔ f x = c
    rw [hfirst x hx]
  let b : t := ⟨(c, (e a.val).2), rfl⟩
  obtain ⟨r0, hs, ht, hf, hg⟩ := exists_openPartialHomeomorph_subtypes e himage a b
  let r := r0.trans (levelSliceHomeomorph c).toOpenPartialHomeomorph
  have hsource : r.source = Subtype.val ⁻¹' e.source := by
    simp [r, hs]
  have htarget : r.target = (fun k : K => (c, k)) ⁻¹' e.target := by
    simp [r, ht, levelSliceHomeomorph]
    rfl
  refine ⟨r, hsource, htarget, ?_, ?_⟩
  · intro x hx
    have hx0 : x ∈ r0.source := by rwa [hsource, ← hs] at hx
    change (r0 x).val.2 = (e x.val).2
    exact congrArg Prod.snd (hf x hx0)
  · intro k hk
    have hk0 : (⟨(c, k), rfl⟩ : t) ∈ r0.target := by
      rw [ht]
      rwa [htarget] at hk
    change (r0.symm (⟨(c, k), rfl⟩ : t)).val = e.symm (c, k)
    exact hg _ hk0

end FsFltz.Geometry
