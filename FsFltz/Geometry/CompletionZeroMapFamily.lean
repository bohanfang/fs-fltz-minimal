import FsFltz.Geometry.CompletionMapFamily
import FsFltz.Geometry.ZeroDimensionalCompletion

/-!
# Completed comparison families for zero-dimensional ribbons

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 126–160;
`def:chain`, lines 163–199; and `sec:lean`, lines 783–814 and 825–830.
The boundary of a zero-dimensional compact domain is empty. Consequently
the compact/end map construction needs no collar compatibility hypothesis.
This includes empty ribbons and the source's rank-one ribbon case.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.Completion
open SmoothManifold

variable {D E : LiouvilleDomain 0}

/-- With empty boundary, compact map regularity alone makes the actual
completed extension jointly smooth. There is no collar-overlap assumption. -/
theorem contMDiffOn_extendedMap_zero (C : Completion D) (C' : Completion E)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point)
    (V : TopologicalSpace.Opens ℝ)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model 0) ∞
      (fun p : ℝ × D.domain.extension.Point => g p.1 p.2) ((V : Set ℝ) ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model 0) ∞
      (fun p : ℝ × C.ambient.manifold.Point => C.extendedMap C' g b p.1 p.2)
      ((V : Set ℝ) ×ˢ univ) := by
  apply C.contMDiffOn_extendedMap C' g b V 1 zero_lt_one hg
  · rintro ⟨_, x⟩ _
    exact ((D.domain.zero_boundary rfl).false x).elim
  · intro _ _ q
    exact ((D.domain.zero_boundary rfl).false q.1).elim

/-- In dimension zero every completed point lies in the compact image.
Thus a smooth real compact extension proves interval regularity of any
prescribed completed map with that compact square. -/
theorem isSmoothIntervalMapFamily_of_compact_zero
    (C : Completion D) (C' : Completion E)
    (f : Parameter → C.ambient.manifold.Point → C'.ambient.manifold.Point)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (V : TopologicalSpace.Opens ℝ) (hV : parameterInterval ⊆ V)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model 0) ∞
      (fun p : ℝ × D.domain.extension.Point => g p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hsquare : ∀ t : Parameter, ∀ x ∈ D.domain.carrier,
      f t (C.inclusion.map x) = C'.inclusion.map (g t.val x)) :
    C.ambient.manifold.IsSmoothIntervalMapFamily C'.ambient.manifold f := by
  let b : ℝ → D.domain.boundary.Point → E.domain.boundary.Point :=
    fun _ x => ((D.domain.zero_boundary rfl).false x).elim
  refine ⟨C.extendedMap C' g b, ?_, ?_⟩
  · exact ⟨(V : Set ℝ) ×ˢ univ, V.isOpen.prod isOpen_univ,
      fun _ hp => ⟨hV hp.1, hp.2⟩, C.contMDiffOn_extendedMap_zero C' g b V hg⟩
  · intro t
    funext z
    have hz : z ∈ C.inclusion.map '' D.domain.carrier ∪
        C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := C.covering ▸ mem_univ z
    rcases hz with ⟨x, hx, rfl⟩ | ⟨⟨x, _⟩, _, _⟩
    · exact (C.extendedMap_compact C' g b t.val x hx).trans (hsquare t x hx).symm
    · exact ((D.domain.zero_boundary rfl).false x).elim

/-- Smooth compact presentations and inverse presentations produce actual
jointly smooth strict comparisons of fixed zero-dimensional completions.
No primitive equation, boundary map extension, collar overlap or nonemptiness
is an input: zero-dimensional forms vanish and the boundaries are empty. -/
theorem exists_strictEquivFamily_zero (C : Completion D) (C' : Completion E)
    (h : Parameter → DomainPresentationEquiv D.domain E.domain)
    (g : ℝ → D.domain.extension.Point → E.domain.extension.Point)
    (g' : ℝ → E.domain.extension.Point → D.domain.extension.Point)
    (V : TopologicalSpace.Opens ℝ) (hV : parameterInterval ⊆ V)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model 0) ∞
      (fun p : ℝ × D.domain.extension.Point => g p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hg' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model 0) ∞
      (fun p : ℝ × E.domain.extension.Point => g' p.1 p.2) ((V : Set ℝ) ×ˢ univ))
    (hgeq : ∀ t : Parameter, g t.val = (h t).extensionEquiv)
    (hg'eq : ∀ t : Parameter, g' t.val = (h t).extensionEquiv.symm) :
    ∃ e : Parameter → C.ambient.manifold.SmoothEquiv C'.ambient.manifold,
      (∀ t, C.ambient.manifold.pullback C'.ambient.manifold (e t)
        C'.ambient.primitive = C.ambient.primitive) ∧
      (∀ t x, x ∈ D.domain.carrier →
        e t (C.inclusion.map x) = C'.inclusion.map ((h t).extensionEquiv x)) ∧
      (∀ t y, y ∈ E.domain.carrier →
        (e t).symm (C'.inclusion.map y) = C.inclusion.map ((h t).extensionEquiv.symm y)) ∧
      C.ambient.manifold.IsSmoothIntervalMapFamily C'.ambient.manifold (fun t => e t) ∧
      C'.ambient.manifold.IsSmoothIntervalMapFamily C.ambient.manifold (fun t => (e t).symm) := by
  classical
  have hp (t : Parameter) : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension (h t).extensionEquiv
        E.liouville.primitive x = (1 : ℝ) • D.liouville.primitive x := by
    intro x _
    rw [E.domain.extension.oneForm_eq_zero_of_dimension_zero E.liouville.primitive,
      D.domain.extension.oneForm_eq_zero_of_dimension_zero D.liouville.primitive]
    ext v
    simp [SmoothManifold.pullback]
  choose p hp using fun t =>
    C.exists_scaledPresentation_of_compact_primitive C' (h t) 1 zero_lt_one (hp t)
  have hsquare (t : Parameter) := (p t).compact_square
  have hinverse (t : Parameter) (y : E.domain.extension.Point) (hy : y ∈ E.domain.carrier) :
      (p t).equiv.symm (C'.inclusion.map y) =
        C.inclusion.map ((h t).extensionEquiv.symm y) := by
    apply (p t).equiv.injective
    change (p t).equiv ((p t).equiv.symm (C'.inclusion.map y)) =
      (p t).equiv (C.inclusion.map ((h t).extensionEquiv.symm y))
    rw [(p t).equiv.apply_symm_apply, hsquare t]
    · rw [(h t).extensionEquiv.apply_symm_apply]
    · exact ((h t).symm.mem_carrier_iff y).mpr hy
  refine ⟨fun t => (p t).equiv, ?_, hsquare, hinverse, ?_, ?_⟩
  · intro t
    simpa only [one_smul] using hp t
  · apply C.isSmoothIntervalMapFamily_of_compact_zero C' _ g V hV hg
    intro t x hx
    rw [hgeq t]
    exact hsquare t x hx
  · apply C'.isSmoothIntervalMapFamily_of_compact_zero C _ g' V hV hg'
    intro t y hy
    rw [hg'eq t]
    exact hinverse t y hy

end FsFltz.Geometry.Completion
