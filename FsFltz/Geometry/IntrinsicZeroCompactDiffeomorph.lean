import FsFltz.Geometry.IntrinsicZeroLiouvilleDomain
import FsFltz.Geometry.NativeCompactMapCompletion

/-!
# Prescribed native zero-dimensional compact maps and their completions

Source: `geoemtric-part-fsf.tex`, the zero-dimensional conventions at
lines 127–128 and `def:pair`, lines 159–160; `def:chain`, lines 171–189;
and `sec:lean`, lines 805–814 and 825–830. Two independently constructed
native zero-dimensional Liouville domains retain their original topology,
atlas, forms and prescribed native diffeomorphism. Every native one-form
vanishes, so primitive scaling imposes no further hypothesis.

The same prescribed map extends between arbitrary chosen original
completions, with both native map and inverse retained on the compact pieces.
Empty native sources are allowed. This is a rank-one foundation, not a
construction of a geometric comparison chain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.IntrinsicZeroLiouville

variable {M N : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [ChartedSpace (Model 0) N] [IsManifold 𝓘(ℝ, Model 0) ∞ N]

/-- The existing zero-dimensional completion supplies a completion of the
original whole native domain, using its original native carrier equivalence
as inclusion. The completed ambient and all-real-time flow are retained. -/
def nativeCompletion (α : (sourceManifold M).Form 1) :
    Completion (liouvilleDomain M α) := by
  let C := completion α
  let e := completionDiffeomorph α
  letI : IsEmpty (liouvilleDomain M α).domain.boundary.Point :=
    (liouvilleDomain M α).domain.zero_boundary rfl
  exact
    { ambient := C.ambient
      inclusion :=
        { map := ⟨e, e.contMDiff⟩
          embedding := e.toHomeomorph.isEmbedding
          immersion := fun _ => fun _ _ _ => PiLp.ext (fun i => Fin.elim0 i) }
      primitive_on_domain := fun x _ => congrFun (completionDiffeomorph_primitive α) x
      field_on_domain := fun _ _ => PiLp.ext (fun i => Fin.elim0 i)
      endMap := C.endMap
      smooth_endMap := C.smooth_endMap
      end_flow := C.end_flow
      end_embedding := C.end_embedding
      end_immersion := C.end_immersion
      end_primitive := fun x => isEmptyElim x
      covering := by
        apply eq_univ_of_forall
        intro y
        obtain ⟨x, rfl⟩ := e.surjective y
        exact Or.inl ⟨x, mem_univ x, rfl⟩
      overlap := fun x => isEmptyElim x }

@[simp] theorem nativeCompletion_inclusion
    (α : (sourceManifold M).Form 1) (x : M) :
    (nativeCompletion α).inclusion.map x = completionDiffeomorph α x := rfl

/-- The original native diffeomorphism itself represents the compact map
between two independently constructed zero-dimensional native domains.
Both full extensions are the original native manifolds. -/
def compactDiffeomorph (α : (sourceManifold M).Form 1) (β : (sourceManifold N).Form 1)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) :
    CompactDomainDiffeomorph (liouvilleDomain M α).domain (liouvilleDomain N β).domain where
  map := h
  inverse := h.symm
  sourceNeighbourhood := univ
  targetNeighbourhood := univ
  open_source := isOpen_univ
  open_target := isOpen_univ
  contains_source := subset_univ _
  contains_target := subset_univ _
  smooth_map := h.contMDiff.contMDiffOn
  smooth_inverse := h.symm.contMDiff.contMDiffOn
  maps_source := fun _ _ => mem_univ _
  maps_target := fun _ _ => mem_univ _
  left_inverse := fun x _ => h.symm_apply_apply x
  right_inverse := fun y _ => h.apply_symm_apply y
  immersion := fun _ _ => fun _ _ _ => PiLp.ext (fun i => Fin.elim0 i)

@[simp] theorem compactDiffeomorph_map
    (α : (sourceManifold M).Form 1) (β : (sourceManifold N).Form 1)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (x : M) :
    (compactDiffeomorph α β h).map x = h x := rfl

@[simp] theorem compactDiffeomorph_inverse
    (α : (sourceManifold M).Form 1) (β : (sourceManifold N).Form 1)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (y : N) :
    (compactDiffeomorph α β h).inverse y = h.symm y := rfl

/-- Algebraic vanishing of zero-dimensional native one-forms proves every
constant-scale primitive identity for the original prescribed map. -/
theorem compactDiffeomorph_primitive_scaled
    (α : (sourceManifold M).Form 1) (β : (sourceManifold N).Form 1)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (c : ℝ) (x : M) :
    (liouvilleDomain M α).domain.extension.pullback (liouvilleDomain N β).domain.extension
      (compactDiffeomorph α β h).map (liouvilleDomain N β).liouville.primitive x =
        c • (liouvilleDomain M α).liouville.primitive x := by
  change (sourceManifold M).pullback (sourceManifold N) h β x = c • α x
  rw [positiveForm_eq_zero M 0 ((sourceManifold M).pullback (sourceManifold N) h β),
    positiveForm_eq_zero M 0 α]
  simp

/-- The native map, on two independent native presentations, extends
between arbitrary original completions. Both compact formulas preserve the
original map and inverse, without an extra representation hypothesis. -/
theorem exists_scaledCompletionEquiv_of_nativeDiffeomorph
    (α : (sourceManifold M).Form 1) (β : (sourceManifold N).Form 1)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞)
    (C : Completion (liouvilleDomain M α)) (C' : Completion (liouvilleDomain N β))
    (c : ℝ) (hc : 0 < c) :
    ∃ e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold,
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        c • C.ambient.primitive ∧
      (∀ x : M, e (C.inclusion.map x) = C'.inclusion.map (h x)) ∧
      (∀ y : N, e.symm (C'.inclusion.map y) = C.inclusion.map (h.symm y)) := by
  obtain ⟨e, _, hp, he, _, _⟩ := C.exists_scaledEquiv_of_compactDiffeomorph C'
    (compactDiffeomorph α β h) c hc (fun x _ => compactDiffeomorph_primitive_scaled α β h c x)
  have he' (x : M) : e (C.inclusion.map x) = C'.inclusion.map (h x) := he x (mem_univ x)
  refine ⟨e, hp, he', ?_⟩
  intro y
  have hi := congrArg e.symm (he' (h.symm y))
  simpa only [e.symm_apply_apply, h.apply_symm_apply] using hi.symm

/-- The primitive-preserving completion map for a prescribed native
zero-dimensional diffeomorphism retains its native compact map and inverse. -/
theorem exists_strictCompletionEquiv_of_nativeDiffeomorph
    (α : (sourceManifold M).Form 1) (β : (sourceManifold N).Form 1)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞)
    (C : Completion (liouvilleDomain M α)) (C' : Completion (liouvilleDomain N β)) :
    ∃ e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold,
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        C.ambient.primitive ∧
      (∀ x : M, e (C.inclusion.map x) = C'.inclusion.map (h x)) ∧
      (∀ y : N, e.symm (C'.inclusion.map y) = C.inclusion.map (h.symm y)) := by
  simpa only [one_smul] using exists_scaledCompletionEquiv_of_nativeDiffeomorph
    α β h C C' 1 (by norm_num)

/-- The two native sources themselves construct both completions and a
strict completed equivalence extending the prescribed native map and its
inverse. No completion or extension presentation is supplied as input. -/
theorem exists_strictConstructedCompletionEquiv_of_nativeDiffeomorph
    (α : (sourceManifold M).Form 1) (β : (sourceManifold N).Form 1)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) :
    ∃ e : (nativeCompletion α).ambient.manifold.SmoothEquiv
      (nativeCompletion β).ambient.manifold,
      (nativeCompletion α).ambient.manifold.pullback (nativeCompletion β).ambient.manifold
        e (nativeCompletion β).ambient.primitive = (nativeCompletion α).ambient.primitive ∧
      (∀ x : M, e (completionDiffeomorph α x) = completionDiffeomorph β (h x)) ∧
      (∀ y : N, e.symm (completionDiffeomorph β y) = completionDiffeomorph α (h.symm y)) := by
  exact exists_strictCompletionEquiv_of_nativeDiffeomorph α β h
    (nativeCompletion α) (nativeCompletion β)

end FsFltz.Geometry.IntrinsicZeroLiouville
