import FsFltz.Geometry.PairGermFamilyConstruction

/-!
# Pair families from genuinely partial embedding germs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The embedding extension is supplied only on an open neighborhood of
the compact parameter-ribbon product. A compact tube restricts the spatial
extension before invoking the compact embedding-neighborhood construction.
The auxiliary map outside the tube's parameter interval uses time zero
on that same restricted spatial domain. It requires no point of the target
independent of the partial map, even when the target and ribbon are empty.

This constructs families on supplied compact extension presentations.
It does not construct an extension of an arbitrary intrinsic manifold with
boundary, the target ribbons, full-fiber markings or the comparison chain.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry

namespace PartialMapFamily

/-- The actual open spatial domain of a partial family at time `t`. -/
def spatialSlice {X : Type*} [TopologicalSpace X]
    (W : TopologicalSpace.Opens (ℝ × X)) (t : ℝ) : TopologicalSpace.Opens X :=
  ⟨{x | (t, x) ∈ W}, W.isOpen.preimage (continuous_const.prodMk continuous_id)⟩

/-- Restriction of a partial family to its native open spatial slice. -/
def sliceMap {X Y : Type*} [TopologicalSpace X]
    (W : TopologicalSpace.Opens (ℝ × X)) (j : W → Y) (t : ℝ) :
    spatialSlice W t → Y := fun x => j ⟨(t, x.val), x.property⟩

end PartialMapFamily

namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false

/-- Inclusion between native open restrictions has the identity differential. -/
theorem mfderiv_openInclusion {d : ℕ} (M : SmoothManifold d)
    (U V : TopologicalSpace.Opens M.Point) (hUV : U ≤ V) (x : U) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (TopologicalSpace.Opens.inclusion hUV) x =
      ContinuousLinearMap.id ℝ (Model d) := by
  have he := mfderiv_comp (f := TopologicalSpace.Opens.inclusion hUV)
    (g := (Subtype.val : V → M.Point)) x
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_inclusion (I := 𝓘(ℝ, Model d)) (n := ∞) hUV).mdifferentiableAt (by simp))
  erw [M.mfderiv_restrict_val U x,
    M.mfderiv_restrict_val V (TopologicalSpace.Opens.inclusion hUV x)] at he
  exact he.symm

/-- Pullback through inclusion between open restrictions is the literal
restriction of the same native partial-map pullback. -/
theorem pullback_openInclusion {d e k : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (U V : TopologicalSpace.Opens M.Point) (hUV : U ≤ V)
    (f : V → N.Point) (η : N.Form k) (x : U)
    (hf : MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f
      (TopologicalSpace.Opens.inclusion hUV x)) :
    (M.restrict U).pullback N (f ∘ TopologicalSpace.Opens.inclusion hUV) η x =
      (M.restrict V).pullback N f η (TopologicalSpace.Opens.inclusion hUV x) := by
  unfold pullback
  rw [mfderiv_comp x hf
    ((contMDiff_inclusion (I := 𝓘(ℝ, Model d)) (n := ∞) hUV).mdifferentiableAt (by simp)),
    M.mfderiv_openInclusion U V hUV x]
  rfl

/-- The native slice of a jointly smooth partial family is smooth. -/
theorem contMDiff_partialSlice {d e : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (W : TopologicalSpace.Opens (ℝ × M.Point))
    (j : W → N.Point)
    (hj : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ j)
    (t : ℝ) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ (PartialMapFamily.sliceMap W j t) := by
  let a : PartialMapFamily.spatialSlice W t → W :=
    fun x => ⟨(t, x.val), x.property⟩
  have ha : ContMDiff 𝓘(ℝ, Model d) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff W a).mp
      (contMDiff_const.prodMk contMDiff_subtype_val)
  exact hj.comp ha

/-- A partial map on an open neighborhood of the compact product restricts
to a common spatial neighborhood and an honest smooth parameter extension.
Outside the open parameter neighborhood its auxiliary map uses its own
time-zero value; no nonempty-target assumption is needed. -/
theorem exists_partialFamily_rectangle {d e : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (K : Set M.Point) (hK : IsCompact K)
    (W : TopologicalSpace.Opens (ℝ × M.Point))
    (hcover : parameterInterval ×ˢ K ⊆ W) (j : W → N.Point)
    (hj : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ j) :
    ∃ (U : TopologicalSpace.Opens M.Point) (V : TopologicalSpace.Opens ℝ)
      (_hKU : K ⊆ U) (_hIV : parameterInterval ⊆ V)
      (hVU : (V : Set ℝ) ×ˢ (U : Set M.Point) ⊆ W)
      (g : ℝ → U → N.Point),
      (∀ t (ht : t ∈ V) x, g t x = j ⟨(t, x.val), hVU ⟨ht, x.property⟩⟩) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
        (fun p : ℝ × U => g p.1 p.2) ((V : Set ℝ) ×ˢ univ) := by
  obtain ⟨v, u, hvo, huo, hIv, hKu, hvu⟩ :=
    generalized_tube_lemma isCompact_Icc hK W.isOpen hcover
  let U : TopologicalSpace.Opens M.Point := ⟨u, huo⟩
  let V : TopologicalSpace.Opens ℝ := ⟨v, hvo⟩
  have h0 : (0 : ℝ) ∈ V := hIv (by constructor <;> norm_num)
  let g : ℝ → U → N.Point := fun t x =>
    if ht : t ∈ V then j ⟨(t, x.val), hvu ⟨ht, x.property⟩⟩
    else j ⟨(0, x.val), hvu ⟨h0, x.property⟩⟩
  have hg : ∀ t (ht : t ∈ V) x, g t x =
      j ⟨(t, x.val), hvu ⟨ht, x.property⟩⟩ := by
    intro t ht x
    simp only [g, dite_eq_left ht]
  let P : TopologicalSpace.Opens (ℝ × U) := ⟨(V : Set ℝ) ×ˢ univ, hvo.prod isOpen_univ⟩
  let a : P → W := fun p => ⟨(p.val.1, p.val.2.val), hvu ⟨p.property.1, p.val.2.property⟩⟩
  have hpre : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × U => (p.1, p.2.val)) :=
    contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
  have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff W a).mp (hpre.comp contMDiff_subtype_val)
  have hgs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p : P => g p.val.1 p.val.2) := by
    have he : (fun p : P => g p.val.1 p.val.2) = j ∘ a :=
      funext (fun p => hg p.val.1 p.property.1 p.val.2)
    rw [he]
    exact hj.comp ha
  refine ⟨U, V, hKu, hIv, hvu, g, hg, ?_⟩
  intro p hp
  exact (contMDiffAt_subtype_iff (f := fun q : ℝ × U => g q.1 q.2)
    (x := (⟨p, hp⟩ : P))).mp (hgs.contMDiffAt) |>.contMDiffWithinAt

end SmoothManifold

namespace CompactDomain
open SmoothManifold PartialMapFamily

/-- Genuinely partial smooth embedding germs on supplied compact extension
presentations construct an actual family of witnessed pairs. Both open
restrictions preserve the entire compact ribbon, its embedding and primitive.
The witness is the supplied witness, and both collars and completions come
from the existing localized family construction. Empty targets, empty ribbons
and dimension-zero ribbons require no additional assumptions. -/
theorem exists_localized_pairDeformation_of_partialCompactEmbeddingGerm {n : ℕ}
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (M : Parameter → LiouvilleStructure F)
    (W : TopologicalSpace.Opens (ℝ × F.extension.Point))
    (hcover : parameterInterval ×ˢ F.carrier ⊆ W) (j : W → D.boundary.Point)
    (hj : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n - 1)) ∞ j)
    (hinj : ∀ t ∈ parameterInterval,
      InjOn (sliceMap W j t) (Subtype.val ⁻¹' F.carrier))
    (himm : ∀ t ∈ parameterInterval, ∀ x : spatialSlice W t, x.val ∈ F.carrier →
      Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 2))
        𝓘(ℝ, Model (2 * n - 1)) (sliceMap W j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hM : F.extension.IsSmoothIntervalFormFamily (fun t => (M t).primitive))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t : Parameter, ∀ x : spatialSlice W t.val, x.val ∈ F.carrier →
      (F.extension.restrict (spatialSlice W t.val)).pullback D.boundary
        (sliceMap W j t.val) (fun y => b t y • D.boundaryForm (L t).primitive y) x =
        (M t).primitive x.val) :
    ∃ (U₀ : TopologicalSpace.Opens F.extension.Point) (hU₀ : F.carrier ⊆ U₀)
      (V₀ : TopologicalSpace.Opens ℝ) (hV₀ : parameterInterval ⊆ V₀)
      (hrect : (V₀ : Set ℝ) ×ˢ (U₀ : Set F.extension.Point) ⊆ W)
      (U₁ : TopologicalSpace.Opens (F.restrict U₀ hU₀).extension.Point)
      (hU₁ : (F.restrict U₀ hU₀).carrier ⊆ U₁)
      (k : Parameter → ((F.restrict U₀ hU₀).restrict U₁ hU₁).extension.SmoothEmbedding
        D.boundary),
      (∀ t x, (k t).map x =
        j ⟨(t.val, x.val.val), hrect ⟨hV₀ t.property, x.val.property⟩⟩) ∧
      ((F.restrict U₀ hU₀).restrict U₁ hU₁).extension.IsSmoothIntervalMapFamily
        D.boundary (fun t => (k t).map) ∧
      (∀ t, (k t).map '' ((F.restrict U₀ hU₀).restrict U₁ hU₁).carrier =
        sliceMap W j t.val '' (Subtype.val ⁻¹' F.carrier)) ∧
      ∃ hprimitive : ∀ t x, x ∈ ((F.restrict U₀ hU₀).restrict U₁ hU₁).carrier →
        ((F.restrict U₀ hU₀).restrict U₁ hU₁).extension.pullback D.boundary (k t).map
          (fun y => b t y • D.boundaryForm (L t).primitive y) x =
          (((M t).restrict U₀ hU₀).restrict U₁ hU₁).primitive x,
      ∃ A : (t : Parameter) → LiouvilleDomain.FlowCollar
        (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
      ∃ B : (t : Parameter) → LiouvilleDomain.FlowCollar
        (⟨(F.restrict U₀ hU₀).restrict U₁ hU₁,
          ((M t).restrict U₀ hU₀).restrict U₁ hU₁⟩ : LiouvilleDomain (2 * n - 2)),
      ∃ Q : PairDeformation n,
        Q.pair = fun t => localizedWitnessedPair ⟨D, L t⟩
          ⟨(F.restrict U₀ hU₀).restrict U₁ hU₁,
            ((M t).restrict U₀ hU₀).restrict U₁ hU₁⟩ (A t) (B t)
          (k t) (b t) (hb.contMDiff_slice t) (hpositive t) (hprimitive t) := by
  obtain ⟨U₀, V₀, hU₀, hV₀, hrect, g, hg, hgs⟩ :=
    F.extension.exists_partialFamily_rectangle D.boundary F.carrier F.compact
      W hcover j hj
  have hinc (t : ℝ) (ht : t ∈ parameterInterval) : U₀ ≤ spatialSlice W t :=
    fun x hx => hrect ⟨hV₀ ht, hx⟩
  have he (t : ℝ) (ht : t ∈ parameterInterval) :
      g t = sliceMap W j t ∘ TopologicalSpace.Opens.inclusion (hinc t ht) := by
    funext x
    exact hg t (hV₀ ht) x
  have hgi : ∀ t ∈ parameterInterval, InjOn (g t) (F.restrict U₀ hU₀).carrier := by
    intro t ht x hx y hy hxy
    rw [he t ht] at hxy
    have h := hinj t ht hx hy hxy
    exact Subtype.ext (congrArg (fun z : spatialSlice W t => z.val) h)
  have hgimm : ∀ t ∈ parameterInterval, ∀ x ∈ (F.restrict U₀ hU₀).carrier,
      Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 2))
        𝓘(ℝ, Model (2 * n - 1)) (g t) x) := by
    intro t ht x hx
    rw [he t ht, mfderiv_comp x
      ((F.extension.contMDiff_partialSlice D.boundary W j hj t).mdifferentiableAt (by simp))
      ((contMDiff_inclusion (I := 𝓘(ℝ, Model (2 * n - 2))) (n := ∞)
        (hinc t ht)).mdifferentiableAt (by simp)),
      F.extension.mfderiv_openInclusion U₀ (spatialSlice W t) (hinc t ht) x]
    exact himm t ht (TopologicalSpace.Opens.inclusion (hinc t ht) x) hx
  have hprimitive₀ : ∀ t : Parameter, ∀ x ∈ (F.restrict U₀ hU₀).carrier,
      (F.restrict U₀ hU₀).extension.pullback D.boundary (g t.val)
        (fun y => b t y • D.boundaryForm (L t).primitive y) x =
        ((M t).restrict U₀ hU₀).primitive x := by
    intro t x hx
    rw [he t.val t.property,
      F.extension.pullback_openInclusion D.boundary U₀ (spatialSlice W t.val)
        (hinc t.val t.property) (sliceMap W j t.val) _ x
        ((F.extension.contMDiff_partialSlice D.boundary W j hj t.val).mdifferentiableAt
          (by simp)), (M t).restrict_primitive]
    exact hribbon t (TopologicalSpace.Opens.inclusion (hinc t.val t.property) x) hx
  have hM₀ := F.extension.isSmoothIntervalFormFamily_restrict U₀
    (fun t => (M t).primitive) hM
  have hcover₀ : parameterInterval ×ˢ (F.restrict U₀ hU₀).carrier ⊆
      (V₀ : Set ℝ) ×ˢ univ := fun _ hp => ⟨hV₀ hp.1, mem_univ _⟩
  obtain ⟨U₁, hU₁, k, hk, hks, _, _, _, hki, hprimitive, A, B, Q, hQ⟩ :=
    D.exists_localized_pairDeformation_of_compactEmbeddingGerm (F.restrict U₀ hU₀)
      L (fun t => (M t).restrict U₀ hU₀) g ((V₀ : Set ℝ) ×ˢ univ)
      (V₀.isOpen.prod isOpen_univ) hcover₀ hgs hgi hgimm b hL hM₀ hb hpositive hprimitive₀
  refine ⟨U₀, hU₀, V₀, hV₀, hrect, U₁, hU₁, k, ?_, hks, ?_,
    hprimitive, A, B, Q, hQ⟩
  · intro t x
    exact (hk t x).trans (hg t.val (hV₀ t.property) x.val)
  · intro t
    rw [hki t]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨TopologicalSpace.Opens.inclusion (hinc t.val t.property) x, hx,
        (hg t.val (hV₀ t.property) x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      let z : U₀ := ⟨x.val, hU₀ hx⟩
      exact ⟨z, hx, hg t.val (hV₀ t.property) z⟩

end CompactDomain

end FsFltz.Geometry
