import FsFltz.Geometry.PairFamilyConstruction
import FsFltz.Geometry.ImmersionNeighborhood

/-!
# Constructing pair families from compact embedding germs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160; `def:chain`,
lines 163–169; and `sec:lean`, lines 788–814. The ribbon embedding need
only extend smoothly with injective differential on the compact ribbon.
Restriction to a common open embedding neighborhood preserves its entire
compact carrier and its primitive. The localized pair-family constructor
then supplies both collars and completions.

This is a foundation for extended compact data, including dimension zero
and empty carriers. It does not construct intrinsic manifold extensions,
target ribbons, full-fiber markings or the geometric comparison chain.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

/-- A fixed native open inclusion restricts jointly smooth interval
primitives, retaining their actual open extensions at parameter endpoints. -/
theorem isSmoothIntervalFormFamily_restrict {d : ℕ} (M : SmoothManifold d)
    (U : TopologicalSpace.Opens M.Point) (α : Parameter → M.Form 1)
    (hα : M.IsSmoothIntervalFormFamily α) :
    (M.restrict U).IsSmoothIntervalFormFamily
      (fun t => (M.restrict U).pullback M Subtype.val (α t)) :=
  (M.restrict U).isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family M
    (fun _ x => x.val) (contMDiff_subtype_val.comp contMDiff_snd) α hα

/-- For a germ map, the pullback restriction formula only needs actual
differentiability at the point in question, not a globally smooth map. -/
theorem pullback_comp_restrict_val_of_mdifferentiableAt {d e k : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (U : TopologicalSpace.Opens M.Point) (f : M.Point → N.Point)
    (η : N.Form k) (x : U)
    (hf : MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x.val) :
    (M.restrict U).pullback N (fun y : U => f y.val) η x =
      M.pullback N f η x.val := by
  unfold pullback
  rw [M.mfderiv_comp_restrict_val N U x hf]
  rfl

end SmoothManifold

namespace CompactDomain

/-- The native restriction retains the full embedded compact carrier. -/
theorem image_map_restrict_carrier {d : ℕ} {Y : Type*} (F : CompactDomain d)
    (U : TopologicalSpace.Opens F.extension.Point) (hU : F.carrier ⊆ U)
    (j : F.extension.Point → Y) (k : U → Y) (hk : ∀ x, k x = j x.val) :
    k '' (F.restrict U hU).carrier = j '' F.carrier := by
  have he : k = j ∘ (Subtype.val : U → F.extension.Point) := funext hk
  rw [he, image_comp, F.image_restrict_carrier U hU]

/-- Restricting an actual embedding germ preserves the supplied compact
ribbon primitive. The differential is needed only on that compact carrier. -/
theorem ribbon_primitive_restrict {n : ℕ}
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : LiouvilleStructure D) (M : LiouvilleStructure F)
    (j : F.extension.Point → D.boundary.Point) (b : D.boundary.Point → ℝ)
    (U : TopologicalSpace.Opens F.extension.Point) (hU : F.carrier ⊆ U)
    (k : (F.restrict U hU).extension.SmoothEmbedding D.boundary)
    (hk : ∀ x, k.map x = j x.val)
    (hj : ∀ x ∈ F.carrier,
      MDifferentiableAt 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n - 1)) j x)
    (hribbon : ∀ x ∈ F.carrier, F.extension.pullback D.boundary j
      (fun y => b y • D.boundaryForm L.primitive y) x = M.primitive x) :
    ∀ x ∈ (F.restrict U hU).carrier,
      (F.restrict U hU).extension.pullback D.boundary k.map
        (fun y => b y • D.boundaryForm L.primitive y) x =
        (M.restrict U hU).primitive x := by
  intro x hx
  have he : (k.map : U → D.boundary.Point) = fun y => j y.val := funext hk
  rw [he, F.extension.pullback_comp_restrict_val_of_mdifferentiableAt
    D.boundary U j _ x (hj x.val hx), M.restrict_primitive]
  exact hribbon x.val hx

/-- Smooth extended maps that are injective and immersive only on the
compact ribbon construct an actual smooth deformation of witnessed pairs.
A common open embedding neighborhood is produced, and the whole compact
embedding, witness and primitive are retained under the native inclusions.
Both collars and completions are constructed by the existing localized
family constructor. There is no nonemptiness or positive ribbon-dimension
assumption, so dimension-zero and empty ribbons are included. -/
theorem exists_localized_pairDeformation_of_compactEmbeddingGerm_with_presentations {n : ℕ}
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (M : Parameter → LiouvilleStructure F)
    (j : ℝ → F.extension.Point → D.boundary.Point)
    (W : Set (ℝ × F.extension.Point)) (hW : IsOpen W)
    (hcover : parameterInterval ×ˢ F.carrier ⊆ W)
    (hjs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n - 1)) ∞ (fun p : ℝ × F.extension.Point => j p.1 p.2) W)
    (hinj : ∀ t ∈ parameterInterval, InjOn (j t) F.carrier)
    (himm : ∀ t ∈ parameterInterval, ∀ x ∈ F.carrier,
      Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 2))
        𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hM : F.extension.IsSmoothIntervalFormFamily (fun t => (M t).primitive))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t : Parameter, ∀ x ∈ F.carrier,
      F.extension.pullback D.boundary (j t.val)
        (fun y => b t y • D.boundaryForm (L t).primitive y) x = (M t).primitive x) :
    ∃ (U : TopologicalSpace.Opens F.extension.Point) (hU : F.carrier ⊆ U)
      (k : Parameter → (F.restrict U hU).extension.SmoothEmbedding D.boundary),
      (∀ t x, (k t).map x = j t.val x.val) ∧
      ∃ hks : (F.restrict U hU).extension.IsSmoothIntervalMapFamily D.boundary
        (fun t => (k t).map),
      ∃ V : TopologicalSpace.Opens ℝ, parameterInterval ⊆ V ∧
      (V : Set ℝ) ×ˢ (U : Set F.extension.Point) ⊆ W ∧
      (∀ t, (k t).map '' (F.restrict U hU).carrier = j t.val '' F.carrier) ∧
      ∃ hprimitive : ∀ t x, x ∈ (F.restrict U hU).carrier →
        (F.restrict U hU).extension.pullback D.boundary (k t).map
          (fun y => b t y • D.boundaryForm (L t).primitive y) x =
          ((M t).restrict U hU).primitive x,
      ∃ (ambient : LocalizedCompletionFamily D L)
        (ribbon : LocalizedCompletionFamily (F.restrict U hU) (fun t => (M t).restrict U hU)),
      ∃ Q : PairDeformation n,
        (Q.pair = fun t => localizedWitnessedPair ⟨D, L t⟩
          ⟨F.restrict U hU, (M t).restrict U hU⟩ (ambient.collars t) (ribbon.collars t)
          (k t) (b t) (hb.contMDiff_slice t) (hpositive t) (hprimitive t)) ∧
        Q = D.localizedPairDeformation (F.restrict U hU) L
          (fun t => (M t).restrict U hU) k b hL
          (F.extension.isSmoothIntervalFormFamily_restrict U (fun t => (M t).primitive) hM)
          hks hb hpositive ambient ribbon hprimitive := by
  obtain ⟨U, hU, k, hk, hks, V, hIV, hVUW⟩ :=
    F.extension.exists_uniform_embedding_neighborhood D.boundary F.carrier F.compact
      j W hW hcover hjs hinj himm
  have hdiff : ∀ t : Parameter, ∀ x ∈ F.carrier,
      MDifferentiableAt 𝓘(ℝ, Model (2 * n - 2))
        𝓘(ℝ, Model (2 * n - 1)) (j t.val) x := by
    intro t x hx
    have hslice : ContMDiffAt 𝓘(ℝ, Model (2 * n - 2))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2))) ∞
        (fun y : F.extension.Point => (t.val, y)) x :=
      contMDiffAt_const.prodMk contMDiffAt_id
    exact ((hjs.contMDiffAt (hW.mem_nhds (hcover
      (show (t.val, x) ∈ parameterInterval ×ˢ F.carrier from ⟨t.property, hx⟩)))).comp x
      hslice).mdifferentiableAt (by simp)
  have hprimitive : ∀ t x, x ∈ (F.restrict U hU).carrier →
      (F.restrict U hU).extension.pullback D.boundary (k t).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x =
        ((M t).restrict U hU).primitive x := fun t =>
    D.ribbon_primitive_restrict F (L t) (M t) (j t.val) (b t)
      U hU (k t) (hk t) (hdiff t) (hribbon t)
  have hMr : (F.restrict U hU).extension.IsSmoothIntervalFormFamily
      (fun t => ((M t).restrict U hU).primitive) :=
    F.extension.isSmoothIntervalFormFamily_restrict U (fun t => (M t).primitive) hM
  obtain ⟨ambient, ribbon, Q, rfl⟩ := D.exists_localized_pairDeformation_with_presentations (F.restrict U hU)
    L (fun t => (M t).restrict U hU) k b hL hMr hks hb hpositive hprimitive
  exact ⟨U, hU, k, hk, hks, V, hIV, hVUW,
    fun t => F.image_map_restrict_carrier U hU (j t.val) (k t).map (hk t),
    hprimitive, ambient, ribbon,
      D.localizedPairDeformation (F.restrict U hU) L (fun t => (M t).restrict U hU)
        k b hL hMr hks hb hpositive ambient ribbon hprimitive, rfl, rfl⟩


/-- Smooth extended maps that are injective and immersive only on the
compact ribbon construct an actual smooth deformation of witnessed pairs.
A common open embedding neighborhood is produced, and the whole compact
embedding, witness and primitive are retained under the native inclusions.
Both collars and completions are constructed by the existing localized
family constructor. There is no nonemptiness or positive ribbon-dimension
assumption, so dimension-zero and empty ribbons are included. -/
theorem exists_localized_pairDeformation_of_compactEmbeddingGerm {n : ℕ}
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (M : Parameter → LiouvilleStructure F)
    (j : ℝ → F.extension.Point → D.boundary.Point)
    (W : Set (ℝ × F.extension.Point)) (hW : IsOpen W)
    (hcover : parameterInterval ×ˢ F.carrier ⊆ W)
    (hjs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n - 1)) ∞ (fun p : ℝ × F.extension.Point => j p.1 p.2) W)
    (hinj : ∀ t ∈ parameterInterval, InjOn (j t) F.carrier)
    (himm : ∀ t ∈ parameterInterval, ∀ x ∈ F.carrier,
      Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 2))
        𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hM : F.extension.IsSmoothIntervalFormFamily (fun t => (M t).primitive))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t : Parameter, ∀ x ∈ F.carrier,
      F.extension.pullback D.boundary (j t.val)
        (fun y => b t y • D.boundaryForm (L t).primitive y) x = (M t).primitive x) :
    ∃ (U : TopologicalSpace.Opens F.extension.Point) (hU : F.carrier ⊆ U)
      (k : Parameter → (F.restrict U hU).extension.SmoothEmbedding D.boundary),
      (∀ t x, (k t).map x = j t.val x.val) ∧
      (F.restrict U hU).extension.IsSmoothIntervalMapFamily D.boundary
        (fun t => (k t).map) ∧
      ∃ V : TopologicalSpace.Opens ℝ, parameterInterval ⊆ V ∧
      (V : Set ℝ) ×ˢ (U : Set F.extension.Point) ⊆ W ∧
      (∀ t, (k t).map '' (F.restrict U hU).carrier = j t.val '' F.carrier) ∧
      ∃ hprimitive : ∀ t x, x ∈ (F.restrict U hU).carrier →
        (F.restrict U hU).extension.pullback D.boundary (k t).map
          (fun y => b t y • D.boundaryForm (L t).primitive y) x =
          ((M t).restrict U hU).primitive x,
      ∃ A : (t : Parameter) → LiouvilleDomain.FlowCollar
        (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
      ∃ B : (t : Parameter) → LiouvilleDomain.FlowCollar
        (⟨F.restrict U hU, (M t).restrict U hU⟩ : LiouvilleDomain (2 * n - 2)),
      ∃ Q : PairDeformation n,
        Q.pair = fun t => localizedWitnessedPair ⟨D, L t⟩
          ⟨F.restrict U hU, (M t).restrict U hU⟩ (A t) (B t)
          (k t) (b t) (hb.contMDiff_slice t) (hpositive t) (hprimitive t) := by
  obtain ⟨U, hU, k, hk, hks, V, hIV, hVUW, himage, hprimitive, ambient, ribbon, Q, hQ, _⟩ :=
    D.exists_localized_pairDeformation_of_compactEmbeddingGerm_with_presentations
      F L M j W hW hcover hjs hinj himm b hL hM hb hpositive hribbon
  exact ⟨U, hU, k, hk, hks, V, hIV, hVUW, himage, hprimitive,
    ambient.collars, ribbon.collars, Q, hQ⟩

end CompactDomain

end FsFltz.Geometry
