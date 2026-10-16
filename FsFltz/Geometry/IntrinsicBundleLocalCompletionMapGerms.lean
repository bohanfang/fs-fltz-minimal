import FsFltz.Geometry.IntrinsicBundleInteriorTransport
import FsFltz.Geometry.IntrinsicBundleLocalCompletionFamily
import FsFltz.Geometry.IntrinsicNativeCompletionFamilySeam

/-!
# Real compact germs for the original local-to-global completed comparison

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814.
The original local compact chart changes into the chosen compatible global
chart. Its actual target-valued real interior germs compose with the retained
global compact presentation into the same fixed completed ambient. The
resulting interval formula is literal, rather than merely abstract smoothness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- Actual native real germs compose with a jointly smooth real target
map, keeping the real parameter unchanged in the composition. -/
theorem HasSmoothManifoldTargetFamilyOn.postcomp_joint {d r m : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold r) (P : SmoothManifold m)
    {S : Set Parameter} {v : Parameter → M.Point → N.Point}
    (hv : HasSmoothManifoldTargetFamilyOn M N S v)
    (G : ℝ × N.Point → P.Point)
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) 𝓘(ℝ, Model m) ∞ G) :
    HasSmoothManifoldTargetFamilyOn M P S (fun t x => G (t.val, v t x)) := by
  intro t ht x
  obtain ⟨U, hpU, β, hβ, heq⟩ := hv t ht x
  let q : U → ℝ × N.Point := fun z => (z.val.1, β z)
  have hq : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) ∞ q :=
    (contMDiff_fst.comp contMDiff_subtype_val).prodMk hβ
  refine ⟨U, hpU, G ∘ q, hG.comp hq, ?_⟩
  intro s hs y hy
  change G (s.val, β ⟨(s.val, y), hy⟩) = _
  rw [heq s hs y hy]

/-- Germs depend only on the original interval values on their actual
parameter set. -/
theorem HasSmoothManifoldTargetFamilyOn.congr {d r : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold r) {S : Set Parameter}
    {f g : Parameter → M.Point → N.Point}
    (hf : HasSmoothManifoldTargetFamilyOn M N S f)
    (he : ∀ t ∈ S, ∀ x, f t x = g t x) :
    HasSmoothManifoldTargetFamilyOn M N S g := by
  intro t ht x
  obtain ⟨U, hpU, β, hβ, heq⟩ := hf t ht x
  exact ⟨U, hpU, β, hβ, fun s hs y hy => (heq s hs y hy).trans (he s hs y)⟩

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- The compact formula of the original local-to-global completion
comparison has actual real target-valued germs at every interior point.
The target is the same retained reference completion of `Q`; the original
ordered compact transition is used literally. -/
theorem compatibleTransition_referenceInterior_germs
    (c g : Trivialization M (π M E))
    (hc : CompatibleTrivialization (𝓡∂ (k + 1)) E c)
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
    (Q : PairDeformation n)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquare : ∀ t x, (Q.ambientPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val) :
    HasSmoothManifoldTargetFamilyOn (IntrinsicInterior.smoothManifold k M)
      Q.source.ambientCompletion.ambient.manifold (c.baseSet ∩ g.baseSet)
      (fun t x => Q.ambientNativeReferenceMap e t (c.coordChange g t x.val)) := by
  let f₀ : M → Q.source.ambientCompletion.ambient.manifold.Point := fun x =>
    Q.source.ambientCompletion.inclusion.map (e parameterZero x).val
  have hf₀ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ f₀ :=
    Q.source.ambientCompletion.inclusion.map.contMDiff.comp
      (Q.source.ambientDomain.domain.contMDiff_subtype_val.comp (e parameterZero).contMDiff)
  let G : ℝ × IntrinsicInterior.Point k M → Q.source.ambientCompletion.ambient.manifold.Point :=
    fun p => f₀ (R p.1 p.2.val)
  have hG : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n)) ∞ G :=
    hf₀.comp (hR.1.comp (contMDiff_id.prodMap IntrinsicInterior.contMDiff_val))
  apply ((compatibleTransition_interior_germs c g hc hg).postcomp_joint
    (IntrinsicInterior.smoothManifold k M) (IntrinsicInterior.smoothManifold k M)
    Q.source.ambientCompletion.ambient.manifold G hG).congr
      (IntrinsicInterior.smoothManifold k M) Q.source.ambientCompletion.ambient.manifold
  intro t ht x
  change f₀ (R t.val (interiorFamilyOn _ _ _ t x).val) = _
  rw [interiorFamilyOn_val _ ht]
  exact (Q.ambientNativeReferenceMap_eq_compact e R hsquare t (c.coordChange g t x.val)).symm

end FsFltz.Geometry.IntrinsicSmoothBundle
