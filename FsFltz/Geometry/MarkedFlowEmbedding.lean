import FsFltz.Geometry.MarkedHorizontalFlow
import FsFltz.Geometry.BoundaryPresentationBridge
import FsFltz.Geometry.ImmersionNeighborhood

/-!
# Smooth embeddings of one fixed compact carrier under horizontal transport

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 991–1009;
`geoemtric-part-fsf.tex`, `def:chain`, lines 163–169.
The actual native compact atlas detects the full ambient tangent map at
its boundary. A transported constant parameter coordinate therefore makes
the spatial projection immersive on that same carrier. The existing
embedding-neighborhood theorem supplies one common extension neighborhood.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Function

namespace FsFltz.Geometry
open SmoothManifold

/-- The spatial projection of a smooth parameter flow is immersive along a
native compact carrier whenever its transported parameter is constant on
that carrier. The full native inclusion differential detects the parameter
derivative at the boundary; no open preservation hypothesis is added. -/
theorem injective_mfderiv_projectedFlow_on_compactDomain {d e : ℕ}
    (D : CompactDomain d) (N : SmoothManifold e) (j : D.extension.SmoothEmbedding N)
    (Φ : Flow ℝ (ℝ × N.Point))
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) ∞
      (fun q : ℝ × (ℝ × N.Point) => Φ q.1 q.2))
    (t : ℝ) (htime : ∀ x ∈ D.carrier, (Φ t (0, j.map x)).1 = t) :
    ∀ x ∈ D.carrier, Function.Injective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e)
        (fun y => (Φ t (0, j.map y)).2) x) := by
  cases d with
  | zero =>
    intro x hx v w _
    change Model 0 at v w
    exact (show (v : Model 0) = w from Subsingleton.elim _ _)
  | succ k =>
    let g : D.extension.Point → ℝ × N.Point := fun x => Φ t (0, j.map x)
    have hslice (u : ℝ) : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) ∞ (Φ u) :=
      hΦ.comp (contMDiff_const.prodMk contMDiff_id)
    let f : D.extension.Point → ℝ × N.Point := fun x => (0, j.map x)
    have hf : ContMDiff 𝓘(ℝ, Model (k + 1))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) ∞ f :=
      contMDiff_const.prodMk j.map.contMDiff
    have hg : ContMDiff 𝓘(ℝ, Model (k + 1))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) ∞ g := (hslice t).comp hf
    let Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) (ℝ × N.Point) (ℝ × N.Point) ∞ :=
      { toEquiv := (Φ.toHomeomorph t).toEquiv
        contMDiff_toFun := hslice t
        contMDiff_invFun := hslice (-t) }
    have hfst := contMDiff_fst.comp hg
    have hsnd := contMDiff_snd.comp hg
    intro x hx
    let z : D.Point := ⟨x, hx⟩
    have hinc := D.injective_mfderiv_subtype_val z
    have hsurj : Function.Surjective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (Subtype.val : D.Point → D.extension.Point) z) :=
      LinearMap.injective_iff_surjective.mp hinc
    have htimeD : (fun y : D.Point => (g y.val).1) = fun _ => t :=
      funext (fun y => htime y.val y.property)
    have hchain := mfderiv_comp (f := (Subtype.val : D.Point → D.extension.Point))
      (g := fun y => (g y).1) z (hfst.mdifferentiableAt (by simp))
      (D.contMDiff_subtype_val.mdifferentiableAt (by simp))
    rw [show (fun y => (g y).1) ∘ Subtype.val = fun _ : D.Point => t from htimeD,
      mfderiv_const] at hchain
    have htimezero (v : Model (k + 1)) :
        mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) (fun y => (g y).1) x v = 0 := by
      obtain ⟨u, rfl⟩ := hsurj v
      exact (congrArg (fun L => L u) hchain).symm
    have hfinj : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) f x) := by
      rw [mfderiv_prodMk mdifferentiableAt_const
        (j.map.contMDiff.mdifferentiableAt (by simp)), mfderiv_const]
      intro v w heq
      exact j.immersion x (congrArg (fun y : ℝ × Model e => y.2) heq)
    have hginj : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) g x) := by
      change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) (Φ t ∘ f) x)
      rw [mfderiv_comp x ((hslice t).mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp))]
      exact (Ψ.isInvertible_mfderiv (by simp)).injective.comp hfinj
    intro v w heq
    apply hginj
    change mfderiv 𝓘(ℝ, Model (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e))
      (fun y => ((Prod.fst ∘ g) y, (Prod.snd ∘ g) y)) x v =
      mfderiv 𝓘(ℝ, Model (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e))
        (fun y => ((Prod.fst ∘ g) y, (Prod.snd ∘ g) y)) x w
    rw [mfderiv_prodMk (hfst.mdifferentiableAt (by simp))
      (hsnd.mdifferentiableAt (by simp))]
    apply Prod.ext
    · change mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) (fun y => (g y).1) x v =
        mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) (fun y => (g y).1) x w
      exact (htimezero v).trans (htimezero w).symm
    · exact heq

/-- One fixed native compact carrier moves by the actual projected flow
through smooth embeddings on a common open spatial neighborhood. The
extension family retains exactly the flow formula, including at endpoints. -/
theorem exists_uniform_projectedFlow_embedding_neighborhood {d e : ℕ}
    (D : CompactDomain d) (N : SmoothManifold e) (j : D.extension.SmoothEmbedding N)
    (Φ : Flow ℝ (ℝ × N.Point))
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model e)) ∞
      (fun q : ℝ × (ℝ × N.Point) => Φ q.1 q.2))
    (htime : ∀ t ∈ parameterInterval, ∀ x ∈ D.carrier,
      (Φ t (0, j.map x)).1 = t) :
    ∃ (U : TopologicalSpace.Opens D.extension.Point) (_hDU : D.carrier ⊆ U)
      (J : Parameter → (D.extension.restrict U).SmoothEmbedding N),
      (∀ t x, (J t).map x = (Φ t.val (0, j.map x.val)).2) ∧
      (D.extension.restrict U).IsSmoothIntervalMapFamily N (fun t => (J t).map) := by
  let E : ℝ → D.extension.Point → N.Point := fun t x => (Φ t (0, j.map x)).2
  have hE : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × D.extension.Point => E q.1 q.2) :=
    contMDiff_snd.comp (hΦ.comp
      (contMDiff_fst.prodMk
        (contMDiff_const.prodMk (j.map.contMDiff.comp contMDiff_snd))))
  have hinj : ∀ t ∈ parameterInterval, InjOn (E t) D.carrier := by
    intro t ht x hx y hy heq
    apply j.embedding.injective
    have htotal : Φ t (0, j.map x) = Φ t (0, j.map y) :=
      Prod.ext ((htime t ht x hx).trans (htime t ht y hy).symm) heq
    exact congrArg (fun p : ℝ × N.Point => p.2) ((Φ.toHomeomorph t).injective htotal)
  have himm : ∀ t ∈ parameterInterval, ∀ x ∈ D.carrier,
      Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) (E t) x) := by
    intro t ht
    exact injective_mfderiv_projectedFlow_on_compactDomain D N j Φ hΦ t (htime t ht)
  obtain ⟨U, hDU, J, heq, hJ, _V, _hV, _hVU⟩ :=
    D.extension.exists_uniform_embedding_neighborhood N D.carrier D.compact E univ
      isOpen_univ (subset_univ _) hE.contMDiffOn hinj himm
  exact ⟨U, hDU, J, heq, hJ⟩

end FsFltz.Geometry
