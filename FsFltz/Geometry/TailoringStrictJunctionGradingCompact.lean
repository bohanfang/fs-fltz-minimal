import FsFltz.Geometry.TailoringStrictJunctionGradingRetained
import FsFltz.Geometry.CompletionCompactCompression
import FsFltz.Geometry.EmbeddedCarrierCompactMap

/-!
# Compact native squares align the actual incoming grading datum

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1919,
and `lem:grading`, lines 1994–2030. The full compact native square detects
its derivatives, including on the boundary. The native tensor equations
then align the two completed data through the same strict ambient map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
namespace Completion

variable {n : ℕ} {D : LiouvilleDomain (2 * n)} (C : Completion D)

/-- The full native compact square detects the two actual tensor pullbacks.
No derivative equality, source tensor equality, or ambient grading
homotopy is an additional premise. -/
theorem tensor_eq_of_compact_native_square
    (N X : SmoothManifold (2 * n)) (q : C.ambient.manifold.SmoothEquiv N)
    (f : D.domain.extension.SmoothMap X) (g : N.SmoothMap X)
    (τ : X.Point → SquaredCanonicalTensor n)
    (σ : C.ambient.manifold.Point → SquaredCanonicalTensor n)
    (υ : N.Point → SquaredCanonicalTensor n)
    (hsquare : ∀ x ∈ D.domain.carrier, g (q (C.inclusion.map x)) = f x)
    (hσ : ∀ x ∈ D.domain.carrier, ∀ v : Fin n ⊕ Fin n → Model (2 * n),
      σ (C.inclusion.map x) (fun i =>
        mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) C.inclusion.map x (v i)) =
      τ (f x) (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x (v i)))
    (hυ : ∀ x ∈ D.domain.carrier, ∀ v : Fin n ⊕ Fin n → Model (2 * n),
      υ (q (C.inclusion.map x)) v = τ (g (q (C.inclusion.map x))) (fun i =>
        mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (q (C.inclusion.map x)) (v i)))
    (x : D.domain.extension.Point) (hx : x ∈ D.domain.carrier) :
    pullbackSquaredTensor C.ambient.manifold N q υ (C.inclusion.map x) = σ (C.inclusion.map x) := by
  let F : D.domain.extension.Point → X.Point := g ∘ q ∘ C.inclusion.map
  have hs : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ F :=
    g.contMDiff.comp (q.contMDiff.comp C.inclusion.map.contMDiff)
  have hd := D.domain.mfderiv_eq_of_eqOn_carrier X
    (fun _ _ => hs.mdifferentiableAt (by simp))
    (fun _ _ => f.contMDiff.mdifferentiableAt (by simp)) hsquare x hx
  have hdq := mfderiv_comp x (q.mdifferentiable (by simp) (C.inclusion.map x))
    (C.inclusion.map.contMDiff.mdifferentiableAt (by simp))
  have hdg := mfderiv_comp x (g.contMDiff.mdifferentiableAt (by simp))
    ((q.contMDiff.comp C.inclusion.map.contMDiff).mdifferentiableAt (by simp))
  have hmap (v : Model (2 * n)) :
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (q (C.inclusion.map x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) q (C.inclusion.map x)
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) C.inclusion.map x v)) =
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v := by
    have h := hdg
    rw [hdq] at h
    exact (congrArg (fun A => A v) h).symm.trans (congrArg (fun A => A v) hd)
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) C.inclusion.map x) :=
    LinearMap.injective_iff_surjective.mp (C.inclusion.immersion x)
  ext v
  choose V hV using fun i => hsurj (v i)
  have hv : v = fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      C.inclusion.map x (V i) := funext (fun i => (hV i).symm)
  rw [hv]
  change υ (q (C.inclusion.map x))
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) q (C.inclusion.map x)
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) C.inclusion.map x (V i))) = _
  have ht := hυ x hx (fun i =>
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) q (C.inclusion.map x)
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) C.inclusion.map x (V i)))
  have hframe := funext (fun i => hmap (V i))
  have hτ := congrArg (fun z : X.Point => τ z
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (q (C.inclusion.map x))
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) q (C.inclusion.map x)
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) C.inclusion.map x (V i)))))
    (hsquare x hx)
  exact ht.trans (hτ.trans ((congrArg (τ (f x)) hframe).trans (hσ x hx V).symm))

/-- Native tensor formulas and the same compact marking square align
the prescribed completed source with the actual pulled target datum. -/
theorem maslovHomotopic_of_compact_native_square
    (hne : D.domain.carrier.Nonempty) (N X : SmoothManifold (2 * n))
    (q : C.ambient.manifold.SmoothEquiv N) {η : N.Form 2}
    (hη : C.ambient.manifold.pullback N q η =
      C.ambient.manifold.exteriorDerivative C.ambient.primitive)
    (f : D.domain.extension.SmoothMap X) (g : N.SmoothMap X)
    (τ : X.Point → SquaredCanonicalTensor n)
    (σ : MaslovRepresentative C.ambient.manifold
      (C.ambient.manifold.exteriorDerivative C.ambient.primitive))
    (υ : MaslovRepresentative N η)
    (hsquare : ∀ x ∈ D.domain.carrier, g (q (C.inclusion.map x)) = f x)
    (hσ : ∀ x ∈ D.domain.carrier, ∀ v : Fin n ⊕ Fin n → Model (2 * n),
      σ.tensor (C.inclusion.map x) (fun i =>
        mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) C.inclusion.map x (v i)) =
      τ (f x) (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x (v i)))
    (hυ : ∀ x ∈ D.domain.carrier, ∀ v : Fin n ⊕ Fin n → Model (2 * n),
      υ.tensor (q (C.inclusion.map x)) v = τ (g (q (C.inclusion.map x))) (fun i =>
        mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (q (C.inclusion.map x)) (v i))) :
    MaslovHomotopic σ (υ.pullbackTo q hη) :=
  C.maslovHomotopic_of_eq_on_compact hne σ (υ.pullbackTo q hη)
    (fun x hx => C.tensor_eq_of_compact_native_square N X q f g τ σ.tensor υ.tensor
      hsquare hσ hυ x hx)

end Completion
end FsFltz.Geometry

namespace FsFltz.StrictHittingJunction
open Geometry

private theorem split_graded_chain {n : ℕ} {P Q R : WitnessedPair n}
    {path : ComparisonChain P Q} {step : ComparisonStep n Q R}
    {s : P.Maslov} {v : R.Maslov}
    (g : GradedComparisonChain P (path.cons step) s v) :
    ∃ u : Q.Maslov, Nonempty (GradedComparisonChain P path s u) ∧
      Nonempty (GradedComparisonStep step u v) := by
  cases g with
  | cons initial last => exact ⟨_, ⟨initial⟩, ⟨last⟩⟩

private theorem identification_lift {n : ℕ} {P Q : WitnessedPair n}
    {C : CompletionIdentification P Q} {s : P.Maslov} {u : Q.Maslov}
    (g : GradedComparisonStep (.identification C) s u) :
    Nonempty (GradedCompletionIdentification C s u) := by
  cases g with
  | identification lift => exact ⟨lift⟩

/-- Replace the induced source by a homotopic actual source representative
on this same junction's first strict identification. The witness and
hitting arrows and their shared representatives remain those already
constructed in the three-arrow grading. -/
theorem gradedChain_of_source_homotopic {n : ℕ}
    {P : WitnessedPair n} {H : PairDeformation n} (J : StrictHittingJunction P H)
    {datum source : P.Maslov} {target : H.target.Maslov}
    (g : GradedComparisonChain P J.chain datum target)
    (hs : MaslovHomotopic source datum) :
    Nonempty (GradedComparisonChain P J.chain source target) := by
  obtain ⟨u, ⟨first⟩, ⟨gh⟩⟩ := split_graded_chain g
  obtain ⟨r, ⟨initial⟩, ⟨gw⟩⟩ := split_graded_chain first
  obtain ⟨s, ⟨empty⟩, ⟨gi⟩⟩ := split_graded_chain initial
  cases empty
  obtain ⟨lift⟩ := identification_lift gi
  have he := (J.identification.gradedLift_iff_class_eq _ _).mp ⟨lift⟩
  obtain ⟨lift'⟩ := (J.identification.gradedLift_iff_class_eq source _).mpr
    ((Quot.sound hs).trans he)
  exact ⟨(((GradedComparisonChain.nil source).cons (.identification lift')).cons gw).cons gh⟩

end FsFltz.StrictHittingJunction

namespace FsFltz.PotentialTailoringMarkedPrefix
open Geometry Geometry.SmoothManifold

/-- The actual native compact square forces every rounded compact point
into the hitting collar's compact carrier. This follows from the retained
native sublevel containment and actual localized carrier image. -/
theorem hitting_marking_mem_carrier {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
    {β Cplus Aminus K : ℝ} {m : RoundingChoice}
    (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    {L : Parameter → LiouvilleStructure P.tailoring_ambient_marking.domain}
    (C : (⟨P.tailoring_ambient_marking.domain, L parameterZero⟩ :
      LiouvilleDomain (2 * n)).FlowCollar)
    (i : P.tailoring.deformation.target.ambientDomain.domain.Point →
      C.cylindricalCompletion.ambient.manifold.Point)
    (hi : ∀ x : P.tailoring.deformation.target.ambientDomain.domain.Point,
      (P.tailoring_ambient_marking.nativeEmbedding.comp C.originalInclusion).map (i x) =
        (P.tailoring.embedding parameterOne).map x.val)
    (x : P.tailoring.deformation.target.ambientDomain.domain.Point) :
    i x ∈ C.localizedDomain.domain.carrier := by
  let O := P.tailoring_ambient_marking
  have hsource : φ ((P.tailoring.embedding parameterOne).map x.val).1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0 := by
    have hy := mem_image_of_mem (P.tailoring.embedding parameterOne).map x.property
    have hy' := (Set.ext_iff.mp (P.tailoring.ambient_image parameterOne)
      ((P.tailoring.embedding parameterOne).map x.val)).mp hy
    exact sub_nonpos.mpr (tailoringRoundedDomain_subset I φ β 1
      (Cplus ^ 2 * β ^ 2 / 2) (Real.exp_pos β) m hy').1
  have hnative : (P.tailoring.embedding parameterOne).map x.val ∈ O.nativeEmbedding.map '' O.domain.carrier := by
    rw [O.native_image]
    exact hsource
  obtain ⟨y, hy, hye⟩ := hnative
  obtain ⟨z, hz, hzy⟩ := (Set.ext_iff.mp C.image_originalInclusion_carrier y).mpr hy
  have heq : (O.nativeEmbedding.comp C.originalInclusion).map z =
      (O.nativeEmbedding.comp C.originalInclusion).map (i x) := by
    change O.nativeEmbedding.map (C.originalInclusion.map z) = _
    rw [hzy, hye]
    exact (hi x).symm
  exact ((O.nativeEmbedding.comp C.originalInclusion).embedding.injective heq) ▸ hz

end FsFltz.PotentialTailoringMarkedPrefix
