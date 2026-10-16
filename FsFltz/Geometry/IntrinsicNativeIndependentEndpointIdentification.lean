import FsFltz.Geometry.IntrinsicCompletionBoundaryConjugation

/-!
# Independent native endpoints and literal family junctions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199, and
`sec:lean`, lines 788–814. The endpoints, their completions, and their
native slice comparisons are already selected independently. The original
strict completion map and full-ribbon square construct the identification
on those exact endpoints. A prescribed native ribbon diffeomorphism produces
its compact representative; a represented ribbon map is not an input.

The two native ambient spaces and boundaries can be different. End shifts
are arbitrary real functions. Both positive-dimensional and zero-dimensional
ribbons are covered. The final consumers insert the produced identification
between the two given deformations, retaining their literal endpoint tuples.
These are conditional foundational producers, not the target's geometric
chain, its markings, core equality, or grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.CompletionIdentification
open IntrinsicLiouville SmoothManifold

section PositiveRibbon

variable {n k d e r s : ℕ} [NeZero (2 * n - 2)]
  (P Q : WitnessedPair n)
  (X : SmoothManifold d) (Y : SmoothManifold e)
  (B : SmoothManifold r) (B' : SmoothManifold s)
  (α : X.Form 1) (β : Y.Form 1)
  (S : X.SmoothEquiv P.ambientCompletion.ambient.manifold)
  (S' : Y.SmoothEquiv Q.ambientCompletion.ambient.manifold)
  (hS : X.pullback P.ambientCompletion.ambient.manifold S
    P.ambientCompletion.ambient.primitive = α)
  (hS' : Y.pullback Q.ambientCompletion.ambient.manifold S'
    Q.ambientCompletion.ambient.primitive = β)
  (Ψ : X.SmoothEquiv Y) (hΨ : X.pullback Y Ψ β = α)
  (endX : B.Point × ℝ → X.Point) (endY : B'.Point × ℝ → Y.Point)
  (bS : B.SmoothEquiv P.ambientDomain.domain.boundary)
  (bS' : B'.SmoothEquiv Q.ambientDomain.domain.boundary)
  (hendS : ∀ x t, 0 ≤ t →
    S (endX (x, t)) = P.ambientCompletion.endMap (bS x, t))
  (hendS' : ∀ x t, 0 ≤ t →
    S' (endY (x, t)) = Q.ambientCompletion.endMap (bS' x, t))
  (ψ : B.SmoothEquiv B') (shift : B.Point → ℝ)
  (hshift : ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, ℝ) ∞ shift)
  (hendΨ : ∀ x, ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
    Ψ (endX (x, t)) = endY (ψ x, t + shift x))
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [IsManifold (𝓡∂ (k + 1)) ∞ N]
  [CompactSpace M]
  (hdim : k + 1 = 2 * n - 2) (μ : Form k M 1) (ν : Form k N 1)
  (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    P.ribbonDomain.domain.Point ∞)
  (eN : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) N
    Q.ribbonDomain.domain.Point ∞)
  (hM : ∀ x, (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = μ x)
  (hN : ∀ x, (Q.ribbonDomain.liouville.primitive (eN x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eN y).val) x) = ν x)
  (hcoordM : HasNativeCoordinateExtensions (k := k)
    P.ribbonDomain.domain.extension (fun x => (eM x).val))
  (hcoordN : HasNativeCoordinateExtensions (k := k)
    Q.ribbonDomain.domain.extension (fun x => (eN x).val))
  (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
  (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
  (c : ℝ) (hc : 0 < c)
  (hscale : ∀ x, (ν (h x)).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • μ x)
  (j : M → B.Point) (j' : N → B'.Point)
  (hj : ∀ x, P.ribbonEmbedding.map (eM x).val = bS (j x))
  (hj' : ∀ y, Q.ribbonEmbedding.map (eN y).val = bS' (j' y))
  (hsquare : ∀ x, ψ (j x) = j' (h x))

include hS hS' hΨ hendS hendS' hshift hendΨ hdim hM hN hcoordM hcoordN
  hgerm hc hscale hj hj' hsquare in
/-- Independent retained native presentations construct a permitted step on
the exact endpoints. Native compact-map and inverse formulas are retained,
as are the original ambient map, boundary map and arbitrary shift. -/
theorem exists_of_independentNativeEndpoints :
    ∃ I : CompletionIdentification P Q,
      I.ambientEquiv = (S.symm.trans Ψ).trans S' ∧
      I.scale = c ∧ I.boundaryEquiv = (bS.symm.trans ψ).trans bS' ∧
      I.shift = shift ∘ bS.symm ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eN (h x)).val) ∧
      (∀ y, I.ribbonEquiv.inverse (eN y).val = (eM (h.symm y)).val) := by
  obtain ⟨g, hgnative, hginverse, hgscale⟩ :=
    exists_originalNativeCompactDiffeomorph_on_fixed_endpoints hdim
      P.ribbonDomain Q.ribbonDomain P.ribbonCompletion Q.ribbonCompletion
      μ ν eM eN hM hN hcoordM hcoordN h hgerm c hscale
  obtain ⟨I, hIa, hIg, hIc, hIb, hIs⟩ :=
    exists_of_nativeBoundaryConjugation P Q X Y B B' α β S S' hS hS' Ψ hΨ
      endX endY bS bS' hendS hendS' ψ shift hshift hendΨ
      eM eN eM.surjective h j j' hj hj' hsquare g hgnative c hc hgscale
  exact ⟨I, hIa, hIc, hIb, hIs,
    by simpa only [hIg] using hgnative, by simpa only [hIg] using hginverse⟩

include hS hS' hΨ hendS hendS' hshift hendΨ hdim hM hN hcoordM hcoordN
  hgerm hc hscale hj hj' hsquare in
/-- Two independently selected completed deformations are joined by the step
constructed from their original native data. The four vertices are the actual
endpoint tuples, and the path has exactly three permitted arrows. -/
theorem exists_threeStepChain_of_independentNativeEndpoints
    (F G : PairDeformation n) (hP : P = F.target) (hQ : Q = G.source) :
    ∃ (I : CompletionIdentification P Q) (C : ComparisonChain F.source G.target),
      I.ambientEquiv = (S.symm.trans Ψ).trans S' ∧
      I.scale = c ∧ I.boundaryEquiv = (bS.symm.trans ψ).trans bS' ∧
      I.shift = shift ∘ bS.symm ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eN (h x)).val) ∧
      (∀ y, I.ribbonEquiv.inverse (eN y).val = (eM (h.symm y)).val) ∧
      C = ((Quiver.Path.nil.cons (ComparisonStep.deformation F)).cons
        (ComparisonStep.identification (hP ▸ hQ ▸ I))).cons
          (ComparisonStep.deformation G) ∧
      C.length = 3 ∧ C.vertices = [F.source, P, Q, G.target] := by
  obtain ⟨I, hIa, hIc, hIb, hIs, hIn, hIi⟩ := exists_of_independentNativeEndpoints
    P Q X Y B B' α β S S' hS hS' Ψ hΨ endX endY bS bS'
    hendS hendS' ψ shift hshift hendΨ hdim μ ν eM eN hM hN hcoordM hcoordN
    h hgerm c hc hscale j j' hj hj' hsquare
  subst P Q
  exact ⟨I, ((Quiver.Path.nil.cons (ComparisonStep.deformation F)).cons
    (ComparisonStep.identification I)).cons (ComparisonStep.deformation G),
    hIa, hIc, hIb, hIs, hIn, hIi, rfl, rfl, rfl⟩

end PositiveRibbon

section ZeroRibbon

variable {d e r s : ℕ}
  (P Q : WitnessedPair 1)
  (X : SmoothManifold d) (Y : SmoothManifold e)
  (B : SmoothManifold r) (B' : SmoothManifold s)
  (α : X.Form 1) (β : Y.Form 1)
  (S : X.SmoothEquiv P.ambientCompletion.ambient.manifold)
  (S' : Y.SmoothEquiv Q.ambientCompletion.ambient.manifold)
  (hS : X.pullback P.ambientCompletion.ambient.manifold S
    P.ambientCompletion.ambient.primitive = α)
  (hS' : Y.pullback Q.ambientCompletion.ambient.manifold S'
    Q.ambientCompletion.ambient.primitive = β)
  (Ψ : X.SmoothEquiv Y) (hΨ : X.pullback Y Ψ β = α)
  (endX : B.Point × ℝ → X.Point) (endY : B'.Point × ℝ → Y.Point)
  (bS : B.SmoothEquiv P.ambientDomain.domain.boundary)
  (bS' : B'.SmoothEquiv Q.ambientDomain.domain.boundary)
  (hendS : ∀ x t, 0 ≤ t →
    S (endX (x, t)) = P.ambientCompletion.endMap (bS x, t))
  (hendS' : ∀ x t, 0 ≤ t →
    S' (endY (x, t)) = Q.ambientCompletion.endMap (bS' x, t))
  (ψ : B.SmoothEquiv B') (shift : B.Point → ℝ)
  (hshift : ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, ℝ) ∞ shift)
  (hendΨ : ∀ x, ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
    Ψ (endX (x, t)) = endY (ψ x, t + shift x))
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (Model 0) M] [ChartedSpace (Model 0) N]
  (eM : letI := P.ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞)
  (eN : letI := Q.ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N Q.ribbonDomain.domain.Point ∞)
  (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞)
  (c : ℝ) (hc : 0 < c)
  (j : M → B.Point) (j' : N → B'.Point)
  (hj : ∀ x, P.ribbonEmbedding.map (eM x).val = bS (j x))
  (hj' : ∀ y, Q.ribbonEmbedding.map (eN y).val = bS' (j' y))
  (hsquare : ∀ x, ψ (j x) = j' (h x))

include hS hS' hΨ hendS hendS' hshift hendΨ hc hj hj' hsquare in
/-- Dimension-zero native ribbon maps produce the same independent-endpoint
identification. Vanishing one-forms give the constant scale; empty ribbons
are allowed and no positive-dimensional ribbon instance is introduced. -/
theorem exists_of_independentNativeZeroEndpoints :
    ∃ I : CompletionIdentification P Q,
      I.ambientEquiv = (S.symm.trans Ψ).trans S' ∧
      I.scale = c ∧ I.boundaryEquiv = (bS.symm.trans ψ).trans bS' ∧
      I.shift = shift ∘ bS.symm ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eN (h x)).val) ∧
      (∀ y, I.ribbonEquiv.inverse (eN y).val = (eM (h.symm y)).val) := by
  obtain ⟨g, hgnative, hginverse, hgscale⟩ :=
    IntrinsicZeroLiouville.exists_originalNativeCompactDiffeomorph
      P.ribbonDomain Q.ribbonDomain P.ribbonCompletion Q.ribbonCompletion eM eN h c
  obtain ⟨I, hIa, hIg, hIc, hIb, hIs⟩ :=
    exists_of_nativeBoundaryConjugation P Q X Y B B' α β S S' hS hS' Ψ hΨ
      endX endY bS bS' hendS hendS' ψ shift hshift hendΨ
      eM eN eM.surjective h j j' hj hj' hsquare g hgnative c hc hgscale
  exact ⟨I, hIa, hIc, hIb, hIs,
    by simpa only [hIg] using hgnative, by simpa only [hIg] using hginverse⟩

include hS hS' hΨ hendS hendS' hshift hendΨ hc hj hj' hsquare in
/-- The rank-one version constructs the intervening identification from the
original zero-dimensional ribbon map, with the same literal junctions. -/
theorem exists_threeStepChain_of_independentNativeZeroEndpoints
    (F G : PairDeformation 1) (hP : P = F.target) (hQ : Q = G.source) :
    ∃ (I : CompletionIdentification P Q) (C : ComparisonChain F.source G.target),
      I.ambientEquiv = (S.symm.trans Ψ).trans S' ∧
      I.scale = c ∧ I.boundaryEquiv = (bS.symm.trans ψ).trans bS' ∧
      I.shift = shift ∘ bS.symm ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eN (h x)).val) ∧
      (∀ y, I.ribbonEquiv.inverse (eN y).val = (eM (h.symm y)).val) ∧
      C = ((Quiver.Path.nil.cons (ComparisonStep.deformation F)).cons
        (ComparisonStep.identification (hP ▸ hQ ▸ I))).cons
          (ComparisonStep.deformation G) ∧
      C.length = 3 ∧ C.vertices = [F.source, P, Q, G.target] := by
  obtain ⟨I, hIa, hIc, hIb, hIs, hIn, hIi⟩ := exists_of_independentNativeZeroEndpoints
    P Q X Y B B' α β S S' hS hS' Ψ hΨ endX endY bS bS'
    hendS hendS' ψ shift hshift hendΨ eM eN h c hc j j' hj hj' hsquare
  subst P Q
  exact ⟨I, ((Quiver.Path.nil.cons (ComparisonStep.deformation F)).cons
    (ComparisonStep.identification I)).cons (ComparisonStep.deformation G),
    hIa, hIc, hIb, hIs, hIn, hIi, rfl, rfl, rfl⟩

end ZeroRibbon

end FsFltz.Geometry.CompletionIdentification
