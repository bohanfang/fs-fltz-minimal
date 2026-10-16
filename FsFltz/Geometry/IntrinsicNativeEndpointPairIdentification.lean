import FsFltz.Geometry.IntrinsicNativePairIdentification

/-!
# Native pair equations on fixed completed endpoints

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199, and
`sec:lean`, lines 788–814. Strict ambient and constant-scale ribbon maps
on the original compact manifolds, with their literal full-ribbon square,
construct a permitted identification on the given pairs. Their domains and
completions are retained. No completed trajectory square is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.CompletionIdentification
open IntrinsicLiouville

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A A' M M' : Type} [TopologicalSpace A] [TopologicalSpace A']
  [T2Space A] [T2Space A'] [SecondCountableTopology A] [SecondCountableTopology A']
  [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A']
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M']
  [IsManifold (𝓡∂ (a + 1)) ∞ A] [IsManifold (𝓡∂ (a + 1)) ∞ A']
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [IsManifold (𝓡∂ (k + 1)) ∞ M']
  [CompactSpace A] [CompactSpace M]

/-- Original strict ambient and scaled ribbon maps with the literal native
full-ribbon equation assemble on these exact pairs and completions. Applied
at `Q.pair t` and `Q'.pair t'`, this retains the already selected endpoints.
The completed ambient map and escaping-trajectory compatibility are derived. -/
theorem exists_of_nativePairSquare
    (P Q : WitnessedPair n) (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (α : Form a A 1) (α' : Form a A' 1) (μ : Form k M 1) (μ' : Form k M' 1)
    (eA : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A P.ambientDomain.domain.Point ∞)
    (eA' : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A' Q.ambientDomain.domain.Point ∞)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞)
    (eM' : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M' Q.ribbonDomain.domain.Point ∞)
    (hpA : ∀ x, (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eA y).val) x) = α x)
    (hpA' : ∀ x, (Q.ambientDomain.liouville.primitive (eA' x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eA' y).val) x) = α' x)
    (hpM : ∀ x, (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = μ x)
    (hpM' : ∀ x, (Q.ribbonDomain.liouville.primitive (eM' x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM' y).val) x) = μ' x)
    (hcA : HasNativeCoordinateExtensions (k := a) P.ambientDomain.domain.extension (fun x => (eA x).val))
    (hcA' : HasNativeCoordinateExtensions (k := a) Q.ambientDomain.domain.extension (fun x => (eA' x).val))
    (hcM : HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => (eM x).val))
    (hcM' : HasNativeCoordinateExtensions (k := k) Q.ribbonDomain.domain.extension (fun x => (eM' x).val))
    (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv P.ambientDomain.domain.boundary)
    (eB' : (IntrinsicBoundary.smoothManifold a A').SmoothEquiv Q.ambientDomain.domain.boundary)
    (hbA : ∀ x, P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val)
    (hbA' : ∀ x, Q.ambientDomain.domain.boundaryInclusion.map (eB' x) = (eA' x.val).val)
    (j : M → IntrinsicBoundary.Point a A) (j' : M' → IntrinsicBoundary.Point a A')
    (hj : ∀ x, P.ribbonEmbedding.map (eM x).val = eB (j x))
    (hj' : ∀ x, Q.ribbonEmbedding.map (eM' x).val = eB' (j' x))
    (hA : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A A' ∞)
    (hgA : IsLocallyExtendibleNativeMap (k := a) hA)
    (hstrict : ∀ x, (α' (hA x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) hA x) = α x)
    (hM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M' ∞)
    (hgM : IsLocallyExtendibleNativeMap (k := k) hM)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x, (μ' (hM x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) hM x) = c • μ x)
    (hsquare : ∀ x, hA (j x).val = (j' (hM x)).val) :
    ∃ I : CompletionIdentification P Q,
      I.scale = c ∧
      (∀ x, I.ambientEquiv (P.ambientCompletion.inclusion.map (eA x).val) =
        Q.ambientCompletion.inclusion.map (eA' (hA x)).val) ∧
      (∀ y, I.ambientEquiv.symm (Q.ambientCompletion.inclusion.map (eA' y).val) =
        P.ambientCompletion.inclusion.map (eA (hA.symm y)).val) ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eM' (hM x)).val) ∧
      (∀ y, I.ribbonEquiv.inverse (eM' y).val = (eM (hM.symm y)).val) ∧
      (∀ x, I.boundaryEquiv (eB (j x)) = eB' (j' (hM x))) := by
  obtain ⟨f, b, hp, hn, hi, _, _, _, _⟩ :=
    IntrinsicLiouville.exists_scaledEquiv_on_fixed_native_endpoints hdimA
      P.ambientDomain Q.ambientDomain P.ambientCompletion Q.ambientCompletion
      α α' eA eA' hpA hpA' hcA hcA' hA hgA 1 (by norm_num)
      (by simpa only [one_smul] using hstrict)
  have hp' : P.ambientCompletion.ambient.manifold.pullback
      Q.ambientCompletion.ambient.manifold f Q.ambientCompletion.ambient.primitive =
        P.ambientCompletion.ambient.primitive := by simpa only [one_smul] using hp
  have ht (x : M) : ∃ r : ℝ,
      f (P.ambientCompletion.endMap (P.ribbonEmbedding.map (eM x).val, 0)) =
        Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (eM' (hM x)).val, r) := by
    refine ⟨0, ?_⟩
    rw [P.ambientCompletion.endMap_zero, Q.ambientCompletion.endMap_zero,
      hj, hj', hbA, hbA', hn, hsquare]
  obtain ⟨I, hf, hIc, hIn, hIi⟩ := exists_of_nativeRibbon_trajectory_square
    P Q hdimM f hp' μ μ' eM eM' hpM hpM' hcM hcM' hM hgM c hc hscale ht
  refine ⟨I, hIc, ?_, ?_, hIn, hIi, ?_⟩
  · simpa only [hf] using hn
  · simpa only [hf] using hi
  · intro x
    rw [← hj, I.ribbon_square _ (eM x).property, hIn, hj']

end FsFltz.Geometry.CompletionIdentification
