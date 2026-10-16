import FsFltz.Geometry.TailoringOuterBoundaryHittingEmbedding

/-!
# Actual outer hitting embeddings for the same retained marked prefix

Source: `geoemtric-part-fsf.tex`, `thm:target`, lines 352–435, and
`sec:lean`, lines 766–836; `geometric-part-fsf-proof.tex`, `prop:band`
and its following immersion argument, lines 1778–1840.
The finite-input producer retains one choice of potentials, one actual
marked prefix and its full fiber, and one constructed action throughout.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance markedHittingEmbeddingCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance markedHittingEmbeddingSmooth :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- Finite toric input constructs smooth outer hitting embeddings on one
common open neighborhood in the actual full fiber of the same retained
marked prefix, preserving its literal full embedded core and outer marking. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hitting_embeddings
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      ∃ Aamb Cminus Cplus β₀ : ℝ, AmbientEndBound I Aamb ∧
        0 < Cminus ∧ Cminus < Cplus ∧ 0 < β₀ ∧ ∀ β ≥ β₀,
        max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β ∧
        RatioSetWellDefined I (Real.exp β) ∧
        (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp β) Afib ∧
          Afib < Cminus ^ 2 * β ^ 2 / 2) ∧
        ∀ originalK : ℝ, K0 I (Real.exp β) ≤ originalK →
          ∃ K : ℝ, 0 < K ∧ originalK ≤ K / Real.exp β ^ 2 ∧
          ∃ m : RoundingChoice,
            GeometricAdmissibleRounding I (Real.exp β) originalK
              (Cminus ^ 2 * β ^ 2 / 2) (Cplus ^ 2 * β ^ 2 / 2) m ∧
            ∃ P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus
              (Cminus ^ 2 * β ^ 2 / 2) originalK K m,
              ((P.marked.tailoring.embedding parameterOne).comp
                (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
                  P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
                P.marked.tailoring.deformation.target.ribbonCompletion.core =
                  tailoringCoreSection I φEnd β ∧
              range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map =
                  {z | φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
              ∃ G : Flow ℝ (ℝ × LGSpace n),
                ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
                  ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
                  (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2) ∧
                (∀ t p, (G t p).1 = p.1) ∧
                (∀ k ∈ Icc (0 : ℝ) K, ∀ y t, φ (G t (k, y)).2.1 ≤ Cplus ^ 2 * β ^ 2 / 2 →
                  IsMIntegralCurveAt (fun s => (G s (k, y)).2)
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β 1) k)) t) ∧
                (∀ k ∈ Icc (0 : ℝ) K, ∀ y ∈ tailoringCoreSection I φEnd β,
                  0 < deriv (fun t => (tailoringFamily I β 1 (G t (k, y)).2).re) 0) ∧
                ∃ W : Set (ℝ × LGSpace n), IsOpen W ∧
                  Icc (0 : ℝ) K ×ˢ tailoringCoreSection I φEnd β ⊆ W ∧
                  ∃ τ : ℝ × LGSpace n → ℝ,
                    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ τ W ∧
                    (∀ p ∈ W, 0 < τ p ∧ φ (G (τ p) p).2.1 = Cplus ^ 2 * β ^ 2 / 2) ∧
                    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
                      𝓘(ℝ, Model (2 * n)) ∞ (fun p => (G (τ p) p).2) W ∧
                    (∀ k ∈ Icc (0 : ℝ) K,
                      (∀ y ∈ tailoringCoreSection I φEnd β,
                        (∀ s, φ (G s (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 → s = τ (k, y)) ∧
                        ∀ s ∈ Icc (0 : ℝ) (τ (k, y)), (G s (k, y)).2 ∈ tailoringLegendreConic I φEnd ∧
                          1 ≤ (tailoringFamily I β 1 (G s (k, y)).2).re) ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        (tailoringLegendreConic I φEnd ∩
                          range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                            P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map)) ∧
                    let Q := P.marked.tailoring.ribbon_marking parameterOne
                    ∃ (V : TopologicalSpace.Opens ℝ)
                      (U : TopologicalSpace.Opens Q.manifold.Point),
                      Icc (0 : ℝ) K ⊆ V ∧
                      Q.embedding.map ⁻¹' tailoringCoreSection I φEnd β ⊆ U ∧
                      (∀ p ∈ (V : Set ℝ) ×ˢ (U : Set Q.manifold.Point),
                        (p.1, Q.embedding.map p.2) ∈ W) ∧
                      ∃ J : V → (Q.manifold.restrict U).SmoothEmbedding (lgManifold n),
                        (∀ k x, (J k).map x =
                          (G (τ (k.val, Q.embedding.map x.val))
                            (k.val, Q.embedding.map x.val)).2) ∧
                        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
                          𝓘(ℝ, Model (2 * n)) ∞
                          (fun p : ℝ × Q.manifold.Point =>
                            (G (τ (p.1, Q.embedding.map p.2))
                              (p.1, Q.embedding.map p.2)).2)
                          ((V : Set ℝ) ×ˢ (U : Set Q.manifold.Point)) := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, hprefix⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_open_transverse_hits
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, ?_⟩
  intro β hβ
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β hβ
  refine ⟨hR, hset, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst,
    hnative, hcoreTrans, W, hW, hproductW, τ, hτ, hhit, hmap, htimes⟩ := hprefix originalK hK
  refine ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst,
    hnative, hcoreTrans, W, hW, hproductW, τ, hτ, hhit, hmap, htimes, ?_⟩
  let Q := P.marked.tailoring.ribbon_marking parameterOne
  obtain ⟨V, U, hPV, hcoreU, hVU, J, hJ, hsmooth⟩ :=
    Q.exists_uniform_outer_hitting_embeddings
      (contMDiff_tailoringFamily_lgManifold I β 1) hcoreP G hG hfst
      isCompact_Icc hW hproductW hτ
      (fun k hk => (htimes k hk).2.1.injOn) hcoreTrans
  exact ⟨V, U, hPV, hcoreU, hVU, J, hJ, hsmooth⟩

end FsFltz
