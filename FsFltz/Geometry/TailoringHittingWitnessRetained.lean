import FsFltz.Geometry.TailoringHittingWitness
import FsFltz.Geometry.TailoringShrunkHittingEmbedding

/-!
# The positive hitting witness of the same retained full ribbon

Source: `geoemtric-part-fsf.tex`, `thm:target`, lines 352–435, and
`sec:lean`, lines 766–836; `geometric-part-fsf-proof.tex`,
`eq:hittingprimitive` and `eq:ribbonprimitive`, lines 1818–1875.
Finite toric input constructs the full-boundary witness on the same marked
outer domain, using the same original prefix, native action and finite
intrinsic shrinking, with the original full-fiber marking retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance retainedHittingWitnessCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance retainedHittingWitnessSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- The constructed positive witness matches the actual hitting time on the
entire same retained shrunk full ribbon, in the actual native outer boundary. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hitting_witnesses
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
                      ∃ hPV : Icc (0 : ℝ) K ⊆ V,
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
                          ((V : Set ℝ) ×ˢ (U : Set Q.manifold.Point)) ∧
                        ∃ S : IntrinsicShrinkingData P.marked.tailoring.deformation.target,
                          ∃ hU : ∀ x : S.extension,
                            (S.fiberEmbedding Q parameterOne).map x ∈ U,
                          ∃ j : V → (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding
                            P.marked.tailoring_ambient_marking.domain.boundary,
                            (∀ k x,
                              (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map
                                  ((j k).map x) =
                                (S.hittingEmbedding Q U hU V J k).map x) ∧
                            ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
                              𝓘(ℝ, Model (2 * n - 1)) ∞
                              (fun p : V × S.extension => (j p.1).map p.2) ∧
                            ∃ w : ℝ × P.marked.tailoring_ambient_marking.domain.boundary.Point → ℝ,
                              ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 1)))
                                𝓘(ℝ, ℝ) ∞ w ∧ (∀ p, 0 < w p) ∧
                              ∀ k (hk : k ∈ Icc (0 : ℝ) K),
                                ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
                                  w (k, (j ⟨k, hPV hk⟩).map x) =
                                    Real.exp (-τ (k, Q.embedding.map
                                      ((S.fiberEmbedding Q parameterOne).map x))) := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, hprefix⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_hitting_embeddings
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, ?_⟩
  intro β hβ
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β hβ
  refine ⟨hR, hset, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst,
    hnative, hcoreTrans, W, hW, hproductW, τ, hτ, hhit, hmap, htimes,
    V, U, hPV, hcoreU, hVU, J, hJ, hsmooth⟩ := hprefix originalK hK
  refine ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst,
    hnative, hcoreTrans, W, hW, hproductW, τ, hτ, hhit, hmap, htimes,
    V, U, hPV, hcoreU, hVU, J, hJ, hsmooth, ?_⟩
  let Q := P.marked.tailoring.ribbon_marking parameterOne
  obtain ⟨S, hU⟩ := Q.exists_shrinkingData_into_fiber U (by
    change Q.embedding.map ⁻¹'
      (((P.marked.tailoring.embedding parameterOne).comp
        (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
          P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
        P.marked.tailoring.deformation.target.ribbonCompletion.core) ⊆ U
    rw [hcoreP]
    exact hcoreU)
  let F := (S.pair parameterOne).ribbonDomain.domain
  let O := P.marked.tailoring_ambient_marking
  let i := O.nativeEmbedding.comp O.domain.boundaryInclusion
  let g : ℝ × Q.manifold.Point → LGSpace n := fun p =>
    (G (τ (p.1, Q.embedding.map p.2)) (p.1, Q.embedding.map p.2)).2
  let hit : ℝ × S.extension → LGSpace n := fun p =>
    g (p.1, (S.fiberEmbedding Q parameterOne).map p.2)
  let time : ℝ × S.extension → ℝ := fun p =>
    τ (p.1, Q.embedding.map ((S.fiberEmbedding Q parameterOne).map p.2))
  have hh : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n)) ∞ hit ((V : Set ℝ) ×ˢ univ) :=
    S.contMDiffOn_shrunk_family Q U hU V (lgManifold n) g hsmooth
  have htimepre : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × S.extension =>
        (p.1, Q.embedding.map ((S.fiberEmbedding Q parameterOne).map p.2))) :=
    contMDiff_fst.prodMk
      (Q.embedding.map.contMDiff.comp
        ((S.fiberEmbedding Q parameterOne).map.contMDiff.comp contMDiff_snd))
  have ht : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, ℝ) ∞ time ((V : Set ℝ) ×ˢ univ) :=
    hτ.comp htimepre.contMDiffOn
      (fun p hp => hVU
        (p.1, (S.fiberEmbedding Q parameterOne).map p.2) ⟨hp.1, hU p.2⟩)
  have he (k : V) (x : S.extension) :
      (S.hittingEmbedding Q U hU V J k).map x = hit (k.val, x) :=
    hJ k ⟨(S.fiberEmbedding Q parameterOne).map x, hU x⟩
  have hrange (k : V) (x : S.extension) :
      (S.hittingEmbedding Q U hU V J k).map x ∈ range i.map := by
    rw [he]
    change hit (k.val, x) ∈ range
      (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
        P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map
    rw [hboundaryP]
    exact (hhit _ (hVU (k.val, (S.fiberEmbedding Q parameterOne).map x) ⟨k.property, hU x⟩)).2
  obtain ⟨j, hj, hjs, w, hw, hwpos, hwtime⟩ :=
    exists_native_boundary_hitting_witness F O.domain.boundary i V isCompact_Icc hPV
      (S.hittingEmbedding Q U hU V J) hit he hh hrange time ht
  exact ⟨S, hU, j, hj, hjs, w, hw, hwpos, hwtime⟩

end FsFltz
