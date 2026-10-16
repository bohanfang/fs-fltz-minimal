import FsFltz.Geometry.TailoringHittingRibbonMarking
import FsFltz.Geometry.TailoringHittingCore

/-!
# Actual completed pair families for the same retained hitting ribbon

Source: `geoemtric-part-fsf.tex`, `thm:target`, lines 352–435, and
`sec:lean`, lines 766–836; `geometric-part-fsf-proof.tex`,
`eq:hittingprimitive` and `eq:ribbonprimitive`, lines 1818–1875.
Finite toric input constructs the actual completed pair family on the same
marked outer domain, using the same original prefix, native action and finite
intrinsic shrinking, with the original full-fiber marking retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance retainedHittingRibbonFamilyCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance retainedHittingRibbonFamilySmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- Finite toric input constructs the actual completed decreasing-coefficient
hitting family on the same native outer domain and same full ribbon shrink. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hitting_pairFamilies_with_legendre
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      Nonempty (RetainedLegendrePotential φEnd φ) ∧
      ∃ Aamb Cminus Cplus β₀ : ℝ, AmbientEndBound I Aamb ∧
        0 < Cminus ∧ Cminus < Cplus ∧ 0 < β₀ ∧ ∀ β ≥ β₀,
        max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β ∧
        RatioSetWellDefined I (Real.exp β) ∧
        (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp β) Afib ∧
          Afib < Cminus ^ 2 * β ^ 2 / 2) ∧
        ∀ originalK : ℝ, K0 I (Real.exp β) ≤ originalK →
          ∃ (K : ℝ) (hKpos : 0 < K), originalK ≤ K / Real.exp β ^ 2 ∧
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
              (∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
                (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β 1) k)) y) ∧
              (∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
                φ y.1 = Cplus ^ 2 * β ^ 2 / 2 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y)) ∧
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
                              (∀ k (hk : k ∈ Icc (0 : ℝ) K),
                                ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
                                  w (k, (j ⟨k, hPV hk⟩).map x) =
                                    Real.exp (-τ (k, Q.embedding.map
                                      ((S.fiberEmbedding Q parameterOne).map x)))) ∧
                              (∀ k (hk : k ∈ Icc (0 : ℝ) K),
                                ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
                                  (S.pair parameterOne).ribbonDomain.domain.extension.pullback
                                    P.marked.tailoring_ambient_marking.domain.boundary
                                    (j ⟨k, hPV hk⟩).map
                                    (fun y => w (k, y) •
                                      P.marked.tailoring_ambient_marking.domain.boundaryForm
                                        (P.marked.tailoring_ambient_marking.domain.extension.pullback
                                          (lgManifold n)
                                          P.marked.tailoring_ambient_marking.nativeEmbedding.map
                                          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                                            (tailoringFamily I β 1) k)) y) x =
                                    (S.pair parameterOne).ribbonDomain.liouville.primitive x) ∧
                              ∃ L : Parameter → LiouvilleStructure
                                P.marked.tailoring_ambient_marking.domain,
                                (∀ t, (L t).primitive =
                                  P.marked.tailoring_ambient_marking.domain.extension.pullback
                                    (lgManifold n) P.marked.tailoring_ambient_marking.nativeEmbedding.map
                                    ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                                      (tailoringFamily I β 1) (K * (1 - t.val)))) ∧
                                ∃ H : CompletedHittingRibbonFamily
                                  P.marked.tailoring_ambient_marking.domain
                                  (S.pair parameterOne).ribbonDomain L
                                  (fun t => j ⟨(decreasingHittingParameter K hKpos.le t).val,
                                    hPV (decreasingHittingParameter K hKpos.le t).property⟩)
                                  (fun t y => w (K * (1 - t.val), y)),
                                  ∀ t, (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                    P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map ''
                                      (H.deformation.pair t).embeddedCore =
                                    tailoringLegendreConic I φEnd ∩
                                      range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                        P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, hLegendre, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, hprefix⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_hitting_ribbons_with_legendre
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, hLegendre, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, ?_⟩
  intro β hβ
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β hβ
  refine ⟨hR, hset, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, hND, hOut, G, hG, hfst,
    hnative, hcoreTrans, W, hW, hproductW, τ, hτ, hhit, hmap, htimes,
    V, U, hPV, hcoreU, hVU, J, hJ, hsmooth, S, hU, j, hj, hjs,
    w, hw, hwpos, hwtime, hweighted⟩ := hprefix originalK hK
  refine ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, hND, hOut, G, hG, hfst,
    hnative, hcoreTrans, W, hW, hproductW, τ, hτ, hhit, hmap, htimes,
    V, U, hPV, hcoreU, hVU, J, hJ, hsmooth, S, hU, j, hj, hjs,
    w, hw, hwpos, hwtime, hweighted, ?_⟩
  obtain ⟨L, hL, ⟨H⟩⟩ := P.marked.tailoring_ambient_marking.exists_completed_hitting_ribbon_family
    I hφ β (Cplus ^ 2 * β ^ 2 / 2) K hKpos.le hboundaryP
    (fun k hk => hND k hk.1) (fun k hk => hOut k hk.1)
    (S.pair parameterOne).ribbonDomain V hPV j hjs w hw hwpos hweighted
  refine ⟨L, hL, H, ?_⟩
  intro t
  let k := decreasingHittingParameter K hKpos.le t
  let v : V := ⟨k.val, hPV k.property⟩
  let Q := P.marked.tailoring.ribbon_marking parameterOne
  let g : LGSpace n → LGSpace n := fun y => (G (τ (k.val, y)) (k.val, y)).2
  have hcoreHit := S.hittingEmbedding_core_image Q U hU V J v g (hJ v)
  calc
    _ = (S.hittingEmbedding Q U hU V J v).map ''
        (S.pair parameterOne).ribbonCompletion.core := by
      rw [H.embeddedCore (S.pair parameterOne).ribbonCompletion t, ← image_comp]
      apply image_congr
      intro x _
      exact hj v x
    _ = g '' (_ '' P.marked.tailoring.deformation.target.ribbonCompletion.core) := hcoreHit
    _ = _ := (congrArg (fun C => g '' C) hcoreP).trans
      (htimes k.val k.property).2.2.image_eq

/-- The established interface retains the same witnesses by projection. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hitting_pairFamilies
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
          ∃ (K : ℝ) (hKpos : 0 < K), originalK ≤ K / Real.exp β ^ 2 ∧
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
              (∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
                (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β 1) k)) y) ∧
              (∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
                φ y.1 = Cplus ^ 2 * β ^ 2 / 2 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y)) ∧
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
                              (∀ k (hk : k ∈ Icc (0 : ℝ) K),
                                ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
                                  w (k, (j ⟨k, hPV hk⟩).map x) =
                                    Real.exp (-τ (k, Q.embedding.map
                                      ((S.fiberEmbedding Q parameterOne).map x)))) ∧
                              (∀ k (hk : k ∈ Icc (0 : ℝ) K),
                                ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
                                  (S.pair parameterOne).ribbonDomain.domain.extension.pullback
                                    P.marked.tailoring_ambient_marking.domain.boundary
                                    (j ⟨k, hPV hk⟩).map
                                    (fun y => w (k, y) •
                                      P.marked.tailoring_ambient_marking.domain.boundaryForm
                                        (P.marked.tailoring_ambient_marking.domain.extension.pullback
                                          (lgManifold n)
                                          P.marked.tailoring_ambient_marking.nativeEmbedding.map
                                          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                                            (tailoringFamily I β 1) k)) y) x =
                                    (S.pair parameterOne).ribbonDomain.liouville.primitive x) ∧
                              ∃ L : Parameter → LiouvilleStructure
                                P.marked.tailoring_ambient_marking.domain,
                                (∀ t, (L t).primitive =
                                  P.marked.tailoring_ambient_marking.domain.extension.pullback
                                    (lgManifold n) P.marked.tailoring_ambient_marking.nativeEmbedding.map
                                    ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                                      (tailoringFamily I β 1) (K * (1 - t.val)))) ∧
                                ∃ H : CompletedHittingRibbonFamily
                                  P.marked.tailoring_ambient_marking.domain
                                  (S.pair parameterOne).ribbonDomain L
                                  (fun t => j ⟨(decreasingHittingParameter K hKpos.le t).val,
                                    hPV (decreasingHittingParameter K hKpos.le t).property⟩)
                                  (fun t y => w (K * (1 - t.val), y)),
                                  ∀ t, (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                    P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map ''
                                      (H.deformation.pair t).embeddedCore =
                                    tailoringLegendreConic I φEnd ∩
                                      range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                        P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, _hLegendre, rest⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_hitting_pairFamilies_with_legendre
  exact ⟨φEnd, φ, hstrong, hEnd1, hφ, rest⟩

end FsFltz
