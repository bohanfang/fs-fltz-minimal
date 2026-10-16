import FsFltz.Geometry.TailoringStrictJunction

/-!
# Finite-input assembly of the retained strict comparison through K=0

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1876–1924,
and `sec:assembly`, lines 2159–2233. The retained original prefix, intrinsic
shrinking, incoming identification, witness interpolation and completed
hitting family are concatenated with literal matching endpoint tuples.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

namespace PotentialTailoringOriginalMarkedPrefix
variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
  {β Cplus Aminus originalK K : ℝ} {m : RoundingChoice}

/-- The retained five-arrow prefix, actual two-arrow shrinking comparison,
and constructed three-arrow strict hitting suffix share literal endpoints. -/
def strictHittingChain (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (S : IntrinsicShrinkingData P.marked.tailoring.deformation.target) (x₀ : S.extension)
    (H : PairDeformation n) (J : StrictHittingJunction (S.pair parameterOne) H) :
    ComparisonChain P.original.pair H.target :=
  (P.chain.comp (S.chain x₀)).comp J.chain

@[simp] theorem strictHittingChain_length
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (S : IntrinsicShrinkingData P.marked.tailoring.deformation.target) (x₀ : S.extension)
    (H : PairDeformation n) (J : StrictHittingJunction (S.pair parameterOne) H) :
    (P.strictHittingChain S x₀ H J).length = 10 := by
  simp only [strictHittingChain, Quiver.Path.length_comp, P.chain_length,
    StrictHittingJunction.chain_length]
  rfl

end PotentialTailoringOriginalMarkedPrefix

variable {n : ℕ}
local instance strictRetainedLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance strictRetainedLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- Finite toric input constructs the literal comparison from the retained
original pair through intrinsic shrinking and the strict incoming junction
to the same completed zero-coefficient hitting endpoint. The same selected
potential's global Legendre data and native full-core equality are retained. -/
theorem ToricInput.exists_uniform_original_marked_prefix_strict_hitting_comparison
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
          ∃ (K : ℝ) (_hKpos : 0 < K), originalK ≤ K / Real.exp β ^ 2 ∧
          ∃ m : RoundingChoice,
            GeometricAdmissibleRounding I (Real.exp β) originalK
              (Cminus ^ 2 * β ^ 2 / 2) (Cplus ^ 2 * β ^ 2 / 2) m ∧
            ∃ P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus
              (Cminus ^ 2 * β ^ 2 / 2) originalK K m,
              range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map =
                  {z | φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
              ∃ S : IntrinsicShrinkingData P.marked.tailoring.deformation.target,
                ∃ x₀ : S.extension,
                  ∃ L : Parameter → LiouvilleStructure P.marked.tailoring_ambient_marking.domain,
                    (∀ t, (L t).primitive =
                      P.marked.tailoring_ambient_marking.domain.extension.pullback
                        (lgManifold n) P.marked.tailoring_ambient_marking.nativeEmbedding.map
                        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                          (tailoringFamily I β 1) (K * (1 - t.val)))) ∧
                    ∃ j : Parameter → (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding
                      P.marked.tailoring_ambient_marking.domain.boundary,
                      ∃ b : Parameter → P.marked.tailoring_ambient_marking.domain.boundary.Point → ℝ,
                        ∃ H : CompletedHittingRibbonFamily P.marked.tailoring_ambient_marking.domain
                          (S.pair parameterOne).ribbonDomain L j b,
                          ∃ J : StrictHittingJunction (S.pair parameterOne) H.deformation,
                            (P.strictHittingChain S x₀ H.deformation J).length = 10 ∧
                            ∀ t, (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                              P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map ''
                                (H.deformation.pair t).embeddedCore =
                                tailoringLegendreConic I φEnd ∩
                                  range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                    P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, hLegendre, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, hprefix⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_hitting_pairFamilies_with_legendre
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, hLegendre, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, ?_⟩
  intro β hβ
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β hβ
  refine ⟨hR, hset, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, _hcoreP, hboundaryP, hND, hOut, G, hG, _hfst,
    hnative, _hcoreTrans, W, _hW, _hproductW, τ, _hτ, hhit, _hmap, _htimes,
    V, U, hPV, _hcoreU, hVU, J, hJ, _hsmooth, S, hU, j, hj, _hjs,
    w, _hw, _hwpos, hwtime, _hweighted, L, hL, H, hcoreH⟩ := hprefix originalK hK
  let M := P.marked.tailoring.ribbon_marking parameterOne
  have hk : K ∈ Icc (0 : ℝ) K := ⟨hKpos.le, le_rfl⟩
  let v : V := ⟨K, hPV hk⟩
  let τF : S.extension → ℝ := fun x => τ (K, M.embedding.map ((S.fiberEmbedding M parameterOne).map x))
  have hL₀ : (L parameterZero).primitive =
      P.marked.tailoring_ambient_marking.domain.extension.pullback (lgManifold n)
        P.marked.tailoring_ambient_marking.nativeEmbedding.map
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K) := by
    simpa only [parameterZero, sub_zero, mul_one] using hL parameterZero
  have htime : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier, 0 < τF x := by
    intro x _
    exact (hhit _ (hVU (K, (S.fiberEmbedding M parameterOne).map x) ⟨v.property, hU x⟩)).1
  have hhitF : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
      (G (τF x) (K, M.embedding.map ((S.fiberEmbedding M parameterOne).map x))).2 =
      (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
        P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map ((j v).map x) := by
    intro x _
    rw [hj v x]
    exact (hJ v ⟨(S.fiberEmbedding M parameterOne).map x, hU x⟩).symm
  have hwF : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
      w (K, (j v).map x) = Real.exp (-τF x) := hwtime K hk
  obtain ⟨junction⟩ := P.marked.exists_strictJunction_into_retained_hitting hφ S H hL₀ hboundaryP
    (hND K hKpos.le) (hOut K hKpos.le) G hG (hnative K hk) τF htime
    (by simpa only [decreasingHittingParameter_zero] using hhitF)
    (by simpa only [decreasingHittingParameter, parameterZero, sub_zero, mul_one] using hwF)
  obtain ⟨x, hx⟩ := P.marked.tailoring.ribbon_nonempty parameterOne
  let x₀ : S.extension := ⟨x, S.contains_carrier hx⟩
  exact ⟨K, hKpos, hKL, m, hm, P, hboundaryP, S, x₀, L, hL, _, _, H,
    junction, P.strictHittingChain_length S x₀ H.deformation junction, hcoreH⟩

end FsFltz
