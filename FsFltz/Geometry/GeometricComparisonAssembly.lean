import FsFltz.Geometry.OriginalNormalizedGradingJunction
import FsFltz.Geometry.TailoringStrictJunctionGradingAlignment
import FsFltz.Geometry.TailoringCotangentCompletedGrading

/-!
# Finite-input assembly of the prescribed graded geometric comparison

Source: `geoemtric-part-fsf.tex`, `thm:target`, lines 352–435;
`geometric-part-fsf-proof.tex`, `sec:assembly`, lines 2091–2233.
The same retained prefix, shrinking, strict junction, hitting family and
cotangent identification carry both the full core and prescribed grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- The finite toric data construct a graded convenient comparison without
assuming any geometric chain or any grading transport as input. -/
theorem ToricInput.exists_uniform_graded_convenient_comparison {n : ℕ} (I : ToricInput n) :
    ∃ φ : RealSpace n → ℝ, ∃ Aamb Cminus Cplus β₀ : ℝ,
      AmbientEndBound I Aamb ∧ 0 < Cminus ∧ Cminus < Cplus ∧ 0 < β₀ ∧
      ∀ β ≥ β₀,
        max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β ∧
        RatioSetWellDefined I (Real.exp β) ∧
        (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp β) Afib ∧
          Afib < Cminus ^ 2 * β ^ 2 / 2) ∧
        ∀ originalK : ℝ, K0 I (Real.exp β) ≤ originalK →
          ∃ K : ℝ, ∃ m : RoundingChoice,
            ∃ P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus
              (Cminus ^ 2 * β ^ 2 / 2) originalK K m,
              ∃ E : CotangentPairData n, ∃ chain : ComparisonChain P.original.pair E.pair,
                chain.length = 11 ∧ E.embeddedCore = fltzLink I ∧
                Nonempty (GradedComparisonChain P.original.pair chain P.originalMaslov E.verticalMaslov) := by
  obtain ⟨φEnd, φ, hstrong, _hEnd1, _hφ, ⟨Dφ⟩, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, hprefix⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_hitting_pairFamilies_with_legendre
  obtain ⟨A₀, hA₀, hendpoint⟩ := Dφ.exists_endpoint_level_threshold hstrong
  obtain ⟨_d, _hd, _R, _hR, Bgrade, _hBgrade, hπall⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I Dφ.smooth
      Dφ.lower_pos Dφ.upper_pos Dφ.hessian_lower Dφ.hessian_upper
  let Bnew := max B (max Bgrade (max 1 (2 * A₀ / Cplus ^ 2)))
  refine ⟨φ, Aamb, Cminus, Cplus, Bnew, hamb, hCminus, hCminusCplus,
    hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβgrade : Bgrade ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβend : max 1 (2 * A₀ / Cplus ^ 2) ≤ β :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβend
  have hβA : 2 * A₀ / Cplus ^ 2 ≤ β := (le_max_right _ _).trans hβend
  have hCplus : 0 < Cplus := hCminus.trans hCminusCplus
  have hCsq : 0 < Cplus ^ 2 := sq_pos_of_pos hCplus
  have hβsq : β ≤ β ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hβsq hCsq.le
  have hquot := (div_le_iff₀ hCsq).mp hβA
  have hlevel : A₀ ≤ Cplus ^ 2 * β ^ 2 / 2 := by nlinarith
  obtain ⟨hlevels, hgradient, hout⟩ := hendpoint _ hlevel
  have hA : 0 < Cplus ^ 2 * β ^ 2 / 2 := hA₀.trans_le hlevel
  have hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound Dφ.smooth Dφ.lower_pos Dφ.hessian_lower y) :=
    fun s hs y => (hπall β hβgrade s hs y _).1
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β hβB
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
  let O := P.marked.tailoring_ambient_marking
  obtain ⟨fTail, hfTail, gTail, ⟨gP⟩⟩ :=
    P.exists_graded_chain_with_tailoring_formula Dφ.smooth Dφ.lower_pos Dφ.hessian_lower hπ hKpos.le
  obtain ⟨fHit, ⟨gHit⟩, _hfHitJ, hfHit⟩ := H.exists_completedGrading_of_native_with_formula
    I Dφ.smooth Dφ.lower_pos Dφ.hessian_lower β K hKpos.le
    (hπ 1 parameterOne.property) O.nativeEmbedding hL
  have hD : O.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := P.marked.tailoring.ambient_nonempty parameterOne
    have hy := mem_image_of_mem (P.marked.tailoring.embedding parameterOne).map hx
    rw [P.marked.tailoring.ambient_image parameterOne] at hy
    have hside := (tailoringRoundedDomain_subset I φ β 1
      (Cplus ^ 2 * β ^ 2 / 2) (Real.exp_pos β) m hy).1
    have hmem : (P.marked.tailoring.embedding parameterOne).map x ∈
        O.nativeEmbedding.map '' O.domain.carrier := by
      rw [O.native_image]
      exact sub_nonpos.mpr hside
    obtain ⟨z, hz, _⟩ := hmem
    exact ⟨z, hz⟩
  obtain ⟨E, C, hfltz, ⟨gC⟩⟩ := H.exists_graded_cotangentEndpoint_of_hitting_family Dφ hstrong
    hA hlevels hgradient hout O hD hboundaryP β K hKpos.le
    (hπ 1 parameterOne.property) hL fHit hfHit (hcoreH parameterOne)
  obtain ⟨junction, ⟨gJ⟩⟩ := P.marked.exists_graded_strictJunction_of_completed_native_families
    Dφ.smooth Dφ.lower_pos Dφ.hessian_lower hπ hKpos.le S H hL hboundaryP
    (hND K hKpos.le) (hOut K hKpos.le) G hG (hnative K hk) τF htime
    (by simpa only [decreasingHittingParameter_zero] using hhitF)
    (by simpa only [decreasingHittingParameter, parameterZero, sub_zero, mul_one] using hwF)
    fTail hfTail fHit hfHit gHit
  obtain ⟨x, hx⟩ := P.marked.tailoring.ribbon_nonempty parameterOne
  let x₀ : S.extension := ⟨x, S.contains_carrier hx⟩
  let chain := (P.strictHittingChain S x₀ H.deformation junction).cons (.identification C)
  refine ⟨K, m, P, E, chain, ?_, hfltz, ?_⟩
  · simp [chain]
  · exact ⟨((gP.comp (S.grading x₀ _)).comp gJ).cons (.identification gC)⟩

/-- Every supplied initial pair reaches the prescribed vertical cotangent
endpoint along one finite graded chain, with literal full-core equality. -/
theorem ToricInput.exists_arbitrary_initial_endpointComparison {n : ℕ}
    (I : ToricInput n) :
    ∃ Aamb R0 : ℝ, AmbientEndBound I Aamb ∧
      max 1 (sublevelMagnitudeSup I Aamb) < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        RatioSetWellDefined I R ∧ (∃ Afib : ℝ, FiberEndBound I Aamb R Afib) ∧
        ∀ Afib : ℝ, FiberEndBound I Aamb R Afib →
          ∀ K : ℝ, K0 I R ≤ K →
            ∀ Aminus A : ℝ, Afib < Aminus →
              ∀ m : RoundingChoice, ∀ initial : InitialPairData I R K Aminus A m,
                ∃ comparison : EndpointComparison initial, comparison.chain.length = 14 := by
  obtain ⟨φ, Aamb, Cminus, Cplus, β₀, hamb, _hCminus, _hCminusCplus, _hβ₀, hall⟩ :=
    I.exists_uniform_graded_convenient_comparison
  refine ⟨Aamb, Real.exp β₀, hamb, (hall β₀ le_rfl).1, ?_⟩
  intro R hR
  have hRpos : 0 < R := (Real.exp_pos β₀).trans_le hR
  have hβ : β₀ ≤ Real.log R := (Real.le_log_iff_exp_le hRpos).mpr hR
  obtain ⟨hlarge, hset, ⟨Afib', hfib', hAfib'⟩, hprefix⟩ := hall (Real.log R) hβ
  have hlocal :
      RatioSetWellDefined I (Real.exp (Real.log R)) ∧
      (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp (Real.log R)) Afib) ∧
      ∀ Afib : ℝ, FiberEndBound I Aamb (Real.exp (Real.log R)) Afib →
        ∀ K : ℝ, K0 I (Real.exp (Real.log R)) ≤ K →
          ∀ Aminus A : ℝ, Afib < Aminus →
            ∀ m : RoundingChoice,
              ∀ initial : InitialPairData I (Real.exp (Real.log R)) K Aminus A m,
                ∃ comparison : EndpointComparison initial, comparison.chain.length = 14 := by
    refine ⟨hset, ⟨Afib', hfib'⟩, ?_⟩
    intro Afib hfib K hK Aminus A hAminus m initial
    obtain ⟨K', m', P, E, chain, hlength, hfltz, ⟨gchain⟩⟩ := hprefix K hK
    obtain ⟨D, hD, hdatum, _hfour, _gfour, _height, _hpath⟩ :=
      P.exists_arbitrary_source_chain hamb hlarge hset hK hfib hfib' hAminus hAfib' initial
    have gD : GradedComparisonChain initial.pair D.chain D.sourceDatum P.originalMaslov := by
      rw [← hdatum]
      exact D.graded
    let comparison : EndpointComparison initial := {
      endpoint := E
      chain := D.chain.comp chain
      core_eq := hfltz
      sourceDatum := D.sourceDatum
      source_prescribed := D.source_prescribed
      endpointDatum := E.verticalMaslov
      graded := gD.comp gchain
      verticalDatum := E.verticalMaslov
      vertical_prescribed := E.verticalMaslov_prescribed
      endpoint_homotopy := MaslovHomotopy.refl E.verticalMaslov }
    refine ⟨comparison, ?_⟩
    change (D.chain.comp chain).length = 14
    simp only [Quiver.Path.length_comp, hD, hlength]
  erw [Real.exp_log hRpos] at hlocal
  exact hlocal

/-- The geometric target for one finite toric input, with all original
parameter ranges and every admissible initial choice. -/
theorem ToricInput.geometricTargetFor {n : ℕ} (I : ToricInput n) : GeometricTargetFor I := by
  obtain ⟨Aamb, R0, hamb, hR0, hall⟩ := I.exists_arbitrary_initial_endpointComparison
  refine ⟨I.allNonnegativeComplete, Aamb, R0, hamb, hR0, ?_⟩
  intro R hR
  obtain ⟨hset, hfib, hcomparison⟩ := hall R hR
  refine ⟨⟨hset.1, hset.2, hfib⟩, ?_⟩
  intro Afib hAfib K hK Aminus A hAminus hA
  refine ⟨exists_original_admissible_rounding I hamb (hR0.trans_le hR)
    hset hK hAfib hAminus hA, ?_⟩
  intro m hm
  obtain ⟨initial⟩ := nonempty_originalInitialPairData I hamb (hR0.trans_le hR)
    hset hK hAfib hAminus m hm
  obtain ⟨comparison, _⟩ := hcomparison Afib hAfib K hK Aminus A hAminus m initial
  exact ⟨initial, ⟨comparison⟩⟩

/-- The geometric FS–FLTZ theorem. The general categorical GPS deduction
remains the separate external interface. -/
theorem geometricTarget : GeometricTarget := fun _ I => I.geometricTargetFor

end FsFltz
