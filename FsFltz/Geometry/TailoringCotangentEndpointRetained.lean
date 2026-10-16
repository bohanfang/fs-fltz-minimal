import FsFltz.Geometry.TailoringCotangentEndpointRetainedNative
import FsFltz.Geometry.TailoringStrictJunctionRetained

/-!
# The cotangent endpoint of the same retained strict comparison

Source: `geometric-part-fsf-proof.tex`, `prop:endpoint`, lines 1922–1959,
and `sec:assembly`, lines 2091–2191. The endpoint uses the same selected
potential, outer compact domain, finite shrinking and completed hitting family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance retainedCotangentCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance retainedCotangentSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- Localization retains the exact native outer carrier and primitive,
so the constructed native zero marking applies to this selected hitting slice. -/
theorem CompletedHittingRibbonFamily.exists_retained_cotangentEndpoint_with_compact
    {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
    (Dφ : RetainedLegendrePotential φEnd φ)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    {A : ℝ} (hA : 0 < A)
    (hlevelEq : {y : LGSpace n | φ y.1 = A} = {y : LGSpace n | φEnd y.1 = A})
    (hgradient : ∀ u, φ u = A → coordinateGradient φ u = coordinateGradient φEnd u)
    (hout : ∀ y : LGSpace n, A ≤ φ y.1 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y))
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {α : Parameter → (lgManifold n).Form 1}
    (O : OuterAmbientInclusionMarkingFamily Q J (fun y => φ y.1 - A) α)
    (hD : O.domain.carrier.Nonempty)
    (hboundary : range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map =
      {y | φ y.1 = A})
    {F : LiouvilleDomain (2 * n - 2)} {L : Parameter → LiouvilleStructure O.domain}
    {j : Parameter → F.domain.extension.SmoothEmbedding O.domain.boundary}
    {b : Parameter → O.domain.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily O.domain F L j b)
    (hzero : (L parameterOne).primitive = O.domain.extension.pullback (lgManifold n)
      O.nativeEmbedding.map (lambdaPotentialForm φ))
    (hcore : (O.nativeEmbedding.comp O.domain.boundaryInclusion).map '' H.deformation.target.embeddedCore =
      tailoringLegendreConic I φEnd ∩ range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map) :
    ∃ q : H.deformation.target.ambientManifold.SmoothEquiv (lgManifold n),
      H.deformation.target.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
        H.deformation.target.ambientCompletion.ambient.primitive ∧
      (∀ x ∈ H.deformation.target.ambientDomain.domain.carrier,
        q (H.deformation.target.ambientCompletion.inclusion.map x) =
          (O.nativeEmbedding.comp (H.ambient.collars parameterOne).originalInclusion).map x) ∧
      ∃ E : CotangentPairData n, ∃ C : CompletionIdentification H.deformation.target E.pair,
        (∀ y, E.marking (C.ambientEquiv y) = ((q y).2, coordinateGradient φ (q y).1)) ∧
        E.pair.ribbonDomain = H.deformation.target.ribbonDomain ∧
        HEq E.pair.ribbonCompletion H.deformation.target.ribbonCompletion ∧
        HEq C.ribbonEquiv.map (id : H.deformation.target.ribbonDomain.domain.extension.Point →
          H.deformation.target.ribbonDomain.domain.extension.Point) ∧ C.scale = 1 ∧
        (∀ x, E.boundaryCoordinates (C.boundaryEquiv x) =
          tailoringRadialProjection φEnd ((O.nativeEmbedding.comp O.domain.boundaryInclusion).map x)) ∧
        (∀ x, E.pair.witness (C.boundaryEquiv x) =
          Real.sqrt (realSquaredNorm (coordinateGradient φEnd
            ((O.nativeEmbedding.comp O.domain.boundaryInclusion).map x).1)) * H.deformation.target.witness x) ∧
        E.embeddedCore = fltzLink I := by
  let B := H.ambient.collars parameterOne
  let e := O.nativeEmbedding.comp B.originalInclusion
  have hP : H.deformation.target.ambientDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hD
    let z := B.cylindricalCompactHomeomorph.symm ⟨x, hx⟩
    exact ⟨z.val, z.property⟩
  have himage : e.map '' H.deformation.target.ambientDomain.domain.carrier =
      {y : LGSpace n | φ y.1 ≤ A} := by
    change (O.nativeEmbedding.map ∘ B.originalInclusion.map) '' B.localizedDomain.domain.carrier = _
    rw [image_comp, B.image_originalInclusion_carrier, O.native_image]
    ext y
    change φ y.1 - A ≤ 0 ↔ φ y.1 ≤ A
    exact sub_nonpos
  have hp : ∀ x ∈ H.deformation.target.ambientDomain.domain.carrier,
      H.deformation.target.ambientDomain.liouville.primitive x =
        H.deformation.target.ambientDomain.domain.extension.pullback (lgManifold n)
          e.map (lambdaPotentialForm φ) x := by
    intro x _
    change B.localizedDomain.liouville.primitive x =
      B.localizedDomain.domain.extension.pullback (lgManifold n)
        (O.nativeEmbedding.map ∘ B.originalInclusion.map) (lambdaPotentialForm φ) x
    rw [B.localizedDomain.domain.extension.pullback_comp O.domain.extension (lgManifold n)
      (B.originalInclusion.map.contMDiff.mdifferentiable (by simp))
      (O.nativeEmbedding.map.contMDiff.mdifferentiable (by simp)), ← hzero,
      B.pullback_originalInclusion, B.original_primitive]
  have he : (e.comp H.deformation.target.ambientDomain.domain.boundaryInclusion).map =
      (O.nativeEmbedding.comp O.domain.boundaryInclusion).map := rfl
  obtain ⟨q, hq, hc, E, C, hmap, hribbon, hcompletion, hid, hscale, hb, hw, hfltz⟩ :=
    Dφ.exists_literal_cotangentEndpoint hstrong hA hlevelEq hgradient hout
      H.deformation.target hP e himage hp (by rw [he]; exact hboundary)
      (by rw [he]; exact hcore)
  refine ⟨q, hq, ?_, E, C, hmap, hribbon, hcompletion, hid, hscale, ?_, ?_, hfltz⟩
  · exact hc
  · exact hb
  · exact hw

/-- Boundary-facing projection of the full retained compact marking. -/
theorem CompletedHittingRibbonFamily.exists_retained_cotangentEndpoint
    {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
    (Dφ : RetainedLegendrePotential φEnd φ)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    {A : ℝ} (hA : 0 < A)
    (hlevelEq : {y : LGSpace n | φ y.1 = A} = {y : LGSpace n | φEnd y.1 = A})
    (hgradient : ∀ u, φ u = A → coordinateGradient φ u = coordinateGradient φEnd u)
    (hout : ∀ y : LGSpace n, A ≤ φ y.1 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y))
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {α : Parameter → (lgManifold n).Form 1}
    (O : OuterAmbientInclusionMarkingFamily Q J (fun y => φ y.1 - A) α)
    (hD : O.domain.carrier.Nonempty)
    (hboundary : range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map =
      {y | φ y.1 = A})
    {F : LiouvilleDomain (2 * n - 2)} {L : Parameter → LiouvilleStructure O.domain}
    {j : Parameter → F.domain.extension.SmoothEmbedding O.domain.boundary}
    {b : Parameter → O.domain.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily O.domain F L j b)
    (hzero : (L parameterOne).primitive = O.domain.extension.pullback (lgManifold n)
      O.nativeEmbedding.map (lambdaPotentialForm φ))
    (hcore : (O.nativeEmbedding.comp O.domain.boundaryInclusion).map '' H.deformation.target.embeddedCore =
      tailoringLegendreConic I φEnd ∩ range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map) :
    ∃ q : H.deformation.target.ambientManifold.SmoothEquiv (lgManifold n),
      H.deformation.target.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
        H.deformation.target.ambientCompletion.ambient.primitive ∧
      (∀ x, q (H.deformation.target.ambientCompletion.inclusion.map
        (H.deformation.target.ambientDomain.domain.boundaryInclusion.map x)) =
          (O.nativeEmbedding.comp O.domain.boundaryInclusion).map x) ∧
      ∃ E : CotangentPairData n, ∃ C : CompletionIdentification H.deformation.target E.pair,
        (∀ y, E.marking (C.ambientEquiv y) = ((q y).2, coordinateGradient φ (q y).1)) ∧
        E.pair.ribbonDomain = H.deformation.target.ribbonDomain ∧
        HEq E.pair.ribbonCompletion H.deformation.target.ribbonCompletion ∧
        HEq C.ribbonEquiv.map (id : H.deformation.target.ribbonDomain.domain.extension.Point →
          H.deformation.target.ribbonDomain.domain.extension.Point) ∧ C.scale = 1 ∧
        (∀ x, E.boundaryCoordinates (C.boundaryEquiv x) =
          tailoringRadialProjection φEnd ((O.nativeEmbedding.comp O.domain.boundaryInclusion).map x)) ∧
        (∀ x, E.pair.witness (C.boundaryEquiv x) =
          Real.sqrt (realSquaredNorm (coordinateGradient φEnd
            ((O.nativeEmbedding.comp O.domain.boundaryInclusion).map x).1)) * H.deformation.target.witness x) ∧
        E.embeddedCore = fltzLink I := by
  obtain ⟨q, hq, hc, rest⟩ := H.exists_retained_cotangentEndpoint_with_compact
    Dφ hstrong hA hlevelEq hgradient hout O hD hboundary hzero hcore
  exact ⟨q, hq, fun x => hc _
    (H.deformation.target.ambientDomain.domain.boundaryInclusion_mem_carrier x), rest⟩

/-- Finite toric input constructs one selected retained comparison and its
actual scale-one cotangent endpoint, with literal entire FLTZ core equality.
The terminal arrow is appended to that same ten-arrow strict comparison. -/
theorem ToricInput.exists_uniform_original_marked_prefix_strict_cotangent_comparison
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
                            (∀ t, (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                              P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map ''
                                (H.deformation.pair t).embeddedCore =
                                tailoringLegendreConic I φEnd ∩
                                  range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                    P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map) ∧
                            ∃ q : H.deformation.target.ambientManifold.SmoothEquiv (lgManifold n),
                              H.deformation.target.ambientManifold.pullback (lgManifold n) q
                                (lambdaPotentialForm φ) = H.deformation.target.ambientCompletion.ambient.primitive ∧
                              (∀ x, q (H.deformation.target.ambientCompletion.inclusion.map
                                (H.deformation.target.ambientDomain.domain.boundaryInclusion.map x)) =
                                  (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                    P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map x) ∧
                              ∃ E : CotangentPairData n,
                                ∃ C : CompletionIdentification H.deformation.target E.pair,
                                  (∀ y, E.marking (C.ambientEquiv y) = ((q y).2, coordinateGradient φ (q y).1)) ∧
                                  E.pair.ribbonDomain = H.deformation.target.ribbonDomain ∧
                                  HEq E.pair.ribbonCompletion H.deformation.target.ribbonCompletion ∧
                                  HEq C.ribbonEquiv.map
                                    (id : H.deformation.target.ribbonDomain.domain.extension.Point →
                                      H.deformation.target.ribbonDomain.domain.extension.Point) ∧ C.scale = 1 ∧
                                  (∀ x, E.boundaryCoordinates (C.boundaryEquiv x) =
                                    tailoringRadialProjection φEnd
                                      ((P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                        P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map x)) ∧
                                  (∀ x, E.pair.witness (C.boundaryEquiv x) =
                                    Real.sqrt (realSquaredNorm (coordinateGradient φEnd
                                      ((P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                                        P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map x).1)) *
                                      H.deformation.target.witness x) ∧
                                  E.embeddedCore = fltzLink I ∧
                                  ((P.strictHittingChain S x₀ H.deformation J).cons
                                    (ComparisonStep.identification C)).length = 11 := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, ⟨Dφ⟩, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, hprefix⟩ :=
    I.exists_uniform_original_marked_prefix_strict_hitting_comparison
  obtain ⟨A₀, hA₀, hendpoint⟩ := Dφ.exists_endpoint_level_threshold hstrong
  let Bnew := max B (max 1 (2 * A₀ / Cplus ^ 2))
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, ⟨Dφ⟩, Aamb, Cminus, Cplus, Bnew,
    hamb, hCminus, hCminusCplus, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβA : 2 * A₀ / Cplus ^ 2 ≤ β :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hCplus : 0 < Cplus := hCminus.trans hCminusCplus
  have hCsq : 0 < Cplus ^ 2 := sq_pos_of_pos hCplus
  have hβsq : β ≤ β ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hβsq hCsq.le
  have hquot := (div_le_iff₀ hCsq).mp hβA
  have hlevel : A₀ ≤ Cplus ^ 2 * β ^ 2 / 2 := by nlinarith
  obtain ⟨hlevels, hgradient, hout⟩ := hendpoint _ hlevel
  have hA : 0 < Cplus ^ 2 * β ^ 2 / 2 := hA₀.trans_le hlevel
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β hβB
  refine ⟨hR, hset, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, hboundary, S, x₀, L, hL, j, b, H, J,
    hlength, hcore⟩ := hprefix originalK hK
  let O := P.marked.tailoring_ambient_marking
  have hzero : (L parameterOne).primitive = O.domain.extension.pullback (lgManifold n)
      O.nativeEmbedding.map (lambdaPotentialForm φ) := by
    simpa only [parameterOne, sub_self, mul_zero, SmoothManifold.rankTwoPrimitive,
      zero_smul, add_zero] using hL parameterOne
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
  obtain ⟨q, hq, hbq, E, C, hmap, hribbon, hcompletion, hid, hscale, hb, hw, hfltz⟩ :=
    H.exists_retained_cotangentEndpoint Dφ hstrong hA hlevels hgradient hout O hD
      hboundary hzero (hcore parameterOne)
  refine ⟨K, hKpos, hKL, m, hm, P, hboundary, S, x₀, L, hL, j, b, H, J,
    hlength, hcore, q, hq, hbq, E, C, hmap, hribbon, hcompletion, hid, hscale,
    hb, hw, hfltz, ?_⟩
  simp only [Quiver.Path.length_cons, hlength]

end FsFltz
