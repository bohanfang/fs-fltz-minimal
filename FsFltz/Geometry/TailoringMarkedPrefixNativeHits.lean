import FsFltz.Geometry.TailoringMarkedPrefixCore
import FsFltz.Geometry.TailoringMarkedOuterBoundary
import FsFltz.Geometry.TailoringOuterBoundaryHittingNative
import FsFltz.Geometry.TailoringCotangentEndpointRetainedPotential

/-!
# One retained marked prefix and its native outer hitting maps

Source: `geoemtric-part-fsf.tex`, `thm:target`, lines 352–435, and
`sec:lean`, lines 766–836; `geometric-part-fsf-proof.tex`, `prop:band`,
lines 1778–1817. Finite toric input chooses the potentials once, then
chooses one common outer radius for the actual marked prefix and the
native outer-boundary comparison. The full-core and marked-boundary
equalities belong to that same retained prefix. Smooth hitting data is
asserted on its proved open logarithmic-coordinate neighborhoods.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology ContDiff Manifold

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance markedPrefixNativeHitsChartedSpace :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance markedPrefixNativeHitsIsManifold :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- Finite input constructs the actual retained marked prefix, its full
embedded core, its literal marked outer boundary, and the native outer
bijection with the same potential and radius throughout. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hits_with_legendre
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      Nonempty (RetainedLegendrePotential φEnd φ) ∧
      ∃ c U : ℝ, 0 < c ∧ 0 < U ∧
      (∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
        inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) ∧
      (∀ u v : EuclideanSpace ℝ (Fin n),
        inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) ∧
      (∃ L > 0, ∀ u, L ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) ∧
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
                ∀ k ∈ Icc (0 : ℝ) K, ∃ τ : LGSpace n → ℝ,
                  (∀ y ∈ tailoringCoreSection I φEnd β,
                    0 < τ y ∧ φ (G (τ y) (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 ∧
                    (∀ s, φ (G s (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 → s = τ y) ∧
                    ∀ s ∈ Icc (0 : ℝ) (τ y), (G s (k, y)).2 ∈ tailoringLegendreConic I φEnd ∧
                      1 ≤ (tailoringFamily I β 1 (G s (k, y)).2).re) ∧
                  BijOn (fun y => (G (τ y) (k, y)).2) (tailoringCoreSection I φEnd β)
                    {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
                  BijOn (fun y => (G (τ y) (k, y)).2) (tailoringCoreSection I φEnd β)
                    (tailoringLegendreConic I φEnd ∩
                      range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                        P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map) ∧
                  ∀ x : TangentCoordinates n, lgCover x ∈ tailoringCoreSection I φEnd β →
                    ∃ V : Set (ℝ × TangentCoordinates n), IsOpen V ∧ (k, x) ∈ V ∧
                      ∃ τlocal : ℝ × TangentCoordinates n → ℝ,
                        ContDiffOn ℝ ∞ τlocal V ∧ τlocal (k, x) = τ (lgCover x) ∧
                        (∀ p ∈ V, φ (G (τlocal p) (p.1, lgCover p.2)).2.1 =
                          Cplus ^ 2 * β ^ 2 / 2) ∧
                        ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
                          (fun p => (G (τlocal p) (p.1, lgCover p.2)).2) V := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, _hzero, c, U, hc, hU, hlower, hupper,
    _hnear, L, hL, hend, ΦEnd, Φ, hΦEndeq, hΦEnd0, hΦEnd,
    hΦEndinv, hΦeq, _hΦ, hΦinv, _Fcore, _hFcore, Bcore, _hBcore, hcore⟩ :=
    I.exists_complete_tailoring_fullCore
  obtain ⟨D₀, _hD₀, hhits⟩ := tailoringEndpoint_exists_uniform_native_outer_boundary_bijection
    I hφ hc hU hlower hupper hEnd1 hstrong ΦEnd hΦEndeq hΦEnd0 hΦEnd hΦEndinv hL hend
  obtain ⟨Aamb, F, hamb, hF, hprefix⟩ :=
    coefficientPath_tailoring_exists_uniform_original_marked_prefix
      I hφ hc hU hlower hupper hEnd1 hstrong.smooth hstrong.homogeneous hL hend
  let Cminus := F + 1
  let Cplus := max (F + 2) D₀
  have hCminus : 0 < Cminus := by dsimp [Cminus]; linarith
  have hFCminus : F < Cminus := by dsimp [Cminus]; linarith
  have hCminusCplus : Cminus < Cplus :=
    (by dsimp only [Cminus]; linarith : Cminus < F + 2).trans_le (le_max_left _ _)
  have hCplus : 0 < Cplus := hCminus.trans hCminusCplus
  obtain ⟨Bprefix, hBprefix, hprefix⟩ := hprefix Cplus (hFCminus.trans hCminusCplus)
  obtain ⟨Bhits, _hBhits, hhits⟩ := hhits Cplus (le_max_right _ _)
  obtain ⟨Bdomain, _hBdomain, hdomain⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hstrong.smooth hstrong.homogeneous hL hend hCplus
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ,
    ⟨⟨hφ, hEnd1, c, U, hc, hU, hlower, hupper, L, hL, hend,
      ΦEnd, Φ, hΦEndeq, hΦEnd0, hΦeq, hΦinv⟩⟩, c, U, hc, hU, hlower, hupper,
    ⟨L, hL, hend⟩, Aamb, Cminus, Cplus, max Bprefix (max Bcore (max Bhits Bdomain)),
    hamb, hCminus, hCminusCplus, hBprefix.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨hβP, hβC, hβH, hβD⟩ : Bprefix ≤ β ∧ Bcore ≤ β ∧ Bhits ≤ β ∧ Bdomain ≤ β := by
    simpa only [max_le_iff] using hβ
  have hβpos := hBprefix.trans_le hβP
  obtain ⟨hR, hset, hfib, Kstar, hKstar, hprefix⟩ := hprefix β hβP
  have hlevel : F ^ 2 * β ^ 2 / 2 < Cminus ^ 2 * β ^ 2 / 2 := by gcongr
  have houter : Cminus ^ 2 * β ^ 2 / 2 < Cplus ^ 2 * β ^ 2 / 2 := by gcongr
  obtain ⟨δ, hδ, _hgap, hprefix⟩ := hprefix (Cminus ^ 2 * β ^ 2 / 2) hlevel houter
  refine ⟨hR, hset, ⟨F ^ 2 * β ^ 2 / 2, hfib, hlevel⟩, ?_⟩
  intro originalK hK
  let K := max Kstar (originalK * Real.exp β ^ 2)
  have hKpos : 0 < K := hKstar.trans_le (le_max_left _ _)
  have hKL : originalK ≤ K / Real.exp β ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos β))).mpr (le_max_right _ _)
  let m : RoundingChoice := ⟨δ, roundingProfile δ hδ⟩
  obtain ⟨hm, hprefix⟩ := hprefix m hδ le_rfl originalK hK
  obtain ⟨P⟩ := hprefix K (le_max_left _ _) hKL
  have hcoreP :
      ((P.marked.tailoring.embedding parameterOne).comp
        (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
          P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
        P.marked.tailoring.deformation.target.ribbonCompletion.core =
          tailoringCoreSection I φEnd β := by
    obtain ⟨_hcompact, _hbij, _himageRadial, N, j, Q, himage, hiff, _htruncations⟩ := hcore β hβC
    apply (P.marked.tailoring.ribbon_marking parameterOne).image_core_eq_of_fullFiber N j Q
      (by simpa [parameterOne] using himage)
    · intro y hy
      rw [himage]
      exact hy.2
    · exact hiff
  have hreg : ∀ y : LGSpace n, φ y.1 - Cplus ^ 2 * β ^ 2 / 2 = 0 →
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
        (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2) y ≠ 0 := by
    exact regular_zero_of_scalarDerivative_pos (lgManifold n)
      (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2)
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) K))
      ((hdomain β hβD).2.2 1 (by simp) K hKpos.le).2
  have hboundaryP : range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
      P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map =
      {z | φ z.1 = Cplus ^ 2 * β ^ 2 / 2} := by
    calc
      _ = {z | φ z.1 - Cplus ^ 2 * β ^ 2 / 2 = 0} :=
        P.marked.tailoring_ambient_marking.native_boundary_image
          ((contMDiff_potentialValue hφ).sub contMDiff_const) hreg
      _ = _ := by ext z; exact sub_eq_zero
  obtain ⟨G, hG, hfst, hnative, htimes⟩ := hhits β hβH K
  refine ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst, hnative, ?_⟩
  intro k hk
  obtain ⟨τ, hτ, hbij, hsmooth⟩ := htimes k hk
  refine ⟨τ, hτ, hbij, ?_, hsmooth⟩
  rw [hboundaryP]
  exact hbij

/-- The established native-hitting interface is the projection of the same
selected construction retaining its analytic Legendre data. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hits
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      ∃ c U : ℝ, 0 < c ∧ 0 < U ∧
      (∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
        inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) ∧
      (∀ u v : EuclideanSpace ℝ (Fin n),
        inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) ∧
      (∃ L > 0, ∀ u, L ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) ∧
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
                ∀ k ∈ Icc (0 : ℝ) K, ∃ τ : LGSpace n → ℝ,
                  (∀ y ∈ tailoringCoreSection I φEnd β,
                    0 < τ y ∧ φ (G (τ y) (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 ∧
                    (∀ s, φ (G s (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 → s = τ y) ∧
                    ∀ s ∈ Icc (0 : ℝ) (τ y), (G s (k, y)).2 ∈ tailoringLegendreConic I φEnd ∧
                      1 ≤ (tailoringFamily I β 1 (G s (k, y)).2).re) ∧
                  BijOn (fun y => (G (τ y) (k, y)).2) (tailoringCoreSection I φEnd β)
                    {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
                  BijOn (fun y => (G (τ y) (k, y)).2) (tailoringCoreSection I φEnd β)
                    (tailoringLegendreConic I φEnd ∩
                      range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                        P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map) ∧
                  ∀ x : TangentCoordinates n, lgCover x ∈ tailoringCoreSection I φEnd β →
                    ∃ V : Set (ℝ × TangentCoordinates n), IsOpen V ∧ (k, x) ∈ V ∧
                      ∃ τlocal : ℝ × TangentCoordinates n → ℝ,
                        ContDiffOn ℝ ∞ τlocal V ∧ τlocal (k, x) = τ (lgCover x) ∧
                        (∀ p ∈ V, φ (G (τlocal p) (p.1, lgCover p.2)).2.1 =
                          Cplus ^ 2 * β ^ 2 / 2) ∧
                        ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
                          (fun p => (G (τlocal p) (p.1, lgCover p.2)).2) V := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, _hLegendre, rest⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_hits_with_legendre
  exact ⟨φEnd, φ, hstrong, hEnd1, hφ, rest⟩

end FsFltz
