import FsFltz.Geometry.TailoringRoundedMarkingFamilyTransfer
import FsFltz.Geometry.CommonEmbeddingCompactMap

/-!
# Common completion markings on the same rounded pair carriers

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and the actual common marking, lines 1270–1303. The prescribed compact
source presentation is retained. A compact diffeomorphism is constructed
from its full rounded image and the native rounded sublevel in the outer
completion, and then extended by the proved absorption construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance roundedMarkingFamilyLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

/-- On any prescribed rounded Liouville presentation, actual compact
confinement and positivity construct an inclusion marking into the named
outer completion. Its projection retains the original compact embedding
and its all-real boundary flow. No source completion is replaced. -/
theorem tailoringRounded_exists_inclusionMarking_on_same_presentation
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β s K R A : ℝ) (hR : 0 < R) (m : RoundingChoice)
    (S : LiouvilleDomain (2 * n)) (CS : Completion S)
    (hS : S.domain.carrier.Nonempty)
    (j : S.domain.extension.SmoothEmbedding (lgManifold n))
    (himage : j.map '' S.domain.carrier = tailoringRoundedDomain I φ β s R A m)
    (hp : ∀ x ∈ S.domain.carrier, S.liouville.primitive x =
      S.domain.extension.pullback (lgManifold n) j.map
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K) x)
    (hcompact : IsCompact {y : LGSpace n | φ y.1 - A ≤ 0})
    (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ)
    (hout : ∀ y : (lgManifold n).Point, φ y.1 - A = 0 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - A) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y)) :
    let E := tailoringPotentialOuterDomain I hφ β s K A hcompact hω hout
    ∀ C : LiouvilleDomain.FlowCollar E,
    (∀ y ∈ E.domain.carrier, 0 ≤ tailoringRoundedDefiningFunction I φ β s R A m y →
      0 < (lgManifold n).scalarDerivative (tailoringRoundedDefiningFunction I φ β s R A m)
        y (E.liouville.field y)) →
    ∃ (i : S.domain.Point → C.cylindricalCompletion.ambient.manifold.Point)
      (q : InclusionMarking CS C.cylindricalCompletion.ambient i),
      (∀ x, C.originalInclusion.map (i x) = j.map x.val) ∧
      ∀ b r, q.equiv (CS.endMap (b, r)) =
        C.cylindricalCompletion.ambient.completeFlow.flow r
          (i ⟨S.domain.boundaryInclusion.map b, S.domain.boundaryInclusion_mem_carrier b⟩) := by
  intro E C hpos
  let P := C.cylindricalCompletion.ambient
  let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K
  let ρ₀ := tailoringRoundedDefiningFunction I φ β s R A m
  let ρ : P.manifold.Point → ℝ := fun z => ρ₀ (C.originalInclusion.map z)
  have hρ₀ := contMDiff_tailoringRoundedDefiningFunction I hφ β s R A m
  have hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ :=
    hρ₀.comp C.originalInclusion.map.contMDiff
  have hsubset : {z : P.manifold.Point | ρ z ≤ 0} ⊆ C.localizedDomain.domain.carrier := by
    intro z hz
    have hφz := (tailoringRoundedDomain_subset I φ β s A hR m hz).1
    change φ z.val.val.1 - A ≤ 0
    exact sub_nonpos.mpr hφz
  have hcompactρ : IsCompact {z : P.manifold.Point | ρ z ≤ 0} :=
    C.localizedDomain.domain.compact.of_isClosed_subset
      (isClosed_le hρ.continuous continuous_const) hsubset
  have houtρ : ∀ z : P.manifold.Point, ρ z = 0 →
      0 < P.manifold.scalarDerivative ρ z (P.manifold.liouvilleVector P.primitive z) := by
    intro z hz
    have hzc := hsubset hz.le
    rw [← P.field_eq_liouvilleVector]
    change 0 < C.localizedDomain.domain.extension.scalarDerivative
      (fun y => ρ₀ (C.originalInclusion.map y)) z (P.field z)
    rw [C.scalarDerivative_originalInclusion ρ₀ hρ₀]
    erw [C.cylindricalCompletion_original_field z hzc]
    exact hpos z.val.val hzc hz.ge
  have habsorb : ∀ z : P.manifold.Point, ∃ T : ℝ, 0 ≤ T ∧
      ρ (P.completeFlow.flow (-T) z) ≤ 0 := by
    intro z
    obtain ⟨T, hT, _hc, he⟩ := C.exists_nonneg_time_original_scalar_le ρ₀ hρ₀ 0 hpos z
    exact ⟨T, hT, he⟩
  let B := regularSublevelLiouvilleDomain P.manifold ρ hρ hcompactρ
    P.primitive P.smooth_primitive P.symplectic houtρ
  have himageB : C.originalInclusion.map '' B.domain.carrier =
      tailoringRoundedDomain I φ β s R A m := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hyE : y ∈ E.domain.carrier :=
        sub_nonpos.mpr (tailoringRoundedDomain_subset I φ β s A hR m hy).1
      let z := C.cylindricalCompactHomeomorph.symm ⟨y, hyE⟩
      have he : C.originalInclusion.map z.val = y :=
        congrArg Subtype.val (C.cylindricalCompactHomeomorph.apply_symm_apply ⟨y, hyE⟩)
      refine ⟨z.val, ?_, he⟩
      change ρ₀ (C.originalInclusion.map z.val) ≤ 0
      rw [he]
      exact hy
  obtain ⟨h, hsquare, _hinverse⟩ := S.domain.exists_compactDiffeomorph_of_commonEmbedding
    B.domain (lgManifold n) hS j C.originalInclusion (himage.trans himageB.symm)
  have hP (z : P.manifold.Point) (hz : z ∈ B.domain.carrier) :
      P.primitive z = P.manifold.pullback (lgManifold n) C.originalInclusion.map α z := by
    change P.primitive z =
      C.localizedDomain.domain.extension.pullback E.domain.extension C.originalInclusion.map α z
    rw [C.pullback_originalInclusion]
    exact C.cylindricalCompletion_original_primitive z (hsubset hz)
  have hp' : ∀ x ∈ S.domain.carrier,
      S.domain.extension.pullback P.manifold h.map P.primitive x = S.liouville.primitive x := by
    intro x hx
    rw [hp x hx]
    have he := h.pullback_of_commonEmbedding (lgManifold n) j C.originalInclusion hsquare α x hx
    unfold SmoothManifold.pullback at he ⊢
    rw [hP (h.map x) (h.maps_source hx)]
    exact he
  obtain ⟨q, hend⟩ := CS.exists_inclusionMarking_of_absorbing_sublevel P ρ hρ
    hcompactρ houtρ habsorb h hp'
  exact ⟨fun x => h.map x.val, q,
    fun x => hsquare x.val (h.contains_source x.property), hend⟩

/-- Finite toric estimates construct actual common outer markings on every
supplied genuine rounded presentation and its already chosen completion.
The quantifier over source completions preserves independently assembled
pair families rather than selecting new rounded carriers. -/
theorem tailoringFamily_exists_uniform_rounded_markings_on_same_presentation
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {Cplus : ℝ} (hCplus : 0 < Cplus) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ K ≥ Kstar, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ (S : LiouvilleDomain (2 * n)) (CS : Completion S), S.domain.carrier.Nonempty →
      ∀ j : S.domain.extension.SmoothEmbedding (lgManifold n),
      j.map '' S.domain.carrier =
        tailoringRoundedDomain I φ β s R (Cplus ^ 2 * β ^ 2 / 2) m →
      (∀ x ∈ S.domain.carrier, S.liouville.primitive x =
        S.domain.extension.pullback (lgManifold n) j.map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K) x) →
      ∃ (hcompact : IsCompact {y : LGSpace n | φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0})
        (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ)
        (hout : ∀ y : (lgManifold n).Point, φ y.1 - Cplus ^ 2 * β ^ 2 / 2 = 0 →
          0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2) y
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β s) K) y)),
      let E := tailoringPotentialOuterDomain I hφ β s K (Cplus ^ 2 * β ^ 2 / 2) hcompact hω hout
      ∀ C : LiouvilleDomain.FlowCollar E,
      ∃ (i : S.domain.Point → C.cylindricalCompletion.ambient.manifold.Point)
        (q : InclusionMarking CS C.cylindricalCompletion.ambient i),
        (∀ x, C.originalInclusion.map (i x) = j.map x.val) ∧
        ∀ b r, q.equiv (CS.endMap (b, r)) =
          C.cylindricalCompletion.ambient.completeFlow.flow r
            (i ⟨S.domain.boundaryInclusion.map b, S.domain.boundaryInclusion_mem_carrier b⟩) := by
  obtain ⟨Bo, _hBo, ho⟩ := tailoringFamily_exists_uniform_rounded_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend hCplus
  obtain ⟨BD, _hBD, hDdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend hCplus
  let β₀ := max 1 (max Bo BD)
  refine ⟨β₀, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβo : Bo ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβD : BD ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hcompact, _hne, hdata⟩ := hDdata β hβD
  obtain ⟨Kstar, hKstar, hout⟩ := ho β hβo
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hgap
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout R hR Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd K hK s hs S CS hS j hj hp
  obtain ⟨hω, hb⟩ := hdata s hs K (hKstar.le.trans hK)
  refine ⟨hcompact, hω, hb, ?_⟩
  intro E C
  apply tailoringRounded_exists_inclusionMarking_on_same_presentation I hφ β s K R
    (Cplus ^ 2 * β ^ 2 / 2) hR m S CS hS j hj hp hcompact hω hb C
  intro y hy hqy
  exact hout m hm hmd K hK s hs y (sub_nonpos.mp hy) hqy

/-- The same actual rounded completed pair family carries constructed inclusion
markings into every chosen native outer completion at every parameter.
All original tuple, whole-carrier, frontier and presentation equations are retained. -/
theorem tailoringFamily_exists_uniform_rounded_pairDeformation_with_inclusion_markings
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∀ Cplus : ℝ, F < Cplus →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ (E : CompactDomain (2 * n)) (D : CompactDomain (2 * n - 2))
        (k : D.extension.SmoothEmbedding E.boundary)
        (J : Parameter → E.extension.SmoothEmbedding (lgManifold n))
        (Λ : (K : ℝ) → Kstar ≤ K → Parameter → LiouvilleStructure E)
        (Μ : Parameter → LiouvilleStructure D),
        let W := fun t => (J t).comp (E.boundaryInclusion.comp k)
        E.carrier.Nonempty ∧ D.carrier.Nonempty ∧
        E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (W t).map) ∧
        (∀ t : Parameter,
          (J t).map '' E.carrier = tailoringRoundedDomain I φ β t.val R
            (Cplus ^ 2 * β ^ 2 / 2) m ∧
          (J t).map '' frontier E.carrier =
            {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
          (W t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
          (W t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus}) ∧
        (∀ K hK t, (Λ K hK t).primitive = E.extension.pullback (lgManifold n) (J t).map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K)) ∧
        (∀ t, (Μ t).primitive = D.extension.pullback (lgManifold n) (W t).map
          (lambdaPotentialForm φ)) ∧
        ∀ K hK,
          ∃ hribbon : ∀ t x, x ∈ D.carrier →
            D.extension.pullback E.boundary k.map
              (fun y => (1 : ℝ) • E.boundaryForm (Λ K hK t).primitive y) x = (Μ t).primitive x,
          ∃ (hα : E.extension.IsSmoothIntervalFormFamily (fun t => (Λ K hK t).primitive))
            (hμ : D.extension.IsSmoothIntervalFormFamily (fun t => (Μ t).primitive))
            (hk : D.extension.IsSmoothIntervalMapFamily E.boundary (fun _ => k.map))
            (hb : E.boundary.IsSmoothIntervalScalarFamily (fun _ _ => (1 : ℝ)))
            (ambient : LocalizedCompletionFamily E (Λ K hK))
            (ribbon : LocalizedCompletionFamily D Μ),
          let A := ambient.collars
          let B := ribbon.collars
          ∃ Q : PairDeformation n,
            Q = E.localizedPairDeformation D (Λ K hK) Μ (fun _ => k) (fun _ _ => 1)
              hα hμ hk hb (fun _ _ => zero_lt_one) ambient ribbon hribbon ∧
            Q.pair = (fun t => localizedWitnessedPair ⟨E, Λ K hK t⟩ ⟨D, Μ t⟩ (A t) (B t)
              k (fun _ => 1) contMDiff_const (fun _ => zero_lt_one) (hribbon t)) ∧
            ∀ t : Parameter,
              ((J t).comp (A t).originalInclusion).map '' (A t).localizedDomain.domain.carrier =
                tailoringRoundedDomain I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m ∧
              ((J t).comp (A t).originalInclusion).map '' frontier (A t).localizedDomain.domain.carrier =
                {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
              ((W t).comp (B t).originalInclusion).map '' (B t).localizedDomain.domain.carrier =
                {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
              ((W t).comp (B t).originalInclusion).map '' frontier (B t).localizedDomain.domain.carrier =
                {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus} ∧
              ∃ (hcompact : IsCompact {y : LGSpace n | φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0})
                (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β t.val) K)) univ)
                (hout : ∀ y : (lgManifold n).Point, φ y.1 - Cplus ^ 2 * β ^ 2 / 2 = 0 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) y)),
              let Outer := tailoringPotentialOuterDomain I hφ β t.val K
                (Cplus ^ 2 * β ^ 2 / 2) hcompact hω hout
              ∀ C : LiouvilleDomain.FlowCollar Outer,
              ∃ (i : (A t).localizedDomain.domain.Point → C.cylindricalCompletion.ambient.manifold.Point)
                (q : InclusionMarking (A t).cylindricalCompletion C.cylindricalCompletion.ambient i),
                (∀ x, C.originalInclusion.map (i x) = (J t).map ((A t).originalInclusion.map x.val)) ∧
                ∀ b r, q.equiv ((A t).cylindricalCompletion.endMap (b, r)) =
                  C.cylindricalCompletion.ambient.completeFlow.flow r
                    (i ⟨(A t).localizedDomain.domain.boundaryInclusion.map b,
                      (A t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩) := by
  obtain ⟨F, hF, hpair⟩ := tailoringFamily_exists_uniform_rounded_pairDeformation_with_presentations
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, ?_⟩
  intro Cplus hCplus
  obtain ⟨Bp, hBp, hpair⟩ := hpair Cplus hCplus
  obtain ⟨Bm, _hBm, hmark⟩ := tailoringFamily_exists_uniform_rounded_markings_on_same_presentation
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend (hF.trans hCplus)
  refine ⟨max Bp Bm, hBp.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨Kp, hKp, hpair⟩ := hpair β ((le_max_left _ _).trans hβ)
  obtain ⟨Km, _hKm, hmark⟩ := hmark β ((le_max_right _ _).trans hβ)
  refine ⟨max Kp Km, hKp.trans_le (le_max_left _ _), ?_⟩
  intro R hR Aminus hlo hhi
  obtain ⟨δp, hδp, hgp, hpair⟩ := hpair R hR Aminus hlo hhi
  obtain ⟨δm, hδm, _hgm, hmark⟩ := hmark R hR Aminus hhi
  refine ⟨min δp δm, lt_min hδp hδm, (min_le_left _ _).trans_lt hgp, ?_⟩
  intro m hm hmd
  obtain ⟨E, D, k, J, Λ, Μ, hE, hD, hJ, hW, himages, hΛ, hΜ, hpair⟩ :=
    hpair m hm (hmd.trans (min_le_left _ _))
  let Λ' : (K : ℝ) → max Kp Km ≤ K → Parameter → LiouvilleStructure E :=
    fun K hK => Λ K ((le_max_left _ _).trans hK)
  refine ⟨E, D, k, J, Λ', Μ, hE, hD, hJ, hW, himages, ?_, hΜ, ?_⟩
  · intro K hK t
    exact hΛ K ((le_max_left _ _).trans hK) t
  · intro K hK
    obtain ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, hQ, hpairs, hlocalImages⟩ :=
      hpair K ((le_max_left _ _).trans hK)
    refine ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, hQ, hpairs, ?_⟩
    intro t
    refine ⟨(hlocalImages t).1, (hlocalImages t).2.1, (hlocalImages t).2.2.1,
      (hlocalImages t).2.2.2, ?_⟩
    let A := ambient.collars
    let S := (A t).localizedDomain
    let CS := (A t).cylindricalCompletion
    let j := (J t).comp (A t).originalInclusion
    have hS : S.domain.carrier.Nonempty := by
      obtain ⟨x, hx⟩ := hE
      let z := (A t).cylindricalCompactHomeomorph.symm ⟨x, hx⟩
      exact ⟨z.val, z.property⟩
    have hp : ∀ x ∈ S.domain.carrier, S.liouville.primitive x =
        S.domain.extension.pullback (lgManifold n) j.map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) x := by
      intro x _hx
      have he : S.domain.extension.pullback (lgManifold n) j.map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) x =
          (Λ' K hK t).primitive ((A t).originalInclusion.map x) := by
        change S.domain.extension.pullback (lgManifold n)
          ((J t).map ∘ (A t).originalInclusion.map) _ x = _
        rw [S.domain.extension.pullback_comp E.extension (lgManifold n)
          ((A t).originalInclusion.map.contMDiff.mdifferentiable (by simp))
          ((J t).map.contMDiff.mdifferentiable (by simp))]
        rw [← hΛ K ((le_max_left _ _).trans hK) t, (A t).pullback_originalInclusion]
        rfl
      rw [he]
      exact (A t).original_primitive x
    obtain ⟨hcpt, hω, hout, hmarked⟩ := hmark m hm (hmd.trans (min_le_right _ _))
      K ((le_max_right _ _).trans hK) t.val t.property S CS hS j
      (hlocalImages t).1 hp
    exact ⟨hcpt, hω, hout, hmarked⟩

end FsFltz
