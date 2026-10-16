import FsFltz.Geometry.TailoringStrictWitness
import FsFltz.Geometry.TailoringStrictRetainedAmbient
import FsFltz.Geometry.TailoringHittingRibbonFamilyRetained

/-!
# Actual scale-one strict incoming identifications

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1919;
`geoemtric-part-fsf.tex`, `def:chain`, lines 171–199. The incoming witnessed
pair and its completion identification are constructed from the actual
strict completed map and whole-ribbon hitting equations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
namespace WitnessedPair

/-- The actual incoming witness, scale-one identification, and interpolation
are produced from raw strict map equations on the whole ribbon. -/
theorem exists_strictIncomingJunction {n : ℕ} (P Q : WitnessedPair n)
    (e : P.ambientManifold.SmoothEquiv Q.ambientManifold)
    (he : P.ambientManifold.pullback Q.ambientManifold e
      Q.ambientCompletion.ambient.primitive = P.ambientCompletion.ambient.primitive)
    (ψ : P.ambientDomain.domain.boundary.SmoothEquiv Q.ambientDomain.domain.boundary)
    (s : P.ambientDomain.domain.boundary.Point → ℝ)
    (hs : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ s)
    (hend : ∀ x r, e (P.ambientCompletion.endMap (x, r)) =
      Q.ambientCompletion.endMap (ψ x, r + s x))
    (hcontact : P.ambientDomain.domain.boundary.pullback Q.ambientDomain.domain.boundary ψ
      (Q.ambientDomain.domain.boundaryForm Q.ambientDomain.liouville.primitive) =
      fun x => Real.exp (-s x) •
        P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x)
    (h : CompactDomainDiffeomorph P.ribbonDomain.domain Q.ribbonDomain.domain)
    (hp : ∀ x ∈ P.ribbonDomain.domain.carrier,
      P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension h.map
        Q.ribbonDomain.liouville.primitive x = P.ribbonDomain.liouville.primitive x)
    (τ : P.ribbonDomain.domain.extension.Point → ℝ)
    (hsquare : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ψ (P.ribbonEmbedding.map x) = Q.ribbonEmbedding.map (h.map x))
    (hshift : ∀ x ∈ P.ribbonDomain.domain.carrier, s (P.ribbonEmbedding.map x) = -τ x)
    (hwitness : ∀ x ∈ P.ribbonDomain.domain.carrier,
      Q.witness (Q.ribbonEmbedding.map (h.map x)) = Real.exp (-τ x)) :
    ∃ (R : WitnessedPair n) (C : CompletionIdentification P R) (B : PairDeformation n),
      C.scale = 1 ∧ HEq C.ambientEquiv e ∧ HEq C.ribbonEquiv h ∧
      HEq R.witness (P.strictIncomingWitness Q ψ s) ∧
      B.source = Q ∧ B.target = R := by
  let b := P.strictIncomingWitness Q ψ s
  have hb := P.strictIncomingWitness_smooth Q ψ s hs
  have hpos := P.strictIncomingWitness_positive Q ψ s
  have heq := P.strictIncomingWitness_eq_on_ribbon Q ψ s h τ hsquare hshift hwitness
  let R := Q.withWitness b hb hpos heq
  let C : CompletionIdentification P R :=
    { ambientEquiv := e
      primitive := he
      boundaryEquiv := ψ
      shift := s
      smooth_shift := hs
      induced_at_infinity := fun x => ⟨0, fun r _ => hend x r⟩
      boundary_primitive := hcontact
      ribbonEquiv := h
      scale := 1
      positive_scale := zero_lt_one
      ribbon_primitive := by
        intro x hx
        change P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension h.map
          Q.ribbonDomain.liouville.primitive x = 1 • P.ribbonDomain.liouville.primitive x
        simpa only [one_smul] using hp x hx
      ribbon_square := hsquare }
  let B := Q.witnessDeformation b hb hpos heq
  exact ⟨R, C, B, rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    Q.witnessDeformation_source b hb hpos heq,
    Q.witnessDeformation_target b hb hpos heq⟩

end WitnessedPair
end FsFltz.Geometry

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Constructed strict incoming identification and witness interpolation.
The finite chain is computed from these operations and the retained hitting
deformation; no chain is a field of the data. -/
structure StrictHittingJunction {n : ℕ} (P : WitnessedPair n) (H : PairDeformation n) where
  incoming : WitnessedPair n
  identification : CompletionIdentification P incoming
  scale_one : identification.scale = 1
  interpolation : PairDeformation n
  interpolation_source : interpolation.source = H.source
  interpolation_target : interpolation.target = incoming

namespace StrictHittingJunction
variable {n : ℕ} {P : WitnessedPair n} {H : PairDeformation n}

/-- The actual reverse witness deformation has exactly these two tuples. -/
def witnessStep (J : StrictHittingJunction P H) : ComparisonStep n J.incoming H.source := by
  rw [← J.interpolation_target, ← J.interpolation_source]
  exact .reverse (.deformation J.interpolation)

/-- The three literal operations: strict identification, witness
interpolation, and this same decreasing-coefficient hitting deformation. -/
def chain (J : StrictHittingJunction P H) : ComparisonChain P H.target :=
  ((Quiver.Path.nil.cons (ComparisonStep.identification J.identification)).cons
    J.witnessStep).cons (ComparisonStep.deformation H)

@[simp] theorem chain_length (J : StrictHittingJunction P H) : J.chain.length = 3 := rfl

end StrictHittingJunction

/-- The specified completed hitting family joins a rounded pair by the
constructed strict incoming identification, actual witness interpolation,
and this very hitting deformation. The regional equations are analytic
flow data, not a supplied comparison chain. -/
theorem CompletedHittingRibbonFamily.exists_strictJunction_of_regional_hits
    {n : ℕ} (P : WitnessedPair n)
    {D : CompactDomain (2 * n)} {L : Parameter → LiouvilleStructure D}
    {j : Parameter → P.ribbonDomain.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D P.ribbonDomain L j b)
    (i : P.ambientDomain.domain.Point →
      (H.ambient.collars parameterZero).cylindricalCompletion.ambient.manifold.Point)
    (q : InclusionMarking P.ambientCompletion
      (H.ambient.collars parameterZero).cylindricalCompletion.ambient i)
    (M : SmoothManifold (2 * n)) (e : D.extension.SmoothEmbedding M)
    (α : M.Form 1) (hα : M.IsSmoothForm α)
    (hprimitive : (L parameterZero).primitive = D.extension.pullback M e.map α)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ)
    (A k : ℝ) (himage : e.map '' D.carrier = {y | ρ y ≤ A})
    (hnd : ∀ y, ρ y ≤ A → M.Nondegenerate (M.exteriorDerivative α) y)
    (G : Flow ℝ (ℝ × M.Point))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × M.Point) => G p.1 p.2))
    (hnative : ∀ y t, ρ (G t (k, y)).2 ≤ A →
      IsMIntegralCurveAt (fun s => (G s (k, y)).2) (M.liouvilleVector α) t)
    (hout : ∀ y, ρ y = A → 0 < M.scalarDerivative ρ y (M.liouvilleVector α y))
    (τ : P.ribbonDomain.domain.extension.Point → ℝ)
    (start : P.ribbonDomain.domain.extension.Point → M.Point)
    (hstart : ∀ x ∈ P.ribbonDomain.domain.carrier,
      e.map ((H.ambient.collars parameterZero).originalInclusion.map
        (i ⟨P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x),
          P.ambientDomain.domain.boundaryInclusion_mem_carrier (P.ribbonEmbedding.map x)⟩)) = start x)
    (htime : ∀ x ∈ P.ribbonDomain.domain.carrier, 0 < τ x)
    (hboundary : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ρ (e.map (D.boundaryInclusion.map ((j parameterZero).map x))) = A)
    (hhit : ∀ x ∈ P.ribbonDomain.domain.carrier,
      (G (τ x) (k, start x)).2 = e.map (D.boundaryInclusion.map ((j parameterZero).map x)))
    (hwitness : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b parameterZero ((j parameterZero).map x) = Real.exp (-τ x))
    (hne : P.ribbonDomain.domain.carrier.Nonempty) :
    Nonempty (StrictHittingJunction P H.deformation) := by
  let A₀ := H.ambient.collars parameterZero
  let F₀ := H.ribbon.collars parameterZero
  let Q := H.deformation.source
  obtain ⟨ψ, s, hs, hend, hcontact, hwhole⟩ :=
    A₀.exists_boundaryEquiv_of_regional_cutoff_ribbon_hits P i q M e α hα hprimitive
      ρ hρ A k himage hnd G hG hnative hout (j parameterZero).map τ start
      hstart htime hboundary hhit
  obtain ⟨h, hproj, hp⟩ := F₀.exists_originalCompactComparison hne
  have hsquare : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ψ (P.ribbonEmbedding.map x) = Q.ribbonEmbedding.map (h.map x) := by
    intro x hx
    change ψ (P.ribbonEmbedding.map x) = (j parameterZero).map (F₀.originalInclusion.map (h.map x))
    rw [hproj x (h.contains_source hx)]
    exact (hwhole x hx).1
  have hshift : ∀ x ∈ P.ribbonDomain.domain.carrier, s (P.ribbonEmbedding.map x) = -τ x :=
    fun x hx => (hwhole x hx).2
  have hw : ∀ x ∈ P.ribbonDomain.domain.carrier,
      Q.witness (Q.ribbonEmbedding.map (h.map x)) = Real.exp (-τ x) := by
    intro x hx
    change b parameterZero ((j parameterZero).map (F₀.originalInclusion.map (h.map x))) = _
    rw [hproj x (h.contains_source hx)]
    exact hwitness x hx
  have hc : P.ambientDomain.domain.boundary.pullback Q.ambientDomain.domain.boundary ψ
      (Q.ambientDomain.domain.boundaryForm Q.ambientDomain.liouville.primitive) =
      fun x => Real.exp (-s x) •
        P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x := by
    change P.ambientDomain.domain.boundary.pullback D.boundary ψ
      (A₀.localizedDomain.domain.boundaryForm A₀.localizedDomain.liouville.primitive) = _
    rw [A₀.localized_boundaryForm]
    exact hcontact
  obtain ⟨R, C, B, hscale, _he, _hr, _hw, hsource, htarget⟩ :=
    P.exists_strictIncomingJunction Q q.equiv q.primitive ψ s hs hend hc h hp τ
      hsquare hshift hw
  exact ⟨⟨R, C, hscale, B, hsource, htarget⟩⟩

end FsFltz

namespace FsFltz
open Geometry Geometry.SmoothManifold

local instance strictJunctionLGCharts {n : ℕ} : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance strictJunctionLGSmooth {n : ℕ} : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- Construct the literal strict junction for this retained prefix, its
actual finite intrinsic shrink, and these actual completed hitting slices.
The strict marking and boundary map are derived, not supplied. -/
theorem PotentialTailoringMarkedPrefix.exists_strictJunction_into_retained_hitting
    {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
    {β Cplus Aminus K : ℝ} {m : RoundingChoice}
    (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (hφ : ContDiff ℝ ∞ φ)
    (S : IntrinsicShrinkingData P.tailoring.deformation.target)
    {L : Parameter → LiouvilleStructure P.tailoring_ambient_marking.domain}
    {j : Parameter → (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding
      P.tailoring_ambient_marking.domain.boundary}
    {b : Parameter → P.tailoring_ambient_marking.domain.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily P.tailoring_ambient_marking.domain
      (S.pair parameterOne).ribbonDomain L j b)
    (hL : (L parameterZero).primitive = P.tailoring_ambient_marking.domain.extension.pullback
      (lgManifold n) P.tailoring_ambient_marking.nativeEmbedding.map
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K))
    (hboundary : range (P.tailoring_ambient_marking.nativeEmbedding.comp
      P.tailoring_ambient_marking.domain.boundaryInclusion).map =
      {y | φ y.1 = Cplus ^ 2 * β ^ 2 / 2})
    (hnd : ∀ y : LGSpace n, (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) y)
    (hout : ∀ y : LGSpace n, φ y.1 = Cplus ^ 2 * β ^ 2 / 2 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) K) y))
    (G : Flow ℝ (ℝ × LGSpace n))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    (hnative : ∀ y t, φ (G t (K, y)).2.1 ≤ Cplus ^ 2 * β ^ 2 / 2 →
      IsMIntegralCurveAt (fun s => (G s (K, y)).2)
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t)
    (τ : (S.pair parameterOne).ribbonDomain.domain.extension.Point → ℝ)
    (htime : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier, 0 < τ x)
    (hhit : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
      (G (τ x) (K, (P.tailoring.ribbon_marking parameterOne).embedding.map
        ((S.fiberEmbedding (P.tailoring.ribbon_marking parameterOne) parameterOne).map x))).2 =
      (P.tailoring_ambient_marking.nativeEmbedding.comp
        P.tailoring_ambient_marking.domain.boundaryInclusion).map ((j parameterZero).map x))
    (hwitness : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
      b parameterZero ((j parameterZero).map x) = Real.exp (-τ x)) :
    Nonempty (StrictHittingJunction (S.pair parameterOne) H.deformation) := by
  let O := P.tailoring_ambient_marking
  let F := S.pair parameterOne
  let M := P.tailoring.ribbon_marking parameterOne
  let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K
  obtain ⟨i, q, hi⟩ := P.exists_marking_into_hitting_collar (L parameterZero)
    (H.ambient.collars parameterZero) hL
  have hstart : ∀ x ∈ F.ribbonDomain.domain.carrier,
      O.nativeEmbedding.map ((H.ambient.collars parameterZero).originalInclusion.map
        (i ⟨F.ambientDomain.domain.boundaryInclusion.map (F.ribbonEmbedding.map x),
          F.ambientDomain.domain.boundaryInclusion_mem_carrier (F.ribbonEmbedding.map x)⟩)) =
        M.embedding.map ((S.fiberEmbedding M parameterOne).map x) := by
    intro x hx
    exact (hi ⟨F.ambientDomain.domain.boundaryInclusion.map (F.ribbonEmbedding.map x),
      F.ambientDomain.domain.boundaryInclusion_mem_carrier (F.ribbonEmbedding.map x)⟩).trans
      (S.fiberEmbedding_compact M parameterOne x hx).symm
  have himage : O.nativeEmbedding.map '' O.domain.carrier =
      {y : LGSpace n | φ y.1 ≤ Cplus ^ 2 * β ^ 2 / 2} := by
    rw [O.native_image]
    ext y
    change φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0 ↔ φ y.1 ≤ Cplus ^ 2 * β ^ 2 / 2
    exact sub_nonpos
  have hhitboundary : ∀ x ∈ F.ribbonDomain.domain.carrier,
      φ (O.nativeEmbedding.map (O.domain.boundaryInclusion.map ((j parameterZero).map x))).1 =
        Cplus ^ 2 * β ^ 2 / 2 := by
    intro x _
    exact (Set.ext_iff.mp hboundary _).mp (mem_range_self ((j parameterZero).map x))
  exact H.exists_strictJunction_of_regional_hits F i q (lgManifold n) O.nativeEmbedding α
    ((lgManifold n).isSmoothForm_rankTwoPrimitive
      (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_tailoringFamily_lgManifold I β 1) K)
    hL (fun y => φ y.1) (contMDiff_potentialValue hφ) (Cplus ^ 2 * β ^ 2 / 2) K
    himage (fun y _ => hnd y) G hG hnative hout τ
    (fun x => M.embedding.map ((S.fiberEmbedding M parameterOne).map x))
    hstart htime hhitboundary hhit hwitness
    (S.pair_ribbon_nonempty (P.tailoring.ribbon_nonempty parameterOne) parameterOne)

end FsFltz
