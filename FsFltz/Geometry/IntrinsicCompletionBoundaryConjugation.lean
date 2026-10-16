import FsFltz.Geometry.IntrinsicNativePairIdentification

/-!
# Boundary coordinates under exact native completion comparisons

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199, and
`sec:lean`, lines 803–814. The original sources are smooth manifolds with
their actual primitives and end parametrizations; no represented completion
record is required on either native source. Strict same-radius comparisons
transport an arbitrary strict original map, including its nonzero shifts.
Only the original eventual end law and the nonnegative-radius comparison
laws are used. The represented all-real end law, boundary map and contact
primitive are derived. The full-ribbon consumer uses the original boundary
square and actual native compact inclusion squares.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

section NativeSources

variable {d e a b r s : ℕ}
  (X : SmoothManifold d) (Y : SmoothManifold e)
  (B : SmoothManifold r) (B' : SmoothManifold s)
  {D : LiouvilleDomain a} {E : LiouvilleDomain b}
  (K : Completion D) (K' : Completion E)
  (α : X.Form 1) (β : Y.Form 1)
  (S : X.SmoothEquiv K.ambient.manifold)
  (S' : Y.SmoothEquiv K'.ambient.manifold)
  (hS : X.pullback K.ambient.manifold S K.ambient.primitive = α)
  (hS' : Y.pullback K'.ambient.manifold S' K'.ambient.primitive = β)
  (Ψ : X.SmoothEquiv Y) (hΨ : X.pullback Y Ψ β = α)

include hS hS' hΨ in
/-- The actual conjugated original map preserves the represented primitive.
Its native comparison maps and original map are retained literally. -/
theorem primitive_conjugate :
    K.ambient.manifold.pullback K'.ambient.manifold ((S.symm.trans Ψ).trans S')
      K'.ambient.primitive = K.ambient.primitive := by
  change K.ambient.manifold.pullback K'.ambient.manifold
    (S' ∘ (Ψ ∘ S.symm)) K'.ambient.primitive = _
  rw [K.ambient.manifold.pullback_comp Y K'.ambient.manifold
    (fun x => (Ψ.contMDiff.comp S.symm.contMDiff).mdifferentiableAt (by simp))
    (fun x => S'.contMDiff.mdifferentiableAt (by simp)), hS']
  rw [K.ambient.manifold.pullback_comp X Y
    (fun x => S.symm.contMDiff.mdifferentiableAt (by simp))
    (fun x => Ψ.contMDiff.mdifferentiableAt (by simp)), hΨ, ← hS]
  exact X.pullback_symm_pullback K.ambient.manifold S K.ambient.primitive

variable
  (endX : B.Point × ℝ → X.Point) (endY : B'.Point × ℝ → Y.Point)
  (bS : B.SmoothEquiv D.domain.boundary)
  (bS' : B'.SmoothEquiv E.domain.boundary)
  (hendS : ∀ x t, 0 ≤ t → S (endX (x, t)) = K.endMap (bS x, t))
  (hendS' : ∀ x t, 0 ≤ t → S' (endY (x, t)) = K'.endMap (bS' x, t))
  (ψ : B.SmoothEquiv B') (shift : B.Point → ℝ)
  (hendΨ : ∀ x, ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
    Ψ (endX (x, t)) = endY (ψ x, t + shift x))

include hS hS' hΨ hendS hendS' hendΨ in
/-- The original eventual end law and exact outward comparison laws derive
the conjugated end law at every real represented radius. A sufficiently
large radius puts both original points in their outward ends; strict flow
transport then extends the resulting law to all real times. -/
theorem conjugated_endMap (y : D.domain.boundary.Point) (t : ℝ) :
    ((S.symm.trans Ψ).trans S') (K.endMap (y, t)) =
      K'.endMap (bS' (ψ (bS.symm y)), t + shift (bS.symm y)) := by
  have hp := K.primitive_conjugate X Y K' α β S S' hS hS' Ψ hΨ
  apply K.map_endMap_of_eventually K' ((S.symm.trans Ψ).trans S') hp
    y (bS' (ψ (bS.symm y))) (shift (bS.symm y))
  obtain ⟨t₀, ht₀⟩ := hendΨ (bS.symm y)
  refine ⟨max t₀ (max 0 (-shift (bS.symm y))), ?_⟩
  intro u hu
  have hu₀ : t₀ ≤ u := (le_max_left _ _).trans hu
  have hu_nonneg : 0 ≤ u := (le_max_left 0 _).trans ((le_max_right _ _).trans hu)
  have hu_shift : 0 ≤ u + shift (bS.symm y) := by
    have h := (le_max_right 0 (-shift (bS.symm y))).trans
      ((le_max_right _ _).trans hu)
    linarith
  have hsource := hendS (bS.symm y) u hu_nonneg
  rw [bS.apply_symm_apply] at hsource
  change S' (Ψ (S.symm (K.endMap (y, u)))) = _
  rw [← hsource, S.symm_apply_apply, ht₀ u hu₀,
    hendS' (ψ (bS.symm y)) (u + shift (bS.symm y)) hu_shift]

include hS hS' hΨ hendS hendS' hendΨ in
/-- The induced boundary diffeomorphism and radial shift of the actual
conjugated original map are exactly the transported native coordinates.
Their contact primitive law is derived from the strict ambient map. -/
theorem boundaryCoordinates_conjugate
    (hshift : ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, ℝ) ∞ shift) :
    let F := (S.symm.trans Ψ).trans S'
    let ψrep := (bS.symm.trans ψ).trans bS'
    let srep := shift ∘ bS.symm
    ContMDiff 𝓘(ℝ, Model (a - 1)) 𝓘(ℝ, ℝ) ∞ srep ∧
      (∀ y t, F (K.endMap (y, t)) = K'.endMap (ψrep y, t + srep y)) ∧
      D.domain.boundary.pullback E.domain.boundary ψrep
        (E.domain.boundaryForm E.liouville.primitive) =
        fun y => Real.exp (-srep y) • D.domain.boundaryForm D.liouville.primitive y := by
  let F := (S.symm.trans Ψ).trans S'
  let ψrep := (bS.symm.trans ψ).trans bS'
  let srep := shift ∘ bS.symm
  have hs : ContMDiff 𝓘(ℝ, Model (a - 1)) 𝓘(ℝ, ℝ) ∞ srep :=
    hshift.comp bS.symm.contMDiff
  have he : ∀ y t, F (K.endMap (y, t)) = K'.endMap (ψrep y, t + srep y) :=
    K.conjugated_endMap X Y B B' K' α β S S' hS hS' Ψ hΨ
      endX endY bS bS' hendS hendS' ψ shift hendΨ
  exact ⟨hs, he, K.boundary_primitive_of_endMap K' F
    (K.primitive_conjugate X Y K' α β S S' hS hS' Ψ hΨ) ψrep srep hs he⟩

end NativeSources

end Completion

namespace CompletionIdentification

/-- An original full-ribbon boundary square transports through the retained
native completion comparisons to a permitted identification of the actual
represented pairs. The original ambient map may have arbitrary radial shift.
The compact ribbon map is the one supplied by the native compact-map producer;
its native carrier equation, scale and the literal inclusion squares are used
on the whole carrier. No encoded trajectory or represented ribbon square is
an input. Generic compact maps include zero-dimensional and empty ribbons. -/
theorem exists_of_nativeBoundaryConjugation {n d e r s : ℕ}
    (P Q : WitnessedPair n)
    (X : SmoothManifold d) (Y : SmoothManifold e)
    (B : SmoothManifold r) (B' : SmoothManifold s)
    (α : X.Form 1) (β : Y.Form 1)
    (S : X.SmoothEquiv P.ambientCompletion.ambient.manifold)
    (S' : Y.SmoothEquiv Q.ambientCompletion.ambient.manifold)
    (hS : X.pullback P.ambientCompletion.ambient.manifold S
      P.ambientCompletion.ambient.primitive = α)
    (hS' : Y.pullback Q.ambientCompletion.ambient.manifold S'
      Q.ambientCompletion.ambient.primitive = β)
    (Ψ : X.SmoothEquiv Y) (hΨ : X.pullback Y Ψ β = α)
    (endX : B.Point × ℝ → X.Point) (endY : B'.Point × ℝ → Y.Point)
    (bS : B.SmoothEquiv P.ambientDomain.domain.boundary)
    (bS' : B'.SmoothEquiv Q.ambientDomain.domain.boundary)
    (hendS : ∀ x t, 0 ≤ t →
      S (endX (x, t)) = P.ambientCompletion.endMap (bS x, t))
    (hendS' : ∀ x t, 0 ≤ t →
      S' (endY (x, t)) = Q.ambientCompletion.endMap (bS' x, t))
    (ψ : B.SmoothEquiv B') (shift : B.Point → ℝ)
    (hshift : ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, ℝ) ∞ shift)
    (hendΨ : ∀ x, ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      Ψ (endX (x, t)) = endY (ψ x, t + shift x))
    {R R' : Type*}
    (eR : R → P.ribbonDomain.domain.Point)
    (eR' : R' → Q.ribbonDomain.domain.Point)
    (heR : Function.Surjective eR) (h : R → R')
    (j : R → B.Point) (j' : R' → B'.Point)
    (hj : ∀ x, P.ribbonEmbedding.map (eR x).val = bS (j x))
    (hj' : ∀ y, Q.ribbonEmbedding.map (eR' y).val = bS' (j' y))
    (horiginal : ∀ x, ψ (j x) = j' (h x))
    (g : CompactDomainDiffeomorph P.ribbonDomain.domain Q.ribbonDomain.domain)
    (hg : ∀ x, g.map (eR x).val = (eR' (h x)).val)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x ∈ P.ribbonDomain.domain.carrier,
      P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension g.map
        Q.ribbonDomain.liouville.primitive x = c • P.ribbonDomain.liouville.primitive x) :
    ∃ I : CompletionIdentification P Q,
      I.ambientEquiv = (S.symm.trans Ψ).trans S' ∧
      I.ribbonEquiv = g ∧ I.scale = c ∧
      I.boundaryEquiv = (bS.symm.trans ψ).trans bS' ∧
      I.shift = shift ∘ bS.symm := by
  let F := (S.symm.trans Ψ).trans S'
  let ψrep := (bS.symm.trans ψ).trans bS'
  let srep := shift ∘ bS.symm
  obtain ⟨hs, hend, hp⟩ := P.ambientCompletion.boundaryCoordinates_conjugate
    X Y B B' Q.ambientCompletion α β S S' hS hS' Ψ hΨ
      endX endY bS bS' hendS hendS' ψ shift hendΨ hshift
  have hsquare (z : P.ribbonDomain.domain.extension.Point)
      (hz : z ∈ P.ribbonDomain.domain.carrier) :
      ψrep (P.ribbonEmbedding.map z) = Q.ribbonEmbedding.map (g.map z) := by
    obtain ⟨x, hx⟩ := heR ⟨z, hz⟩
    have hx' : (eR x).val = z := congrArg Subtype.val hx
    rw [← hx', hg, hj]
    change bS' (ψ (bS.symm (bS (j x)))) = _
    rw [bS.symm_apply_apply, horiginal, hj']
  let I : CompletionIdentification P Q :=
    { ambientEquiv := F
      primitive := P.ambientCompletion.primitive_conjugate
        X Y Q.ambientCompletion α β S S' hS hS' Ψ hΨ
      boundaryEquiv := ψrep
      shift := srep
      smooth_shift := hs
      induced_at_infinity := fun x => ⟨0, fun t _ => hend x t⟩
      boundary_primitive := hp
      ribbonEquiv := g
      scale := c
      positive_scale := hc
      ribbon_primitive := hscale
      ribbon_square := hsquare }
  exact ⟨I, rfl, rfl, rfl, rfl, rfl⟩

end CompletionIdentification
end FsFltz.Geometry
