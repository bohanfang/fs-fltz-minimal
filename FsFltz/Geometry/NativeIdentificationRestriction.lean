import FsFltz.Geometry.Identification
import FsFltz.Geometry.BoundaryPresentationBridge
import FsFltz.Geometry.BoundaryIntrinsicEquiv
import FsFltz.Geometry.NativeCompactFormRestriction
import FsFltz.Geometry.NativeRibbonFamilyRestriction

/-!
# Native restriction of prescribed completion identifications

Source: `geoemtric-part-fsf.tex`, smooth extension conventions at 119–122,
`def:chain`, 171–189, and `sec:lean`, 788–814. The actual compact carrier
maps retain the supplied forward and inverse values. Differential pullback
then transports the full constant-scale primitive equation, including at
boundary points. The boundary/ribbon square is retained on the whole ribbon.

These are soundness foundations for supplied identifications, not existence
of a geometric comparison chain or an endpoint core equality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomainDiffeomorph

/-- The prescribed forward and inverse maps restrict to the actual compact
carriers, with their original values on every point. -/
def carrierEquiv {d : ℕ} {D E : CompactDomain d}
    (h : CompactDomainDiffeomorph D E) : D.Point ≃ E.Point where
  toFun x := ⟨h.map x.val, h.maps_source x.property⟩
  invFun y := ⟨h.inverse y.val, h.maps_target y.property⟩
  left_inv x := Subtype.ext (h.left_inverse x.val x.property)
  right_inv y := Subtype.ext (h.right_inverse y.val y.property)

@[simp] theorem carrierEquiv_val {d : ℕ} {D E : CompactDomain d}
    (h : CompactDomainDiffeomorph D E) (x : D.Point) :
    (h.carrierEquiv x).val = h.map x.val := rfl

@[simp] theorem carrierEquiv_symm_val {d : ℕ} {D E : CompactDomain d}
    (h : CompactDomainDiffeomorph D E) (y : E.Point) :
    (h.carrierEquiv.symm y).val = h.inverse y.val := rfl

/-- Neighborhood smoothness gives a native diffeomorphism up to the actual
compact boundary; no global ambient diffeomorphism is required. -/
def nativeDiffeomorph {k : ℕ} {D E : CompactDomain (k + 1)}
    (h : CompactDomainDiffeomorph D E) :
    Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) D.Point E.Point ∞ :=
  { h.carrierEquiv with
    contMDiff_toFun := E.contMDiff_iff_subtype_val.mpr
      (h.smooth_map.comp_contMDiff D.contMDiff_subtype_val
        (fun x => h.contains_source x.property))
    contMDiff_invFun := D.contMDiff_iff_subtype_val.mpr
      (h.smooth_inverse.comp_contMDiff E.contMDiff_subtype_val
        (fun y => h.contains_target y.property)) }

@[simp] theorem nativeDiffeomorph_val {k : ℕ} {D E : CompactDomain (k + 1)}
    (h : CompactDomainDiffeomorph D E) (x : D.Point) :
    (h.nativeDiffeomorph x).val = h.map x.val := rfl

@[simp] theorem nativeDiffeomorph_symm_val {k : ℕ} {D E : CompactDomain (k + 1)}
    (h : CompactDomainDiffeomorph D E) (y : E.Point) :
    (h.nativeDiffeomorph.symm y).val = h.inverse y.val := rfl

/-- The supplied forward neighborhood map produces real open extensions
in every native source and target chart, including at boundary points. -/
theorem nativeDiffeomorph_germs {k : ℕ} {D E : CompactDomain (k + 1)}
    (h : CompactDomainDiffeomorph D E) :
    IntrinsicLiouville.IsLocallyExtendibleNativeMap (k := k) h.nativeDiffeomorph :=
  D.isLocallyExtendibleNativeMap_of_ambientRestriction E h.map h.nativeDiffeomorph
    h.sourceNeighbourhood h.open_source h.contains_source h.smooth_map (fun _ => rfl)

/-- The specified inverse's own neighborhood extension gives the inverse
native chart germs, with no global inverse extension assumption. -/
theorem nativeDiffeomorph_inverse_germs {k : ℕ} {D E : CompactDomain (k + 1)}
    (h : CompactDomainDiffeomorph D E) :
    IntrinsicLiouville.IsLocallyExtendibleNativeMap (k := k) h.nativeDiffeomorph.symm :=
  E.isLocallyExtendibleNativeMap_of_ambientRestriction D h.inverse h.nativeDiffeomorph.symm
    h.targetNeighbourhood h.open_target h.contains_target h.smooth_inverse (fun _ => rfl)

/-- The same prescribed carrier maps give the zero-dimensional native
diffeomorphism, using the discrete atlas of the actual carrier. -/
def nativeZeroDiffeomorph {D E : CompactDomain 0}
    (h : CompactDomainDiffeomorph D E) :
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) D.Point E.Point ∞ :=
  { h.carrierEquiv with
    contMDiff_toFun := contMDiff_of_discreteTopology
    contMDiff_invFun := contMDiff_of_discreteTopology }

@[simp] theorem nativeZeroDiffeomorph_val {D E : CompactDomain 0}
    (h : CompactDomainDiffeomorph D E) (x : D.Point) :
    (h.nativeZeroDiffeomorph x).val = h.map x.val := rfl

@[simp] theorem nativeZeroDiffeomorph_symm_val {D E : CompactDomain 0}
    (h : CompactDomainDiffeomorph D E) (y : E.Point) :
    (h.nativeZeroDiffeomorph.symm y).val = h.inverse y.val := rfl

/-- Every zero-dimensional native coordinate map has an actual globally
smooth real extension. Its model is the zero vector space, so all coordinate
values agree with the constant zero extension. -/
theorem nativeZeroDiffeomorph_chart_extension {D E : CompactDomain 0}
    (h : CompactDomainDiffeomorph D E)
    (e : OpenPartialHomeomorph D.Point (Model 0))
    (a : OpenPartialHomeomorph E.Point (Model 0)) :
    ∃ β : Model 0 → Model 0, ContDiff ℝ ∞ β ∧
      ∀ x, β (e x) = a (h.nativeZeroDiffeomorph x) := by
  refine ⟨fun _ => 0, contDiff_const, ?_⟩
  intro x
  exact PiLp.ext (fun i => Fin.elim0 i)

/-- The inverse zero-dimensional coordinate map has the same actual
smooth real extension property. -/
theorem nativeZeroDiffeomorph_inverse_chart_extension {D E : CompactDomain 0}
    (h : CompactDomainDiffeomorph D E)
    (e : OpenPartialHomeomorph E.Point (Model 0))
    (a : OpenPartialHomeomorph D.Point (Model 0)) :
    ∃ β : Model 0 → Model 0, ContDiff ℝ ∞ β ∧
      ∀ x, β (e x) = a (h.nativeZeroDiffeomorph.symm x) := by
  refine ⟨fun _ => 0, contDiff_const, ?_⟩
  intro x
  exact PiLp.ext (fun i => Fin.elim0 i)

/-- Restriction commutes with actual differential pullback on the full
native tangent spaces, including the compact boundary. -/
theorem restrictForm_pullback {k r : ℕ} {D E : CompactDomain (k + 1)}
    (h : CompactDomainDiffeomorph D E) (η : E.extension.Form r) (x : D.Point) :
    (E.restrictForm η (h.nativeDiffeomorph x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h.nativeDiffeomorph x) =
    D.restrictForm (D.extension.pullback E.extension h.map η) x := by
  have hd₁ := mfderiv_comp (f := h.nativeDiffeomorph)
    (g := (Subtype.val : E.Point → E.extension.Point)) x
    (E.contMDiff_subtype_val.mdifferentiableAt (by simp))
    (h.nativeDiffeomorph.contMDiff.mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp (f := (Subtype.val : D.Point → D.extension.Point))
    (g := h.map) x
    ((h.smooth_map.contMDiffAt (h.open_source.mem_nhds
      (h.contains_source x.property))).mdifferentiableAt (by simp))
    (D.contMDiff_subtype_val.mdifferentiableAt (by simp))
  have hsquare : (Subtype.val : E.Point → E.extension.Point) ∘ h.nativeDiffeomorph =
      h.map ∘ (Subtype.val : D.Point → D.extension.Point) := rfl
  rw [hsquare] at hd₁
  have hd := hd₁.symm.trans hd₂
  ext vs
  simp only [CompactDomain.restrictForm, SmoothManifold.pullback,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  exact congrArg (η (h.map x.val))
    (funext fun j => congrArg (fun A => A (vs j)) hd)

/-- A carrier-wise constant primitive scale survives restriction as an
equality of native one-forms on every full compact tangent space. -/
theorem native_primitive_scaled {k : ℕ} {D E : CompactDomain (k + 1)}
    (h : CompactDomainDiffeomorph D E) (α : D.extension.Form 1)
    (β : E.extension.Form 1) (c : ℝ)
    (hp : ∀ x ∈ D.carrier, D.extension.pullback E.extension h.map β x = c • α x)
    (x : D.Point) :
    (E.restrictForm β (h.nativeDiffeomorph x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h.nativeDiffeomorph x) =
      c • D.restrictForm α x := by
  rw [h.restrictForm_pullback]
  unfold CompactDomain.restrictForm
  rw [hp x.val x.property]
  ext vs
  rfl

/-- In dimension zero every actual native one-form vanishes. Thus the
prescribed carrier diffeomorphism retains every constant primitive scale. -/
theorem nativeZero_primitive_scaled {D E : CompactDomain 0}
    (h : CompactDomainDiffeomorph D E) (α : D.extension.Form 1)
    (β : E.extension.Form 1) (c : ℝ) (x : D.Point) :
    ((β (h.nativeZeroDiffeomorph x).val).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
        (Subtype.val : E.Point → E.extension.Point) (h.nativeZeroDiffeomorph x))).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) h.nativeZeroDiffeomorph x) =
      c • (α x.val).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
          (Subtype.val : D.Point → D.extension.Point) x) := by
  ext vs
  have hz : vs 0 = 0 := PiLp.ext (fun i => Fin.elim0 i)
  have hl := (((β (h.nativeZeroDiffeomorph x).val).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
      (Subtype.val : E.Point → E.extension.Point) (h.nativeZeroDiffeomorph x))).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) h.nativeZeroDiffeomorph x)).map_coord_zero 0 hz
  have hr := ((α x.val).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
      (Subtype.val : D.Point → D.extension.Point) x)).map_coord_zero 0 hz
  simpa only [ContinuousAlternatingMap.smul_apply, hr, smul_zero] using hl

end CompactDomainDiffeomorph

namespace CompactDomain

/-- Conjugate the prescribed boundary map by the actual frontier
diffeomorphisms. Its points are the genuine intrinsic boundary carriers. -/
def nativeBoundaryEquiv {k : ℕ} (D E : CompactDomain (k + 1))
    (b : D.boundary.SmoothEquiv E.boundary) :
    D.intrinsicBoundary.SmoothEquiv E.intrinsicBoundary :=
  (D.boundaryDiffeomorph.symm.trans b).trans E.boundaryDiffeomorph

@[simp] theorem nativeBoundaryEquiv_boundaryDiffeomorph {k : ℕ}
    (D E : CompactDomain (k + 1)) (b : D.boundary.SmoothEquiv E.boundary)
    (x : D.boundary.Point) :
    D.nativeBoundaryEquiv E b (D.boundaryDiffeomorph x) =
      E.boundaryDiffeomorph (b x) := by
  simp [nativeBoundaryEquiv]

/-- The inverse boundary presentation transports the supplied boundary
primitive to the actual differential restriction on the frontier. -/
theorem pullback_boundaryForm_symm {k : ℕ} (D : CompactDomain (k + 1))
    (α : D.extension.Form 1) :
    D.intrinsicBoundary.pullback D.boundary D.boundaryDiffeomorph.symm
      (D.boundaryForm α) = D.intrinsicBoundaryForm α := by
  have h := SmoothManifold.pullback_comp D.intrinsicBoundary D.boundary
    D.intrinsicBoundary
    (D.boundaryDiffeomorph.symm.contMDiff.mdifferentiable (by simp))
    (D.boundaryDiffeomorph.contMDiff.mdifferentiable (by simp))
    (D.intrinsicBoundaryForm α)
  rw [D.pullback_intrinsicBoundaryForm] at h
  have he : D.boundaryDiffeomorph ∘ D.boundaryDiffeomorph.symm = id := by
    funext x
    exact D.boundaryDiffeomorph.apply_symm_apply x
  rw [he, SmoothManifold.pullback_id] at h
  exact h.symm

/-- A full boundary primitive equation survives conjugation to the actual
intrinsic boundary. The conformal factor is the same pointwise function. -/
theorem nativeBoundaryEquiv_primitive {k : ℕ} (D E : CompactDomain (k + 1))
    (b : D.boundary.SmoothEquiv E.boundary)
    (α : D.extension.Form 1) (β : E.extension.Form 1) (c : D.boundary.Point → ℝ)
    (hp : D.boundary.pullback E.boundary b (E.boundaryForm β) =
      fun x => c x • D.boundaryForm α x) :
    D.intrinsicBoundary.pullback E.intrinsicBoundary (D.nativeBoundaryEquiv E b)
      (E.intrinsicBoundaryForm β) =
      fun x => c (D.boundaryDiffeomorph.symm x) • D.intrinsicBoundaryForm α x := by
  have h₁ := SmoothManifold.pullback_comp D.intrinsicBoundary D.boundary E.boundary
    (D.boundaryDiffeomorph.symm.contMDiff.mdifferentiable (by simp))
    (b.contMDiff.mdifferentiable (by simp)) (E.boundaryForm β)
  have h₂ := SmoothManifold.pullback_comp D.intrinsicBoundary E.boundary E.intrinsicBoundary
    ((b.contMDiff.comp D.boundaryDiffeomorph.symm.contMDiff).mdifferentiable (by simp))
    (E.boundaryDiffeomorph.contMDiff.mdifferentiable (by simp))
    (E.intrinsicBoundaryForm β)
  rw [E.pullback_intrinsicBoundaryForm, h₁, hp] at h₂
  change D.intrinsicBoundary.pullback E.intrinsicBoundary
    (E.boundaryDiffeomorph ∘ (b ∘ D.boundaryDiffeomorph.symm))
    (E.intrinsicBoundaryForm β) = _
  rw [h₂]
  funext x
  have h := congrFun (D.pullback_boundaryForm_symm α) x
  unfold SmoothManifold.pullback at h ⊢
  rw [← h]
  ext vs
  rfl

end CompactDomain

namespace CompletionIdentification

variable {n : ℕ} {P Q : WitnessedPair n}

/-- The full ribbon square holds on the actual compact carriers in every
dimension, including the zero-dimensional ribbon. -/
theorem native_ribbon_square (I : CompletionIdentification P Q)
    (x : P.ribbonDomain.domain.Point) :
    I.boundaryEquiv (P.ribbonEmbedding.map x.val) =
      Q.ribbonEmbedding.map (I.ribbonEquiv.carrierEquiv x).val :=
  I.ribbon_square x.val x.property

/-- The same prescribed infinity map, expressed on the actual native
frontiers of the compact ambient domains. -/
def nativeBoundaryEquiv {m : ℕ} {P Q : WitnessedPair (m + 1)}
    (I : CompletionIdentification P Q) :
    P.ambientDomain.domain.intrinsicBoundary.SmoothEquiv
      Q.ambientDomain.domain.intrinsicBoundary :=
  P.ambientDomain.domain.nativeBoundaryEquiv Q.ambientDomain.domain I.boundaryEquiv

/-- The native infinity map has the exact original contact primitive
factor; the shift is read at the same native boundary point. -/
theorem native_boundary_primitive {m : ℕ} {P Q : WitnessedPair (m + 1)}
    (I : CompletionIdentification P Q) :
    P.ambientDomain.domain.intrinsicBoundary.pullback
      Q.ambientDomain.domain.intrinsicBoundary I.nativeBoundaryEquiv
      (Q.ambientDomain.domain.intrinsicBoundaryForm Q.ambientDomain.liouville.primitive) =
      fun x => Real.exp (-I.shift (P.ambientDomain.domain.boundaryDiffeomorph.symm x)) •
        P.ambientDomain.domain.intrinsicBoundaryForm P.ambientDomain.liouville.primitive x :=
  P.ambientDomain.domain.nativeBoundaryEquiv_primitive Q.ambientDomain.domain
    I.boundaryEquiv P.ambientDomain.liouville.primitive Q.ambientDomain.liouville.primitive
    (fun x => Real.exp (-I.shift x)) I.boundary_primitive

/-- Conjugating the boundary presentation preserves the induced-end
equation for the same strict ambient completion map. -/
theorem native_induced_at_infinity {m : ℕ} {P Q : WitnessedPair (m + 1)}
    (I : CompletionIdentification P Q)
    (x : P.ambientDomain.domain.intrinsicBoundary.Point) :
    ∃ r0 : ℝ, ∀ r : ℝ, r0 ≤ r →
      I.ambientEquiv (P.ambientCompletion.endMap
        (P.ambientDomain.domain.boundaryDiffeomorph.symm x, r)) =
      Q.ambientCompletion.endMap
        (Q.ambientDomain.domain.boundaryDiffeomorph.symm (I.nativeBoundaryEquiv x),
          r + I.shift (P.ambientDomain.domain.boundaryDiffeomorph.symm x)) := by
  simpa [nativeBoundaryEquiv, CompactDomain.nativeBoundaryEquiv] using
    I.induced_at_infinity (P.ambientDomain.domain.boundaryDiffeomorph.symm x)

/-- The entire ribbon square commutes in the actual native frontier.
The carrier equivalence also covers the dimension-one, zero ribbon case. -/
theorem native_frontier_ribbon_square {m : ℕ} {P Q : WitnessedPair (m + 1)}
    (I : CompletionIdentification P Q) (x : P.ribbonDomain.domain.Point) :
    I.nativeBoundaryEquiv (P.ambientDomain.domain.boundaryDiffeomorph
      (P.ribbonEmbedding.map x.val)) =
      Q.ambientDomain.domain.boundaryDiffeomorph
        (Q.ribbonEmbedding.map (I.ribbonEquiv.carrierEquiv x).val) := by
  rw [nativeBoundaryEquiv,
    CompactDomain.nativeBoundaryEquiv_boundaryDiffeomorph, I.native_ribbon_square]

/-- In positive ribbon dimension the native ribbon diffeomorphism retains
the specified constant positive scale on every full compact covector. -/
theorem native_ribbon_primitive {m : ℕ} {P Q : WitnessedPair (m + 2)}
    (I : CompletionIdentification P Q) (x : P.ribbonDomain.domain.Point) :
    (Q.ribbonDomain.domain.restrictForm Q.ribbonDomain.liouville.primitive
      (I.ribbonEquiv.nativeDiffeomorph x)).compContinuousLinearMap
      (mfderiv (𝓡∂ ((2 * m + 1) + 1)) (𝓡∂ ((2 * m + 1) + 1))
        I.ribbonEquiv.nativeDiffeomorph x) =
      I.scale • P.ribbonDomain.domain.restrictForm P.ribbonDomain.liouville.primitive x :=
  I.ribbonEquiv.native_primitive_scaled P.ribbonDomain.liouville.primitive
    Q.ribbonDomain.liouville.primitive I.scale I.ribbon_primitive x

/-- The prescribed dimension-one identification has the full native
zero-ribbon primitive-scale equation, with the same specified scale. -/
theorem native_zero_ribbon_primitive {P Q : WitnessedPair 1}
    (I : CompletionIdentification P Q) (x : P.ribbonDomain.domain.Point) :
    ((Q.ribbonDomain.liouville.primitive (I.ribbonEquiv.nativeZeroDiffeomorph x).val).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
        (Subtype.val : Q.ribbonDomain.domain.Point → Q.ribbonDomain.domain.extension.Point)
        (I.ribbonEquiv.nativeZeroDiffeomorph x))).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) I.ribbonEquiv.nativeZeroDiffeomorph x) =
      I.scale • (P.ribbonDomain.liouville.primitive x.val).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
          (Subtype.val : P.ribbonDomain.domain.Point → P.ribbonDomain.domain.extension.Point) x) :=
  I.ribbonEquiv.nativeZero_primitive_scaled P.ribbonDomain.liouville.primitive
    Q.ribbonDomain.liouville.primitive I.scale x

end CompletionIdentification
end FsFltz.Geometry
