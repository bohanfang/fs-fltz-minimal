import FsFltz.Geometry.TailoringRibbonLiouvilleFamily

/-!
# Common native restriction of an outward primitive family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169;
`geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009.
The same compact carrier is retained while its extension is restricted to
one common symplectic neighborhood. Localized completions are constructed
for the resulting actual primitive and canonical field families.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.CompactDomain
open SmoothManifold

/-- Restrict the native extension once, preserving the supplied compact carrier
and constructing actual Liouville structures and localized completions for the
same jointly smooth outward primitive family. -/
theorem exists_restricted_liouvilleFamily_of_outwardPrimitiveFamily
    {d : ℕ} (D : CompactDomain d) (μ : Parameter → D.extension.Form 1)
    (hμ : D.extension.IsSmoothIntervalFormFamily μ)
    (O : TopologicalSpace.Opens D.extension.Point) (hDO : D.carrier ⊆ O)
    (hsymplectic : ∀ t : Parameter,
      D.extension.IsSymplecticOn (D.extension.exteriorDerivative (μ t)) O)
    (hout : ∀ (t : Parameter) (x : D.extension.Point) (hx : x ∈ frontier D.carrier),
      0 < D.extension.scalarDerivative (D.defining x hx).rho x
        (D.extension.liouvilleVector (μ t) x)) :
    ∃ Λ : Parameter → LiouvilleStructure (D.restrict O hDO),
      let E := D.restrict O hDO
      (∀ t, (Λ t).primitive = E.extension.pullback D.extension Subtype.val (μ t)) ∧
      (∀ t, (Λ t).field = E.extension.liouvilleVector (Λ t).primitive) ∧
      E.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) ∧
      E.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ t).field) ∧
      (∀ t : Parameter, E.extension.IsSymplecticOn
        (E.extension.exteriorDerivative (Λ t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily E Λ) := by
  let E := D.restrict O hDO
  let μ' : Parameter → E.extension.Form 1 :=
    fun t => E.extension.pullback D.extension Subtype.val (μ t)
  have hsm (t : Parameter) : D.extension.IsSmoothForm (μ t) :=
    D.extension.isSmoothForm_of_isSmoothIntervalFormFamily μ hμ t
  have hsm' (t : Parameter) : E.extension.IsSmoothForm (μ' t) :=
    E.extension.isSmoothForm_pullback_one D.extension
      (D.extension.restrictInclusion O).map (μ t) (hsm t)
  have hnd' (t : Parameter) (x : E.extension.Point) :
      E.extension.Nondegenerate (E.extension.exteriorDerivative (μ' t)) x := by
    intro v hv
    apply (hsymplectic t).2.2 x.val x.property v
    intro w
    have heq := hv w
    unfold evalTwo at heq ⊢
    rw [D.extension.exteriorDerivative_restrict O (μ t) (hsm t) x] at heq
    exact heq
  have hglobal (t : Parameter) : E.extension.IsSymplecticOn
      (E.extension.exteriorDerivative (μ' t)) univ :=
    (E.extension.isSymplecticOn_exteriorDerivative_iff _ (hsm' t) _).mpr
      (fun x _ => hnd' t x)
  have hfield (t : Parameter) (x : E.extension.Point) :
      E.extension.liouvilleVector (μ' t) x = D.extension.liouvilleVector (μ t) x.val := by
    apply E.extension.liouvilleVector_eq (μ' t) x (hnd' t x)
    intro v
    dsimp only [μ']
    unfold evalTwo evalOne
    erw [D.extension.exteriorDerivative_restrict O (μ t) (hsm t) x,
      D.extension.pullback_restrict_val O (μ t) x]
    exact D.extension.liouvilleVector_contraction (μ t) x.val
      (D.extension.liouvilleEquation_exists (μ t) x.val
        ((hsymplectic t).2.2 x.val x.property)) v
  let Λ : Parameter → LiouvilleStructure E := fun t =>
    { primitive := μ' t
      smooth_primitive := hsm' t
      symplectic := ⟨(hglobal t).1, fun x _ => (hglobal t).2.1 x (mem_univ _),
        fun x _ => (hglobal t).2.2 x (mem_univ _)⟩
      field := E.extension.liouvilleVector (μ' t)
      smooth_field := E.extension.isSmoothVectorField_liouvilleVector _ (hsm' t) (hnd' t)
      contraction := fun x _ => E.extension.liouvilleVector_contraction _ x
        (E.extension.liouvilleEquation_exists _ x (hnd' t x))
      outward := by
        intro x hx
        have hx' : x.val ∈ frontier D.carrier := by
          rw [D.frontier_restrict_carrier O] at hx
          exact hx
        let B := D.defining x.val hx'
        have hρ := (B.smooth_rho.contMDiffAt
          (B.open_neighbourhood.mem_nhds B.mem_neighbourhood)).mdifferentiableAt (by simp)
        change (0 : ℝ) < (show ℝ from mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ)
          (fun y : O => B.rho y.val) x (E.extension.liouvilleVector (μ' t) x))
        rw [hfield t x]
        have hchain := mfderiv_comp (f := (Subtype.val : O → D.extension.Point))
          (g := B.rho) x hρ
          ((D.extension.restrictInclusion O).map.contMDiff.mdifferentiableAt (by simp))
        erw [D.extension.mfderiv_restrict_val O x] at hchain
        exact (congrArg (fun T => (T (D.extension.liouvilleVector (μ t) x.val) : ℝ))
          hchain).trans_gt (hout t x.val hx') }
  have hΛ : E.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) :=
    E.extension.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family D.extension
      (fun _ x => x.val) ((_root_.contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).comp contMDiff_snd) μ hμ
  have hΛfield : E.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ t).field) :=
    E.extension.isSmoothIntervalVectorFieldFamily_liouvilleVector μ' hΛ hnd'
  exact ⟨Λ, fun _ => rfl, fun _ => rfl, hΛ, hΛfield, hglobal,
    E.exists_smooth_localizedCompletionFamily_of_liouvilleFamily Λ hΛ⟩

end FsFltz.Geometry.CompactDomain
