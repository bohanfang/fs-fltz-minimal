import FsFltz.Geometry.OriginalInitialChoicePrefix
import FsFltz.Geometry.TailoringCotangentEndpointRetained

/-!
# Cotangent comparison for every supplied initial pair

Source: `geoemtric-part-fsf.tex`, `thm:target`, lines 352–435;
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 950–973 and
`sec:assembly`, lines 2091–2233. This proves the geometric chain and literal
full-core equality with the original parameter quantifiers. Grading along
the full chain is a separate, still unmet conclusion of `GeometricTarget`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- One common ambient bound and radius suffice for an actual fourteen-arrow
cotangent comparison from every supplied initial pair. The entire terminal
embedded core is literally the FLTZ link. No grading of this path is asserted. -/
theorem ToricInput.exists_arbitrary_initial_cotangent_comparison {n : ℕ}
    (I : ToricInput n) :
    ∃ Aamb R0 : ℝ, AmbientEndBound I Aamb ∧
      max 1 (sublevelMagnitudeSup I Aamb) < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        RatioSetWellDefined I R ∧ (∃ Afib : ℝ, FiberEndBound I Aamb R Afib) ∧
        ∀ Afib : ℝ, FiberEndBound I Aamb R Afib →
          ∀ K : ℝ, K0 I R ≤ K →
            ∀ Aminus A : ℝ, Afib < Aminus →
              ∀ m : RoundingChoice, ∀ initial : InitialPairData I R K Aminus A m,
                ∃ E : CotangentPairData n,
                  ∃ chain : ComparisonChain initial.pair E.pair,
                    chain.length = 14 ∧ E.embeddedCore = fltzLink I := by
  obtain ⟨φEnd, φ, _hstrong, _hEnd1, _hφ, _Dφ, Aamb, Cminus, Cplus, β₀,
    hamb, _hCminus, _hCminusCplus, _hβ₀, hprefix⟩ :=
    I.exists_uniform_original_marked_prefix_strict_cotangent_comparison
  refine ⟨Aamb, Real.exp β₀, hamb, (hprefix β₀ le_rfl).1, ?_⟩
  intro R hR
  have hRpos : 0 < R := (Real.exp_pos β₀).trans_le hR
  have hβ : β₀ ≤ Real.log R := (Real.le_log_iff_exp_le hRpos).mpr hR
  obtain ⟨hlarge, hset, ⟨Afib', hfib', hAfib'⟩, hprefix⟩ := hprefix (Real.log R) hβ
  have hlocal :
      RatioSetWellDefined I (Real.exp (Real.log R)) ∧
      (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp (Real.log R)) Afib) ∧
      ∀ Afib : ℝ, FiberEndBound I Aamb (Real.exp (Real.log R)) Afib →
        ∀ K : ℝ, K0 I (Real.exp (Real.log R)) ≤ K →
          ∀ Aminus A : ℝ, Afib < Aminus →
            ∀ m : RoundingChoice,
              ∀ initial : InitialPairData I (Real.exp (Real.log R)) K Aminus A m,
                ∃ E : CotangentPairData n,
                  ∃ chain : ComparisonChain initial.pair E.pair,
                    chain.length = 14 ∧ E.embeddedCore = fltzLink I := by
    refine ⟨hset, ⟨Afib', hfib'⟩, ?_⟩
    intro Afib hfib K hK Aminus A hAminus m initial
    obtain ⟨K', _hKpos, _hKK', m', _hm', P, _hboundary, S, x₀, L, _hL, j, b,
      H, J, _hlength, _hcore, q, _hq, _hbq, E, C, _hmap, _hribbon,
      _hcompletion, _hid, _hscale, _hb, _hw, hfltz, hlength⟩ := hprefix K hK
    obtain ⟨D, hD, _hdatum, _hfour, _gfour, _height, _hpath⟩ :=
      P.exists_arbitrary_source_chain hamb hlarge hset hK hfib hfib' hAminus hAfib' initial
    refine ⟨E, D.chain.comp ((P.strictHittingChain S x₀ H.deformation J).cons
      (ComparisonStep.identification C)), ?_, hfltz⟩
    simp only [Quiver.Path.length_comp, hD, hlength]
  erw [Real.exp_log hRpos] at hlocal
  exact hlocal

/-- G1, the full G2 quantifier range and the finite geometric comparison with
literal entire-core equality. The remaining target obligation is prescribed
grading transported on that same path, so this is not `GeometricTargetFor`. -/
theorem ToricInput.exists_uniform_cotangent_comparisons {n : ℕ} (I : ToricInput n) :
    AllNonnegativeComplete I ∧
      ∃ Aamb R0 : ℝ, AmbientEndBound I Aamb ∧
        max 1 (sublevelMagnitudeSup I Aamb) < R0 ∧
        ∀ R : ℝ, R0 ≤ R →
          ((ratioSet I R).Nonempty ∧ BddAbove (ratioSet I R) ∧
            ∃ Afib : ℝ, FiberEndBound I Aamb R Afib) ∧
          ∀ Afib : ℝ, FiberEndBound I Aamb R Afib →
            ∀ K : ℝ, K0 I R ≤ K →
              ∀ Aminus A : ℝ, Afib < Aminus → Aminus < A →
                (∃ m : RoundingChoice, GeometricAdmissibleRounding I R K Aminus A m) ∧
                ∀ m : RoundingChoice, GeometricAdmissibleRounding I R K Aminus A m →
                  ∃ initial : InitialPairData I R K Aminus A m,
                    ∃ E : CotangentPairData n,
                      ∃ chain : ComparisonChain initial.pair E.pair,
                        chain.length = 14 ∧ E.embeddedCore = fltzLink I := by
  obtain ⟨Aamb, R0, hamb, hR0, hall⟩ := I.exists_arbitrary_initial_cotangent_comparison
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
  exact ⟨initial, hcomparison Afib hAfib K hK Aminus A hAminus m initial⟩

end FsFltz
