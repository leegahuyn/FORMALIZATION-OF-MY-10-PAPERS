import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Polynomial.Laurent

/-!
# The coordinate algebra of the punctured cusp

For the cusp in Paper 2, the principal open \(D(t^2)\) has coordinate
algebra \(K[t,t^{-1}]\). The map is induced by the polynomial inclusion
into the Laurent polynomials. This identifies the algebra of the open
subset used in the localization comparison.
-/

namespace ManuscriptAudit.CuspPunctured

open Polynomial

noncomputable section

variable (K : Type*) [CommRing K]

/-- The coordinate subalgebra \(K[t^2,t^3]\) of \(K[t]\). -/
abbrev CuspSubalgebra : Subalgebra K (Polynomial K) :=
  Algebra.adjoin K ({(Polynomial.X : Polynomial K) ^ 2, Polynomial.X ^ 3} :
    Set (Polynomial K))

/-- The coordinate \(t^2\) in the cusp algebra. -/
abbrev cuspSquare : CuspSubalgebra K :=
  ⟨(Polynomial.X : Polynomial K) ^ 2, Algebra.subset_adjoin (by simp)⟩

private theorem X_pow_mem_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    (Polynomial.X : Polynomial K) ^ n ∈ CuspSubalgebra K := by
  have h2 : (Polynomial.X : Polynomial K) ^ 2 ∈ CuspSubalgebra K :=
    (cuspSquare K).property
  have h3 : (Polynomial.X : Polynomial K) ^ 3 ∈ CuspSubalgebra K :=
    Algebra.subset_adjoin (by simp)
  by_cases heven : n % 2 = 0
  · have hform : n = 2 * (n / 2) := by omega
    rw [hform, pow_mul]
    exact (CuspSubalgebra K).pow_mem h2 _
  · have hform : n = 3 + 2 * ((n - 3) / 2) := by omega
    rw [hform, pow_add, pow_mul]
    exact (CuspSubalgebra K).mul_mem h3 ((CuspSubalgebra K).pow_mem h2 _)

private theorem mul_X_pow_mem (g : Polynomial K) (n : ℕ) (hn : 2 ≤ n) :
    g * Polynomial.X ^ n ∈ CuspSubalgebra K := by
  rw [← Polynomial.sum_C_mul_X_pow_eq g, Polynomial.sum, Finset.sum_mul]
  apply (CuspSubalgebra K).sum_mem
  intro k _
  rw [mul_assoc, ← pow_add, Polynomial.C_eq_algebraMap]
  exact (CuspSubalgebra K).mul_mem ((CuspSubalgebra K).algebraMap_mem _)
    (X_pow_mem_of_two_le K (k + n) (by omega))

private theorem cuspSquare_pow_coe (n : ℕ) :
    (((cuspSquare K) ^ n : CuspSubalgebra K) : Polynomial K) =
      (Polynomial.X : Polynomial K) ^ (2 * n) := by
  change ((Polynomial.X : Polynomial K) ^ 2) ^ n = Polynomial.X ^ (2 * n)
  exact (pow_mul _ _ _).symm

private def inclusionToLaurent : CuspSubalgebra K →ₐ[K] LaurentPolynomial K :=
  Polynomial.toLaurentAlg.comp (CuspSubalgebra K).val

/-- Inverting \(t^2\) in \(K[t^2,t^3]\) gives \(K[t,t^{-1}]\)
as a \(K\)-algebra. -/
noncomputable def paper2_cusp_punctured_coordinate_equiv :
    Localization.Away (cuspSquare K) ≃ₐ[K] LaurentPolynomial K := by
  letI : Algebra (CuspSubalgebra K) (LaurentPolynomial K) :=
    (inclusionToLaurent K).toRingHom.toAlgebra
  letI : IsScalarTower K (CuspSubalgebra K) (LaurentPolynomial K) :=
    IsScalarTower.of_algebraMap_eq fun a => ((inclusionToLaurent K).commutes a).symm
  letI : IsLocalization.Away (cuspSquare K) (LaurentPolynomial K) :=
    { map_units := by
        rintro ⟨s, hs⟩
        obtain ⟨n, rfl⟩ := hs
        change IsUnit (Polynomial.toLaurent
          (((cuspSquare K) ^ n : CuspSubalgebra K) : Polynomial K))
        rw [cuspSquare_pow_coe, Polynomial.toLaurent_X_pow]
        exact LaurentPolynomial.isUnit_T _
      surj := by
        intro f
        obtain ⟨n, g, hg⟩ := LaurentPolynomial.exists_T_pow f
        refine ⟨(⟨g * Polynomial.X ^ (n + 2), mul_X_pow_mem K g _ (by omega)⟩,
          ⟨(cuspSquare K) ^ (n + 1), ⟨n + 1, rfl⟩⟩), ?_⟩
        change f * Polynomial.toLaurent
          (((cuspSquare K) ^ (n + 1) : CuspSubalgebra K) : Polynomial K) =
          Polynomial.toLaurent (g * Polynomial.X ^ (n + 2))
        have hindex : ((2 * (n + 1) : ℕ) : ℤ) =
            (n : ℤ) + ((n + 2 : ℕ) : ℤ) := by omega
        calc
          _ = f * LaurentPolynomial.T ((2 * (n + 1) : ℕ) : ℤ) := by
            rw [cuspSquare_pow_coe, Polynomial.toLaurent_X_pow]
          _ = f * LaurentPolynomial.T (n : ℤ) *
              LaurentPolynomial.T ((n + 2 : ℕ) : ℤ) := by
            rw [LaurentPolynomial.mul_T_assoc, hindex]
          _ = Polynomial.toLaurent (g * Polynomial.X ^ (n + 2)) := by
            rw [map_mul, Polynomial.toLaurent_X_pow, hg]
      exists_of_eq := by
        intro a b h
        change Polynomial.toLaurent (a : Polynomial K) =
          Polynomial.toLaurent (b : Polynomial K) at h
        have hab : a = b := Subtype.ext (Polynomial.toLaurent_injective h)
        exact ⟨1, by rw [hab]⟩ }
  exact (Localization.algEquiv (LaurentPolynomial K)
    (Submonoid.powers (cuspSquare K))).restrictScalars K

end

end ManuscriptAudit.CuspPunctured

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CuspPunctured.paper2_cusp_punctured_coordinate_equiv
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
