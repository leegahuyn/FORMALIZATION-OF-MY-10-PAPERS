import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CoprimeTorusAlgebra

/-!
# The literal signed Laurent binomials in Paper 4

Physical page 124, (F2), uses U^p + V^A and U^(-p) + V^A. Inverting U
handles the negative exponent. Negating U then carries either odd-p
generator to the negative of U^p - V^A. Hence the actual ideals and
their quotients are identified before applying the primitive
Laurent binomial calculation.
-/

namespace ManuscriptAudit.Paper4SignedTorus

open CoprimeTorusAlgebra (TwoTorus Curve relationIdeal coordinateEquiv)

noncomputable section

variable (R : Type*) [CommRing R]

private abbrev Exponent := ℤ × ℤ

/-- The Laurent monomial U^i V^j in the two-variable torus algebra. -/
def torusMonomial (i j : ℤ) : TwoTorus R :=
  AddMonoidAlgebra.single (i, j) 1

private def signCoeff (i : ℤ) : R := ((i.negOnePow : ℤ) : R)

private theorem signCoeff_zero : signCoeff R 0 = 1 := by
  simp [signCoeff]

private theorem signCoeff_add (i j : ℤ) :
    signCoeff R (i + j) = signCoeff R i * signCoeff R j := by
  simp only [signCoeff, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

private theorem signCoeff_square (i : ℤ) : signCoeff R i * signCoeff R i = 1 := by
  rw [← signCoeff_add, ← two_mul]
  simp [signCoeff]

private theorem signCoeff_odd {p : ℕ} (hp : Odd p) : signCoeff R (p : ℤ) = -1 :=
  (Int.cast_negOnePow_natCast R p).trans hp.neg_one_pow

private def signedMonomials : Multiplicative Exponent →* TwoTorus R where
  toFun v := AddMonoidAlgebra.single v.toAdd (signCoeff R v.toAdd.1)
  map_one' := by
    change AddMonoidAlgebra.single (0 : Exponent) (signCoeff R 0) = 1
    rw [signCoeff_zero, AddMonoidAlgebra.one_def]
  map_mul' v w := by
    change AddMonoidAlgebra.single (v.toAdd + w.toAdd)
      (signCoeff R (v.toAdd.1 + w.toAdd.1)) =
      AddMonoidAlgebra.single v.toAdd (signCoeff R v.toAdd.1) *
        AddMonoidAlgebra.single w.toAdd (signCoeff R w.toAdd.1)
    rw [signCoeff_add, AddMonoidAlgebra.single_mul_single]

private def negateUHom : TwoTorus R →ₐ[R] TwoTorus R :=
  AddMonoidAlgebra.lift R (TwoTorus R) Exponent (signedMonomials R)

private theorem negateUHom_single (v : Exponent) (a : R) :
    negateUHom R (AddMonoidAlgebra.single v a) =
      AddMonoidAlgebra.single v (a * signCoeff R v.1) := by
  rw [negateUHom, AddMonoidAlgebra.lift_single]
  change a • AddMonoidAlgebra.single v (signCoeff R v.1) = _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul]

private theorem negateUHom_comp_self :
    (negateUHom R).comp (negateUHom R) = AlgHom.id R (TwoTorus R) := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro v
  change negateUHom R (negateUHom R (AddMonoidAlgebra.single v 1)) =
    AddMonoidAlgebra.single v 1
  simp only [negateUHom_single, one_mul, signCoeff_square]

/-- Change U to -U and keep V unchanged. -/
def negateU : TwoTorus R ≃ₐ[R] TwoTorus R :=
  AlgEquiv.ofAlgHom (negateUHom R) (negateUHom R)
    (negateUHom_comp_self R) (negateUHom_comp_self R)

theorem negateU_monomial (i j : ℤ) :
    negateU R (torusMonomial R i j) =
      AddMonoidAlgebra.single (i, j) (signCoeff R i) := by
  change negateUHom R (AddMonoidAlgebra.single (i, j) 1) = _
  simp only [negateUHom_single, one_mul]

private def invertFirstExponent : Exponent ≃+ Exponent where
  toFun v := (-v.1, v.2)
  invFun v := (-v.1, v.2)
  left_inv v := by cases v; simp
  right_inv v := by cases v; simp
  map_add' v w := by
    change (-(v.1 + w.1), v.2 + w.2) = (-v.1 + -w.1, v.2 + w.2)
    rw [neg_add]

/-- Invert U and keep V unchanged. -/
def invertU : TwoTorus R ≃ₐ[R] TwoTorus R :=
  AddMonoidAlgebra.domCongr R R invertFirstExponent

theorem invertU_monomial (i j : ℤ) :
    invertU R (torusMonomial R i j) = torusMonomial R (-i) j := by
  unfold invertU torusMonomial
  rw [AddMonoidAlgebra.domCongr_single] <;> rfl

/-- The actual Laurent polynomial printed in (F2).
The Boolean selects the negative exponent when true. -/
def printedRelation (negative : Bool) (p A : ℕ) : TwoTorus R :=
  torusMonomial R (if negative then -(p : ℤ) else (p : ℤ)) 0 + torusMonomial R 0 A

def printedIdeal (negative : Bool) (p A : ℕ) : Ideal (TwoTorus R) :=
  Ideal.span {printedRelation R negative p A}

abbrev PrintedCurve (negative : Bool) (p A : ℕ) :=
  TwoTorus R ⧸ printedIdeal R negative p A

/-- In the negative case, invert U before applying the sign change. -/
def coordinateChange (negative : Bool) : TwoTorus R ≃ₐ[R] TwoTorus R :=
  if negative then (invertU R).trans (negateU R) else negateU R

private theorem negate_positive_relation {p : ℕ} (hp : Odd p) (A : ℕ) :
    negateU R (printedRelation R false p A) =
      -(torusMonomial R p 0 - torusMonomial R 0 A) := by
  change negateU R (torusMonomial R p 0 + torusMonomial R 0 A) = _
  rw [map_add, negateU_monomial, negateU_monomial, signCoeff_odd R hp, signCoeff_zero,
    AddMonoidAlgebra.single_neg]
  unfold torusMonomial
  abel

theorem coordinateChange_relation {p : ℕ} (hp : Odd p) (negative : Bool) (A : ℕ) :
    coordinateChange R negative (printedRelation R negative p A) =
      -(torusMonomial R p 0 - torusMonomial R 0 A) := by
  cases negative
  · exact negate_positive_relation R hp A
  · have h : invertU R (printedRelation R true p A) = printedRelation R false p A := by
      simp [printedRelation, invertU_monomial]
    change negateU R (invertU R (printedRelation R true p A)) = _
    rw [h]
    exact negate_positive_relation R hp A

theorem printedIdeal_map {p : ℕ} (hp : Odd p) (negative : Bool) (A : ℕ) :
    (printedIdeal R negative p A).map (coordinateChange R negative :
      TwoTorus R →+* TwoTorus R) = relationIdeal R p A := by
  unfold printedIdeal
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {coordinateChange R negative (printedRelation R negative p A)} = _
  rw [coordinateChange_relation R hp, Ideal.span_singleton_neg] <;> rfl

/-- The actual literal quotient and the primitive-model quotient are isomorphic. -/
def literalToBinomialEquiv {p : ℕ} (hp : Odd p) (negative : Bool) (A : ℕ) :
    PrintedCurve R negative p A ≃ₐ[R] Curve R p A :=
  Ideal.quotientEquivAlg (printedIdeal R negative p A) (relationIdeal R p A)
    (coordinateChange R negative) (printedIdeal_map R hp negative A).symm

def literalLaurentEquiv {p A : ℕ} (hp : Odd p) (hc : p.Coprime A) (negative : Bool) :
    PrintedCurve R negative p A ≃ₐ[R] LaurentPolynomial R :=
  (literalToBinomialEquiv R hp negative A).trans (coordinateEquiv R hc)

/-- Both of the printed unit-solution models are Laurent lines over the
residue field for the stated range of p and A. -/
def paper4_literal_coordinateEquiv {p A : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p)
    (hA : A = 4 ∨ A = 3 ∨ A = 2) (negative : Bool) :
    PrintedCurve (ZMod p) negative p A ≃ₐ[ZMod p] LaurentPolynomial (ZMod p) := by
  have hOdd := hp.odd_of_ne_two (by omega)
  have hApos : 0 < A := by rcases hA with rfl | rfl | rfl <;> omega
  have hAlt : A < p := by rcases hA with rfl | rfl | rfl <;> omega
  have hCoprime : p.Coprime A :=
    hp.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt hAlt) (Nat.le_of_dvd hApos h))
  exact literalLaurentEquiv (ZMod p) hOdd hCoprime negative

end

end ManuscriptAudit.Paper4SignedTorus

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper4SignedTorus.negateU_monomial,
      ``ManuscriptAudit.Paper4SignedTorus.invertU_monomial,
      ``ManuscriptAudit.Paper4SignedTorus.coordinateChange_relation,
      ``ManuscriptAudit.Paper4SignedTorus.printedIdeal_map,
      ``ManuscriptAudit.Paper4SignedTorus.literalToBinomialEquiv,
      ``ManuscriptAudit.Paper4SignedTorus.literalLaurentEquiv,
      ``ManuscriptAudit.Paper4SignedTorus.paper4_literal_coordinateEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
