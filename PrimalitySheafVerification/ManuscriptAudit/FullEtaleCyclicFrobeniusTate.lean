import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleCyclicUnitTate

/-! Genuine semilinear pullback on the entire untwisted étale tower
intertwines with actual unit Tate pullback by the cyclotomic scalar. -/

namespace ManuscriptAudit.FullEtaleCyclicFrobeniusTate

open AlgebraicGeometry CategoryTheory
open KummerUnitsSheaf EtaleKummerCyclicCoordinates FullEtaleConstantRootHOne
open FullEtaleCyclicUnitTate FullEtaleCyclicFrobeniusLabel
open OpenEtaleUnitHOneComposition PowerTateModule

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (l : ℕ)

private abbrev T (Y : Scheme.{0}) := FullEtaleCyclicHOneLimit.compatible Y l
private abbrev H (Y : Scheme.{0}) := Sheaf.H (fullCoordinateUnitSheaf Y) 1

/-- Pullback on the whole actual compatible system of cyclic étale H¹ classes. -/
def cyclicTatePullback : T l X →+ T l U where
  toFun x := ⟨fun n => constantPullback j (cyclicGroup l n) (x.val n), fun n => by
    let q := reduction l n
    have h := constantPullback_coeff j q (x.val (n + 1))
    exact h.symm.trans (congrArg (constantPullback j (cyclicGroup l n)) (x.property n))⟩
  map_zero' := Subtype.ext (funext fun n => (constantPullback j (cyclicGroup l n)).map_zero)
  map_add' a b := Subtype.ext (funext fun n => (constantPullback j (cyclicGroup l n)).map_add _ _)

variable (k K : Type) [Field k] [Fintype k] [Field K] [Algebra k K] [IsAlgClosed K]
variable [Fact l.Prime] [NeZero (l : K)]
variable (b : X ⟶ Spec (CommRingCat.of K)) (b' : U ⟶ Spec (CommRingCat.of K))
variable (hX : ∀ n : ℕ, Function.Surjective (fun u : (Γ(X, ⊤))ˣ => u ^ (l ^ n)))
variable (hU : ∀ n : ℕ, Function.Surjective (fun u : (Γ(U, ⊤))ˣ => u ^ (l ^ n)))

/-- Actual semilinear Frobenius on unit Tate is exactly the cyclotomic
scalar times the genuine untwisted cyclic pullback, on the prime-adic limit. -/
theorem cyclicTate_cyclotomic (m : ℕ)
    (h : j ≫ b = b' ≫ Spec.map (CommRingCat.ofHom (((FiniteField.frobeniusAlgHom k K) ^ m).toRingHom)))
    (x : T l X) :
    map l (unitPullback j) (cyclicUnitTateEquiv X l b hX x) =
      (Fintype.card k) ^ m • cyclicUnitTateEquiv U l b' hU (cyclicTatePullback j l x) := by
  apply PowerTateModule.ext l (H U)
  intro n
  rw [evaluate_map, map_nsmul]
  apply Subtype.ext
  change unitPullback j
      ((evaluate l (H X) n (cyclicUnitTateEquiv X l b hX x)) : H X) =
    (Fintype.card k) ^ m •
      ((evaluate l (H U) n (cyclicUnitTateEquiv U l b' hU (cyclicTatePullback j l x))) : H U)
  rw [cyclicUnitTateEquiv_value, cyclicUnitTateEquiv_value]
  exact cyclicUnitLabel_pullback k K l j b b' n m h (x.val n)

end

end ManuscriptAudit.FullEtaleCyclicFrobeniusTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleCyclicFrobeniusTate.cyclicTate_cyclotomic
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
