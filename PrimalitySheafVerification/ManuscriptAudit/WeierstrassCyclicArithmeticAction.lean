import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleCyclicFrobeniusTate
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleHOnePadic
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassArithmeticFrobeniusScheme
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveKummer

/-! Arithmetic Frobenius acts on the actual prime-adic untwisted étale
cohomology of the geometric Weierstrass scheme, with its literal Kummer twist. -/

namespace ManuscriptAudit.WeierstrassCyclicArithmeticAction

open AlgebraicGeometry CategoryTheory
open FullEtaleHOnePadic FullEtaleCyclicFrobeniusTate FullEtaleConstantRootHOne
open FullEtaleCyclicUnitTate OpenEtaleUnitHOneComposition EtaleKummerCyclicCoordinates
open WeierstrassProjectiveClosure WeierstrassArithmeticFrobeniusScheme
open WeierstrassProjectiveKummer PowerTateModule KummerUnitsSheaf
open scoped Padic

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (l : ℕ) [Fact l.Prime]

/-- Actual pullback on the cyclic étale tower is linear over the prime-adic integers. -/
def cyclicPullbackLinear : CyclicHOne X l →ₗ[ℤ_[l]] CyclicHOne U l where
  toFun := cyclicTatePullback j l
  map_add' := (cyclicTatePullback j l).map_add
  map_smul' r a := by
    apply Subtype.ext
    funext n
    let f := constantPullback j (cyclicGroup l n)
    change f (PadicInt.toZModPow n r • a.val n) = PadicInt.toZModPow n r • f (a.val n)
    exact (f.toZModLinearMap (l ^ n)).map_smul (PadicInt.toZModPow n r) (a.val n)

variable (k K : Type) [Field k] [Fintype k] [Field K] [Algebra k K] [IsAlgClosed K] [NeZero (l : K)]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]

private abbrev V {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := W.baseChange K
private abbrev Y {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := projectiveScheme (V K W)
private abbrev φ := (projectiveFrobenius k K W).hom

private theorem globalPowers (Q : WeierstrassCurve.Affine K) [Q.IsElliptic] (n : ℕ) :
    Function.Surjective (fun a : (Γ(projectiveScheme Q, ⊤))ˣ => a ^ (l ^ n)) := by
  letI : NeZero ((l ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (l : K))⟩
  exact globalUnitPower_surjective Q (l ^ n)

/-- Arithmetic Frobenius on the actual geometric projective untwisted H¹. -/
def cyclicFrobenius : Module.End ℤ_[l] (CyclicHOne (Y K W) l) :=
  cyclicPullbackLinear (φ k K W) l

private abbrev compare {k : Type} [Field k] (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [Algebra k K] [IsAlgClosed K] [NeZero (l : K)]
    (W : WeierstrassCurve.Affine k) [W.IsElliptic] :=
  cyclicUnitTateEquiv (Y K W) l (toBase (V K W)) (globalPowers l K (V K W))

/-- On the genuine geometric Weierstrass scheme, actual arithmetic unit
Tate pullback is the field cardinality times actual cyclic Frobenius
under the literal Kummer label, with all levels accounted for. -/
theorem cyclicFrobenius_twist (c : CyclicHOne (Y K W) l) :
    map l (unitPullback (φ k K W)) (compare l K W c) =
      Fintype.card k • compare l K W (cyclicFrobenius l k K W c) := by
  let b := toBase (V K W)
  have h : φ k K W ≫ b =
      b ≫ Spec.map (CommRingCat.ofHom (((FiniteField.frobeniusAlgHom k K) ^ 1).toRingHom)) := by
    rw [pow_one]
    exact projectiveFrobenius_base k K W
  have hc := cyclicTate_cyclotomic (φ k K W) l k K b b
    (globalPowers l K (V K W)) (globalPowers l K (V K W)) 1 h c
  simpa only [pow_one] using hc

end

end ManuscriptAudit.WeierstrassCyclicArithmeticAction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassCyclicArithmeticAction.cyclicFrobenius_twist
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
