import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveSemilinearBase
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitRestriction
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassNativeFrobeniusPowers
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! Arithmetic Frobenius is realized by an actual semilinear
automorphism of the geometric Weierstrass scheme and its affine chart. -/

namespace ManuscriptAudit.WeierstrassArithmeticFrobeniusScheme

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Affine
open WeierstrassProjectiveClosure WeierstrassProjectiveSemilinear
open WeierstrassProjectiveSemilinearBase WeierstrassSemilinearAffineChart
open OpenEtaleUnitRestriction KummerUnitsSheaf PowerTateModule

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (k K : Type) [Field k] [Fintype k] [Field K] [Algebra k K] [IsAlgClosed K]

/-- The literal finite-base Frobenius is invertible on the geometric field. -/
def fieldFrobenius : K ≃+* K := by
  let f := FiniteField.frobeniusAlgHom k K
  refine RingEquiv.ofBijective f.toRingHom ⟨f.injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (Fintype.card_pos (α := k))
  exact ⟨x, hx⟩

theorem fieldFrobenius_toRingHom :
    (fieldFrobenius k K).toRingHom = (FiniteField.frobeniusAlgHom k K).toRingHom := rfl

variable (W : WeierstrassCurve.Affine k)

private abbrev V {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := W.baseChange K
private abbrev e := fieldFrobenius k K

private theorem coefficients_fixed : (V K W).map (e k K).toRingHom = V K W := by
  rw [fieldFrobenius_toRingHom]
  exact W.map_baseChange (FiniteField.frobeniusAlgHom k K)

private def affineTransport {U V : WeierstrassCurve.Affine K} (h : U = V) :
    affineScheme V ≅ affineScheme U :=
  (eqToIso (congrArg (fun T => affineScheme T) h)).symm

private def projectiveTransport {U V : WeierstrassCurve.Affine K} (h : U = V) :
    projectiveScheme V ≅ projectiveScheme U :=
  (eqToIso (congrArg (fun T => projectiveScheme T) h)).symm

private theorem transport_open {U V : WeierstrassCurve.Affine K} (h : U = V) :
    affineOpen V ≫ (projectiveTransport K h).hom = (affineTransport K h).hom ≫ affineOpen U := by
  subst V
  simp [projectiveTransport, affineTransport]

private theorem transport_base {U V : WeierstrassCurve.Affine K} (h : U = V) :
    (projectiveTransport K h).hom ≫ toBase U = toBase V := by
  subst V
  simp [projectiveTransport]

/-- The actual semilinear arithmetic Frobenius on the geometric affine scheme. -/
def affineFrobenius : affineScheme (V K W) ≅ affineScheme (V K W) :=
  affineTransport K (coefficients_fixed k K W) ≪≫ affineSchemeIso (V K W) (e k K)

/-- The actual semilinear arithmetic Frobenius on the geometric proper closure. -/
def projectiveFrobenius : projectiveScheme (V K W) ≅ projectiveScheme (V K W) :=
  projectiveTransport K (coefficients_fixed k K W) ≪≫ projectiveIso (V K W) (e k K)

theorem affineOpen_projectiveFrobenius :
    affineOpen (V K W) ≫ (projectiveFrobenius k K W).hom =
      (affineFrobenius k K W).hom ≫ affineOpen (V K W) := by
  change affineOpen (V K W) ≫
      ((projectiveTransport K (coefficients_fixed k K W)).hom ≫ (projectiveIso (V K W) (e k K)).hom) =
    ((affineTransport K (coefficients_fixed k K W)).hom ≫ (affineSchemeIso (V K W) (e k K)).hom) ≫
      affineOpen (V K W)
  rw [← Category.assoc, transport_open, Category.assoc, affineOpen_projectiveIso, ← Category.assoc]

theorem projectiveFrobenius_base :
    (projectiveFrobenius k K W).hom ≫ toBase (V K W) =
      toBase (V K W) ≫ Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k K).toRingHom) := by
  change ((projectiveTransport K (coefficients_fixed k K W)).hom ≫
    (projectiveIso (V K W) (e k K)).hom) ≫ toBase (V K W) = _
  rw [Category.assoc, projectiveIso_base, ← Category.assoc, transport_base, fieldFrobenius_toRingHom]

/-- The actual unit cohomology action by pullback along the actual geometric scheme automorphism. -/
def unitHOneFrobenius :
    Sheaf.H (fullCoordinateUnitSheaf (projectiveScheme (V K W))) 1 ≃+
      Sheaf.H (fullCoordinateUnitSheaf (projectiveScheme (V K W))) 1 :=
  unitCohomologyIso (projectiveFrobenius k K W) 1

variable (l : ℕ) [Fact l.Prime]

/-- The actual pullback on unit cohomology induces the native prime-adic action. -/
def unitTateFrobenius :
    Tate l (Sheaf.H (fullCoordinateUnitSheaf (projectiveScheme (V K W))) 1) ≃ₗ[ℤ_[l]]
      Tate l (Sheaf.H (fullCoordinateUnitSheaf (projectiveScheme (V K W))) 1) :=
  mapAddEquiv l (unitHOneFrobenius k K W)

end

end ManuscriptAudit.WeierstrassArithmeticFrobeniusScheme

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassArithmeticFrobeniusScheme.affineOpen_projectiveFrobenius,
      ``ManuscriptAudit.WeierstrassArithmeticFrobeniusScheme.projectiveFrobenius_base,
      ``ManuscriptAudit.WeierstrassArithmeticFrobeniusScheme.unitTateFrobenius] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
