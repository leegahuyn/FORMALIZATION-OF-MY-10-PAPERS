import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.MonicPlaneFamily

/-! In characteristic two the affine equation (y^2=x^2(x+1)) becomes
(w^2=x^3) under the involution (w=y+x). The substitution preserves
the coefficient ring and the horizontal coordinate. -/

namespace ManuscriptAudit.NodalCharacteristicTwo

open Polynomial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [CommRing K] [CharP K 2]

open MonicPlaneFamily (equation coordinateRing)

private abbrev B (q : Polynomial K) := coordinateRing K q

private abbrev x (q : Polynomial K) : B K q := AdjoinRoot.of (equation K q) X
private abbrev y (q : Polynomial K) : B K q := AdjoinRoot.root (equation K q)

private theorem two_eq_zero (q : Polynomial K) : (2 : B K q) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (algebraMap K (B K q)) (CharP.ofNat_eq_zero K 2)

private theorem square_y (q : Polynomial K) :
    (y K q) ^ 2 = AdjoinRoot.of (equation K q) q := by
  apply sub_eq_zero.mp
  simpa only [equation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using
    AdjoinRoot.eval₂_root (equation K q)

private theorem shifted_root (q r : Polynomial K) (h : q = r + X ^ 2) :
    (equation K q).eval₂ (AdjoinRoot.of (equation K r)) (y K r + x K r) = 0 := by
  simp only [equation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  apply sub_eq_zero.mpr
  calc
    (y K r + x K r) ^ 2 =
        (y K r) ^ 2 + (2 : B K r) * y K r * x K r + (x K r) ^ 2 := by ring
    _ = AdjoinRoot.of (equation K r) q := by
      rw [two_eq_zero K r, zero_mul, zero_mul, add_zero, square_y K r, h, map_add, map_pow]

private def shift (q r : Polynomial K) (h : q = r + X ^ 2) : B K q →ₐ[K] B K r :=
  AdjoinRoot.liftAlgHom (equation K q) (AdjoinRoot.ofAlgHom K (equation K r))
    (y K r + x K r) (shifted_root K q r h)

private theorem shift_polynomial (q r : Polynomial K) (h : q = r + X ^ 2)
    (a : Polynomial K) :
    shift K q r h (AdjoinRoot.of (equation K q) a) =
      AdjoinRoot.of (equation K r) a :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ a

private theorem shift_x (q r : Polynomial K) (h : q = r + X ^ 2) :
    shift K q r h (x K q) = x K r :=
  shift_polynomial K q r h X

private theorem shift_y (q r : Polynomial K) (h : q = r + X ^ 2) :
    shift K q r h (y K q) = y K r + x K r :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem shift_comp (q r : Polynomial K) (h : q = r + X ^ 2)
    (h' : r = q + X ^ 2) :
    (shift K r q h').comp (shift K q r h) = AlgHom.id K (B K q) := by
  apply AdjoinRoot.algHom_ext'
  · apply AlgHom.ext
    intro a
    change shift K r q h' (shift K q r h (AdjoinRoot.of (equation K q) a)) =
      AdjoinRoot.of (equation K q) a
    rw [shift_polynomial, shift_polynomial]
  · change shift K r q h' (shift K q r h (y K q)) = y K q
    rw [shift_y, map_add, shift_y, shift_x, add_assoc, ← two_mul, two_eq_zero K q,
      zero_mul, add_zero]

private abbrev nodePolynomial : Polynomial K := X ^ 2 * (X + 1)
private abbrev cuspPolynomial : Polynomial K := X ^ 3

private theorem node_eq_cusp_add_x_square :
    nodePolynomial K = cuspPolynomial K + X ^ 2 := by
  dsimp [nodePolynomial, cuspPolynomial]
  ring

private theorem cusp_eq_node_add_x_square :
    cuspPolynomial K = nodePolynomial K + X ^ 2 := by
  rw [node_eq_cusp_add_x_square K, add_assoc, ← two_mul]
  have h : (2 : Polynomial K) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg Polynomial.C (CharP.ofNat_eq_zero K 2)
  rw [h, zero_mul, add_zero]

/-- The actual affine coordinate algebras are isomorphic over the
coefficient ring by translating the vertical coordinate by (x). -/
def affineRingEquiv :
    coordinateRing K (nodePolynomial K) ≃ₐ[K] coordinateRing K (cuspPolynomial K) :=
  AlgEquiv.ofAlgHom
    (shift K _ _ (node_eq_cusp_add_x_square K))
    (shift K _ _ (cusp_eq_node_add_x_square K))
    (shift_comp K _ _ (cusp_eq_node_add_x_square K) (node_eq_cusp_add_x_square K))
    (shift_comp K _ _ (node_eq_cusp_add_x_square K) (cusp_eq_node_add_x_square K))

theorem affineRingEquiv_x :
    affineRingEquiv K (AdjoinRoot.of (equation K (nodePolynomial K)) X) =
      AdjoinRoot.of (equation K (cuspPolynomial K)) X :=
  shift_x K _ _ _

theorem affineRingEquiv_y :
    affineRingEquiv K (AdjoinRoot.root (equation K (nodePolynomial K))) =
      AdjoinRoot.root (equation K (cuspPolynomial K)) +
        AdjoinRoot.of (equation K (cuspPolynomial K)) X :=
  shift_y K _ _ _

end
end ManuscriptAudit.NodalCharacteristicTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCharacteristicTwo.affineRingEquiv,
      ``ManuscriptAudit.NodalCharacteristicTwo.affineRingEquiv_x,
      ``ManuscriptAudit.NodalCharacteristicTwo.affineRingEquiv_y] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
