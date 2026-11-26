import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Fintype.Card
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusExtensionFixed

/-! The native module of points killed by m, including actual Frobenius and its iterates. -/

namespace ManuscriptAudit.TorsionFrobeniusModule

open WeierstrassCurve WeierstrassFrobeniusFixed WeierstrassFrobeniusExtensionFixed

noncomputable section

variable (m : ℕ) (G : Type*) [AddCommGroup G]

def subgroup : AddSubgroup G := (nsmulAddMonoidHom m : G →+ G).ker

abbrev Torsion := ↥(subgroup m G)

theorem mem_iff (P : G) : P ∈ subgroup m G ↔ m • P = 0 := Iff.rfl

instance torsionModule : Module (ZMod m) (Torsion m G) :=
  AddCommGroup.zmodModule fun P => Subtype.ext ((mem_iff m G P).mp P.property)

def carrierEquiv : Torsion m G ≃ {P : G // m • P = 0} where
  toFun P := ⟨P, (mem_iff m G P).mp P.property⟩
  invFun P := ⟨P, (mem_iff m G P).mpr P.property⟩
  left_inv P := Subtype.ext rfl
  right_inv P := Subtype.ext rfl

abbrev inclusion : Torsion m G →+ G := (subgroup m G).subtype

theorem inclusion_injective : Function.Injective (inclusion m G) := Subtype.val_injective

theorem in_image_iff (P : G) : (∃ v : Torsion m G, inclusion m G v = P) ↔ m • P = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (mem_iff m G v).mp v.property
  · intro h
    exact ⟨⟨P, (mem_iff m G P).mpr h⟩, rfl⟩

variable {G} {H : Type*} [AddCommGroup H]

def mapAdd (f : G →+ H) : Torsion m G →+ Torsion m H where
  toFun P := ⟨f P, (mem_iff m H (f P)).mpr (by
    rw [← map_nsmul, (mem_iff m G P).mp P.property, map_zero])⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' P Q := Subtype.ext (map_add f (P : G) (Q : G))

def mapLinear (f : G →+ H) : Torsion m G →ₗ[ZMod m] Torsion m H :=
  (mapAdd m f).toZModLinearMap m

theorem mapLinear_inclusion (f : G →+ H) (P : Torsion m G) :
    inclusion m H (mapLinear m f P) = f (inclusion m G P) := rfl

theorem mapLinear_injective (f : G →+ H) (hf : Function.Injective f) :
    Function.Injective (mapLinear m f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

section AcrossFields

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [DecidableEq L] [DecidableEq M]

def pointMap (W : Affine K) (f : L →ₐ[K] M) :
    Torsion m (W.baseChange L).Point →ₗ[ZMod m] Torsion m (W.baseChange M).Point :=
  mapLinear m (Affine.Point.map (W' := W) f)

theorem pointMap_injective (W : Affine K) (f : L →ₐ[K] M) :
    Function.Injective (pointMap m W f) :=
  mapLinear_injective m _ (Affine.Point.map_injective (W' := W) f)

end AcrossFields

section Frobenius

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L]
variable (W : Affine (ZMod p))

abbrev geometricTorsion := Torsion m (W.baseChange L).Point

def frobeniusLinear : Module.End (ZMod m) (geometricTorsion m p L W) :=
  mapLinear m (frobeniusOnPoints p L W)

theorem frobeniusLinear_injective : Function.Injective (frobeniusLinear m p L W) :=
  mapLinear_injective m _
    (Affine.Point.map_injective (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) L))

def frobeniusLinearEquiv [Finite (geometricTorsion m p L W)] :
    geometricTorsion m p L W ≃ₗ[ZMod m] geometricTorsion m p L W :=
  LinearEquiv.ofBijective (frobeniusLinear m p L W)
    (frobeniusLinear_injective m p L W).bijective_of_finite

theorem frobeniusLinear_inclusion (P : geometricTorsion m p L W) :
    inclusion m _ (frobeniusLinear m p L W P) = frobeniusOnPoints p L W (inclusion m _ P) := rfl

theorem frobeniusLinear_pow_inclusion (n : ℕ) (P : geometricTorsion m p L W) :
    inclusion m _ ((frobeniusLinear m p L W ^ n) P) =
      Affine.Point.map (W' := W) ((FiniteField.frobeniusAlgHom (ZMod p) L) ^ n) (inclusion m _ P) := by
  rw [← point_iterate_eq_map p L W n]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    change inclusion m _ (frobeniusLinear m p L W ((frobeniusLinear m p L W ^ n) P)) = _
    rw [frobeniusLinear_inclusion, ih]

theorem frobeniusLinear_pow_eq_pointMap (n : ℕ) :
    frobeniusLinear m p L W ^ n =
      pointMap m W ((FiniteField.frobeniusAlgHom (ZMod p) L) ^ n) := by
  ext P
  apply inclusion_injective m (W.baseChange L).Point
  exact frobeniusLinear_pow_inclusion m p L W n P

end Frobenius
end
end ManuscriptAudit.TorsionFrobeniusModule

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TorsionFrobeniusModule.carrierEquiv,
      ``ManuscriptAudit.TorsionFrobeniusModule.in_image_iff,
      ``ManuscriptAudit.TorsionFrobeniusModule.pointMap_injective,
      ``ManuscriptAudit.TorsionFrobeniusModule.frobeniusLinear_injective,
      ``ManuscriptAudit.TorsionFrobeniusModule.frobeniusLinear_pow_inclusion,
      ``ManuscriptAudit.TorsionFrobeniusModule.frobeniusLinear_pow_eq_pointMap] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
